import Lean.Data.Json

/-!
# `MarchLean.TailCall` — march's Pass 3, tail-call enforcement

Independent model of march's `enforce_tail_calls_in_decls`
(`lib/typecheck/typecheck.ml:10902`, invoked as "Pass 3" at `:11367`) and the
analysis it drives, `check_recursion_safety` (`typecheck.ml:10715-10898`).

march emits an **ERROR** — not a warning — for *truly unbounded non-tail
recursion*: a recursive call that is neither in tail position nor structurally
decreasing. Structurally decreasing non-tail recursion (`fact(n - 1) * n`) gets
a warning and is allowed (`typecheck.ml:10753-10780`). Nothing modelled this,
so every such program was a FALSE ACCEPT.

## Why this pass reads raw `Json`

It is the only pass here that does not consume `MarchLean.Syntax`. That is
deliberate, and narrow: `Elab.decodeDecl`/`decodeTerm` are lossy in exactly the
places Pass 3 is structural.

| Pass 3 needs | the decoded `Module` has |
|---|---|
| `fn.attrs`, for the `no_warn_recursion` exemption (`typecheck.ml:10955`) | dropped |
| `ECond` arm bodies are TAIL position (`typecheck.ml:10805-10809`) | `Term.opaque_` — an unordered bag; tail position erased |
| the `ELetQ` continuation is TAIL (`typecheck.ml:10888-10891`) | `Term.opaque_` — same erasure |
| `ELetFn` opens a scope and shadows its name (`typecheck.ml:10846`) | `Term.opaque_` — binder erased |
| a multi-clause `DFn`'s NAME (a valid SCC target) | `Decl.unsupported` — name erased |

The emitted JSON is march's *surface* AST and carries all of it. Reading it
directly gives a 1:1 transcription of `typecheck.ml` and — decisively —
requires no change to `Syntax.lean` or `Elab.lean`, so no existing verdict can
be perturbed by this file's existence.

## The no-false-reject contract

`MarchLeanCheck.run` calls `check` BEFORE `Compare.inferModule`'s whole-file
skip gate (mirroring march, whose capability checks at `typecheck.ml:11351`
precede Pass 3 at `:11367`). It therefore sees out-of-fragment modules too, and
can turn a reject-side SKIP into a confirmed reject. `TailResult` has no `skip`
case: this pass either rejects or says nothing, and can never license an
accept.

One bail rule holds the contract: **an unrecognised expression `kind`, or an
unrecognised pattern `kind`, anywhere in a function's body abandons that
function entirely** — `Res.bailed`, no report. Bail beats error, because an
unmodelled sibling in a block could have been an `ELet` shadowing the recursive
name, which would retract an error found later in that same block.

Every other divergence from march is under-reporting (it can leave a false
accept standing but cannot manufacture a false reject): a missing edge only
shrinks an SCC, and the envelope omits the injected prelude, which can only
shrink `fnNames`.

## Nested `mod` is NOT checked — verified, not assumed

`enforce_tail_calls_in_decls` has a `DMod` arm (`typecheck.ml:10968-10969`)
that recurses into a nested module's decls. **It does not fire in the
`--check` path**, and this file deliberately does not model it. Verified
directly against the real binary, two ways:

- `mod M do mod Inner do fn boom(n : Int) : Int do if n == 0 do 0 else boom(n + 1) + 1 end end end … end`
  → march exits **0**. The same function at top level (`scripts/tailcall-probes/nested_mod_flat.march`)
  → march exits **1**.
- A nested structural recursion emits no `structurally recursive but not
  tail-recursive` warning, where the identical flat function emits one — so it
  is Pass 3 as a whole that finds nothing inside, not just its error path.

Nested `mod` bodies ARE otherwise typechecked normally (a type error inside one
is reported) — it is specifically Pass 3 that comes up empty.

Recursing here would reject `scripts/tailcall-probes/nested_mod.march`, which
march accepts — a false reject. This is the reason that probe exists.

**Root cause, since traced upstream:** `Desugar.qualify_module_refs`
(`desugar.ml:3046`) rewrites bare intra-module CALL SITES inside every nested
`DMod` to `Prefix.name` (`EVar "boom"` → `EVar "Inner.boom"`) and leaves the
DECLARATION name bare, so Pass 3 searched a post-desugar body for a pre-desugar
name and concluded nothing was recursive. That is a march bug, fixed upstream in
`fix/tailcall-nested-mod-qualified-names`. **When march-lean re-pins to a march
that carries that fix, `nested_mod` flips from `clean` to `tailcall` and this
section must be rewritten to model the prefix.** The probe failing is the
intended signal — it is why march is modelled as it behaves rather than as its
source reads.
-/

namespace MarchLean.TailCall

open Lean (Json)

/-- Result of the pass. Deliberately has **no `skip` case** — see this module's
docstring. `ok` means "nothing to say", never "accept". -/
inductive TailResult where
  | ok
  | violation (msg : String)
  deriving Repr, Inhabited

def TailResult.isViolation : TailResult → Bool
  | .violation _ => true
  | .ok => false

/-! ## Name sets

march uses `StringSet`. The sets here are function names and pattern-bound
variables — tens of elements at most — so a plain `List String` is used, with
march's own set operations spelled out. -/

abbrev NameSet := List String

def nsMem (s : NameSet) (n : String) : Bool := s.contains n
def nsAdd (s : NameSet) (n : String) : NameSet := if s.contains n then s else n :: s
def nsUnion (a b : NameSet) : NameSet := b.foldl nsAdd a
def nsDiff (a b : NameSet) : NameSet := a.filter (fun n => !b.contains n)
def nsRemove (a : NameSet) (n : String) : NameSet := a.filter (fun m => m != n)

/-! ## Total JSON accessors

Every accessor is `Option`-valued and total. A missing or ill-typed field is
`none`, which the callers turn into a bail — never an exception and never a
silently-skipped subterm. -/

def get? (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption

def str? (j : Json) : Option String := j.getStr?.toOption

def kind? (j : Json) : Option String := do str? (← get? j "kind")

def arr? (j : Json) (k : String) : Option (List Json) := do
  pure (← (← get? j k).getArr?.toOption).toList

/-- The `txt` of a `name_to_json` node (`{"txt": …, "span": …}`). -/
def nameTxt? (j : Json) : Option String := do str? (← get? j "txt")

/-- The `txt` of the `name` field of `j`. -/
def fieldName? (j : Json) (k : String) : Option String := do nameTxt? (← get? j k)

/-- `some v` when `e` is exactly `EVar v`. Drives both the recursive-call test
and the diagnostic's operator name. -/
def evarName? (e : Json) : Option String := do
  if (← kind? e) == "EVar" then fieldName? e "name" else none

/-- `is_infix_op` (`typecheck.ml:10679`). Affects the diagnostic text only,
never the verdict. -/
def isInfixOp (name : String) : Bool :=
  ["+", "-", "*", "/", "%", "<", ">", "<=", ">=",
   "==", "!=", "&&", "||", "+.", "-.", "*.", "/."].contains name

/-! ## `collect_pattern_vars` (`typecheck.ml:10507`)

`none` on an unrecognised pattern `kind`. This must NOT degrade to "binds
nothing": failing to retire a shadowed name would leave an edge march does not
have, which is the one direction that manufactures a false reject. -/

partial def patVars (p : Json) : Option NameSet := do
  match ← kind? p with
  | "PatWild" | "PatLit" => pure []
  | "PatVar" => pure [← fieldName? p "name"]
  | "PatCon" | "PatAtom" =>
      let args ← arr? p "args"
      args.foldlM (fun acc a => do pure (nsUnion acc (← patVars a))) []
  | "PatTuple" =>
      let elems ← arr? p "elements"
      elems.foldlM (fun acc a => do pure (nsUnion acc (← patVars a))) []
  | "PatRecord" =>
      let fields ← arr? p "fields"
      fields.foldlM (fun acc f => do pure (nsUnion acc (← patVars (← get? f "pattern")))) []
  | "PatAs" => pure (nsAdd (← patVars (← get? p "pattern")) (← fieldName? p "name"))
  | "PatOr" =>
      let alts ← arr? p "patterns"
      alts.foldlM (fun acc a => do pure (nsUnion acc (← patVars a))) []
  | _ => none

/-! ## `collect_direct_fn_calls` (`typecheck.ml:10539`)

Which names from `names` are called DIRECTLY (not through a lambda or a local
`ELetFn` body) in `e`. `names` is a SCOPE, not a flat list — see the caveat at
`typecheck.ml:10530-10537`: a local binder retires its name, and without that,
prelude's `length` (which uses a local `fn go`) forged an edge into any program
with its own top-level `go`.

`none` propagates: a function whose body cannot be walked contributes no
adjacency entry at all, exactly like a multi-clause `DFn`. -/

partial def calls (names : NameSet) (e : Json) : Option NameSet := do
  let each (ns : NameSet) (js : List Json) : Option NameSet :=
    js.foldlM (fun acc x => do pure (nsUnion acc (← calls ns x))) []
  match ← kind? e with
  | "EApp" =>
      let fn ← get? e "fn"
      let args ← arr? e "args"
      -- A direct call to a name in scope contributes the name itself; the
      -- callee expression is then NOT re-walked (march's first arm).
      match evarName? fn with
      | some f =>
          let self := if nsMem names f then [f] else []
          pure (nsUnion self (← each names args))
      | none => pure (nsUnion (← calls names fn) (← each names args))
  | "ECon" | "EAtom" => each names (← arr? e "args")
  | "EIf" =>
      each names [← get? e "cond", ← get? e "then_", ← get? e "else_"]
  | "ECond" =>
      let arms ← arr? e "arms"
      arms.foldlM (fun acc a => do
        pure (nsUnion acc (← each names [← get? a "cond", ← get? a "body"]))) []
  | "EMatch" =>
      let scrut ← calls names (← get? e "scrutinee")
      let branches ← arr? e "branches"
      branches.foldlM (fun acc b => do
        -- Arm-bound names shadow same-named top-level functions inside the arm.
        let armNames := nsDiff names (← patVars (← get? b "pattern"))
        let g ← match get? b "guard" with
          | some gj => if gj.isNull then pure [] else calls armNames gj
          | none => pure []
        pure (nsUnion acc (nsUnion g (← calls armNames (← get? b "body"))))) scrut
  | "EBlock" =>
      -- The ONE place a binder's scope extends to SIBLING expressions:
      -- `ELetFn`/`ELet` carry no continuation of their own, so the shadowing
      -- is applied here, to the rest of the block (`typecheck.ml:10575-10590`).
      let exprs ← arr? e "exprs"
      let (acc, _) ← exprs.foldlM (fun (acc, ns) ex => do
        let acc' := nsUnion acc (← calls ns ex)
        let ns' ← match ← kind? ex with
          | "ELetFn" => pure (nsRemove ns (← fieldName? ex "name"))
          | "ELet" => pure (nsDiff ns (← patVars (← get? (← get? ex "binding") "pattern")))
          | _ => pure ns
        pure (acc', ns')) (([] : NameSet), names)
      pure acc
  | "ELet" => calls names (← get? (← get? e "binding") "expr")
  | "ELetFn" | "ELam" => pure []   -- new scope
  | "ETuple" => each names (← arr? e "elements")
  | "ERecord" =>
      let fs ← arr? e "fields"
      fs.foldlM (fun acc f => do pure (nsUnion acc (← calls names (← get? f "value")))) []
  | "ERecordUpdate" =>
      let fs ← arr? e "fields"
      let base ← calls names (← get? e "base")
      fs.foldlM (fun acc f => do pure (nsUnion acc (← calls names (← get? f "value")))) base
  | "EField" => calls names (← get? e "target")
  | "EAnnot" => calls names (← get? e "expr")
  | "EPipe" => each names [← get? e "lhs", ← get? e "rhs"]
  | "ESend" => each names [← get? e "cap", ← get? e "msg"]
  | "ESpawn" => calls names (← get? e "actor")
  | "EDbg" =>
      let x ← get? e "expr"
      if x.isNull then pure [] else calls names x
  | "ELetQ" =>
      let v ← calls names (← get? e "value")
      let contNames := nsDiff names (← patVars (← get? e "pattern"))
      pure (nsUnion v (← calls contNames (← get? e "cont")))
  | "EAssert" => calls names (← get? e "expr")
  | "ESigil" => calls names (← get? e "content")
  | "ELit" | "EVar" | "EHole" | "EResultRef" => pure []
  | _ => none

/-! ## `is_structurally_smaller` (`typecheck.ml:10693-10706`)

The subtle judgment, transcribed rather than reconstructed. All four clauses:

1. a pattern-bound sub-component — `EVar v` with `v ∈ smaller`;
2. an arithmetic reduction — `v - k` or `v / k` with `v ∈ params ∪ smaller`
   (march requires EXACTLY two arguments here);
3. a list element accessor over a smaller list (march's own literal name list);
4. a nullary constructor — structurally minimal.

Getting this too NARROW is what would manufacture false rejects, since a call
that march deems structural is merely warned about and allowed. -/

def accessorNames : List String :=
  ["list_nth_safe", "list_nth", "List.nth", "List.hd", "List.head"]

partial def isSmaller (params smaller : NameSet) (e : Json) : Bool :=
  match kind? e with
  | some "EVar" => match fieldName? e "name" with
      | some v => nsMem smaller v
      | none => false
  | some "ECon" => match arr? e "args" with
      | some [] => true
      | _ => false
  | some "EApp" =>
      match get? e "fn", arr? e "args" with
      | some fn, some args =>
          match evarName? fn with
          | some op =>
              if (op == "-" || op == "/") && args.length == 2 then
                match args.head? with
                | some lhs => match evarName? lhs with
                    | some v => nsMem params v || nsMem smaller v
                    | none => false
                | none => false
              else if accessorNames.contains op then
                match args.head? with
                | some a => isSmaller params smaller a
                | none => false
              else false
          | none => false
      | _, _ => false
  | _ => false

/-- `scrutinee_is_param_or_smaller` (`typecheck.ml:10710`). -/
def scrutIsParamOrSmaller (params smaller : NameSet) (e : Json) : Bool :=
  match evarName? e with
  | some v => nsMem params v || nsMem smaller v
  | none => false

/-! ## `check_tail_position` (`typecheck.ml:10726`) -/

/-- Outcome of walking a subterm. `bailed` beats `err` when the two are
combined — see the bail rule in this module's docstring. -/
structure Res where
  bailed : Bool := false
  err : Option String := none
  deriving Repr, Inhabited

def Res.ok : Res := {}
def Res.bail : Res := { bailed := true }
def Res.error (m : String) : Res := { err := some m }

/-- march reports every offending call; the first suffices to justify exit 1,
so the earlier `err` wins. -/
def Res.merge (a b : Res) : Res :=
  { bailed := a.bailed || b.bailed,
    err := match a.err with | some e => some e | none => b.err }

def Res.mergeAll (rs : List Res) : Res := rs.foldl Res.merge Res.ok

partial def chk (fnName : String) (fnParams : NameSet)
    (inTail : Bool) (names smaller : NameSet) (ctx : String) (e : Json) : Res :=
  let sub (t : Bool) (ns sm : NameSet) (c : String) (x : Option Json) : Res :=
    match x with
    | some j => chk fnName fnParams t ns sm c j
    | none => Res.bail
  let subs (t : Bool) (ns sm : NameSet) (c : String) (xs : Option (List Json)) : Res :=
    match xs with
    | some js => Res.mergeAll (js.map (fun j => chk fnName fnParams t ns sm c j))
    | none => Res.bail
  match kind? e with
  | some "EApp" =>
      match get? e "fn", arr? e "args" with
      | some fn, some args =>
          let recCallee : Option String := match evarName? fn with
            | some f => if nsMem names f then some f else none
            | none => none
          match recCallee with
          | some callee =>
              -- ── Recursive call ──
              let here : Res :=
                if inTail then Res.ok
                else if args.any (isSmaller fnParams smaller) then
                  -- Structural recursion: march WARNS and allows
                  -- (`typecheck.ml:10752-10778`). Not a reject.
                  Res.ok
                else
                  Res.error s!"Function `{fnName}`: recursive call to `{callee}` is not in tail position ({ctx})."
              -- march walks the arguments (never the callee) with in_tail = false.
              let argRes := args.foldl (fun (acc : Res × Nat) a =>
                  (acc.1.merge (chk fnName fnParams false names smaller
                     s!"argument #{acc.2 + 1} in call to `{callee}`" a), acc.2 + 1))
                (Res.ok, 0)
              here.merge argRes.1
          | none =>
              -- ── Regular application ──
              let argCtx := match evarName? fn with
                | some op =>
                    if isInfixOp op then s!"wrapped in binary operation `{op}`"
                    else s!"passed as argument to `{op}`"
                | none => "passed as argument to a function"
              (chk fnName fnParams false names smaller "function part of application" fn).merge
                (Res.mergeAll (args.map (fun a =>
                   chk fnName fnParams false names smaller argCtx a)))
      | _, _ => Res.bail
  | some "ECon" =>
      match fieldName? e "name" with
      | some n => subs false names smaller s!"wrapped in constructor `{n}`" (arr? e "args")
      | none => Res.bail
  | some "EIf" =>
      Res.mergeAll [
        sub false names smaller "condition of `if`" (get? e "cond"),
        sub inTail names smaller ctx (get? e "then_"),
        sub inTail names smaller ctx (get? e "else_")]
  | some "ECond" =>
      -- A `match do` arm BODY is in tail position (`typecheck.ml:10805-10809`).
      match arr? e "arms" with
      | some arms => Res.mergeAll (arms.map (fun a => Res.mergeAll [
          sub false names smaller "condition in `match do`" (get? a "cond"),
          sub inTail names smaller ctx (get? a "body")]))
      | none => Res.bail
  | some "EMatch" =>
      match get? e "scrutinee", arr? e "branches" with
      | some scrut, some branches =>
          let scrutRes := chk fnName fnParams false names smaller "scrutinee of `match`" scrut
          let scrutSmaller := scrutIsParamOrSmaller fnParams smaller scrut
          Res.merge scrutRes (Res.mergeAll (branches.map (fun b =>
            match patVars (get? b "pattern" |>.getD Json.null) with
            | none => Res.bail
            | some pv =>
                let armSmaller := if scrutSmaller then nsUnion smaller pv else smaller
                let armNames := nsDiff names pv
                let guardRes := match get? b "guard" with
                  | some gj => if gj.isNull then Res.ok
                               else chk fnName fnParams false armNames armSmaller "match guard" gj
                  | none => Res.ok
                guardRes.merge (sub inTail armNames armSmaller ctx (get? b "body")))))
      | _, _ => Res.bail
  | some "EBlock" =>
      -- Only the LAST expression is in tail position. A `let` binding a
      -- structurally-smaller RHS propagates smallness to its name, and any
      -- local binder shadows a same-named recursive function for the rest of
      -- the block (`typecheck.ml:10825-10852`).
      match arr? e "exprs" with
      | some exprs =>
          let rec go (ns sm : NameSet) : List Json → Res
            | [] => Res.ok
            | [last] => chk fnName fnParams inTail ns sm ctx last
            | hd :: tl =>
                let hdRes := chk fnName fnParams false ns sm "non-final expression in block" hd
                match kind? hd with
                | some "ELet" =>
                    match get? hd "binding" with
                    | none => Res.bail
                    | some b =>
                        match get? b "pattern", get? b "expr" with
                        | some pat, some rhs =>
                            let sm' :=
                              if kind? pat == some "PatVar" && isSmaller fnParams sm rhs then
                                match fieldName? pat "name" with
                                | some v => nsAdd sm v
                                | none => sm
                              else sm
                            match patVars pat with
                            | none => Res.bail
                            | some pv => hdRes.merge (go (nsDiff ns pv) sm' tl)
                        | _, _ => Res.bail
                | some "ELetFn" =>
                    match fieldName? hd "name" with
                    | some n => hdRes.merge (go (nsRemove ns n) sm tl)
                    | none => Res.bail
                | some _ => hdRes.merge (go ns sm tl)
                | none => Res.bail
          go names smaller exprs
      | none => Res.bail
  | some "ELet" =>
      -- A TRAILING `let` — march walks the RHS only, in non-tail position.
      match get? e "binding" with
      | some b => sub false names smaller "right-hand side of `let` binding" (get? b "expr")
      | none => Res.bail
  | some "ELetFn" =>
      -- An inner named function is checked in its OWN scope, against its own
      -- name and parameters (`typecheck.ml:10857-10862`).
      match fieldName? e "name", arr? e "params", get? e "body" with
      | some n, some ps, some body =>
          match ps.foldlM (fun acc p => do pure (nsAdd acc (← fieldName? p "name"))) ([] : NameSet) with
          | some ips => chk n ips true [n] [] "" body
          | none => Res.bail
      | _, _, _ => Res.bail
  | some "ELam" => Res.ok   -- new scope; march does not descend
  | some "EAnnot" => sub inTail names smaller ctx (get? e "expr")
  | some "ETuple" => subs false names smaller "tuple element" (arr? e "elements")
  | some "ERecord" =>
      match arr? e "fields" with
      | some fs => Res.mergeAll (fs.map (fun f =>
          match fieldName? f "name" with
          | some n => sub false names smaller s!"value of record field `{n}`" (get? f "value")
          | none => Res.bail))
      | none => Res.bail
  | some "ERecordUpdate" =>
      match arr? e "fields" with
      | some fs => Res.merge
          (sub false names smaller "base of record update" (get? e "base"))
          (Res.mergeAll (fs.map (fun f =>
            match fieldName? f "name" with
            | some n => sub false names smaller s!"value of record field `{n}`" (get? f "value")
            | none => Res.bail)))
      | none => Res.bail
  | some "EField" => sub false names smaller "object of field access" (get? e "target")
  | some "EPipe" => Res.mergeAll [
      sub false names smaller "left side of pipe" (get? e "lhs"),
      sub false names smaller "right side of pipe" (get? e "rhs")]
  | some "EAtom" => subs false names smaller "atom argument" (arr? e "args")
  | some "ESend" => Res.mergeAll [
      sub false names smaller "capability in `send`" (get? e "cap"),
      sub false names smaller "message in `send`" (get? e "msg")]
  | some "ESpawn" => sub false names smaller "argument to `spawn`" (get? e "actor")
  | some "EDbg" =>
      match get? e "expr" with
      | some x => if x.isNull then Res.ok
                  else chk fnName fnParams false names smaller "argument to `dbg`" x
      | none => Res.bail
  | some "ELetQ" =>
      -- The continuation IS in tail position (`typecheck.ml:10888-10891`).
      match get? e "pattern" with
      | none => Res.bail
      | some pat => match patVars pat with
        | none => Res.bail
        | some pv => Res.mergeAll [
            sub false names smaller "right-hand side of `let?`" (get? e "value"),
            sub inTail (nsDiff names pv) smaller ctx (get? e "cont")]
  | some "EAssert" => sub false names smaller "assert expression" (get? e "expr")
  | some "ESigil" => sub false names smaller "sigil content" (get? e "content")
  | some "ELit" | some "EVar" | some "EHole" | some "EResultRef" => Res.ok
  | _ => Res.bail

/-! ## Call graph and recursion detection

march runs Tarjan (`find_sccs`, `typecheck.ml:10631`) and then asks two
questions of the result: is this function on a cycle, and what is its SCC.
Both are answered here by mutual reachability, which is the definition of an
SCC — a smaller surface than a hand-ported Tarjan, over graphs of a few dozen
nodes. -/

/-- `List.assoc_opt` semantics: the FIRST entry for `v` wins. -/
def neighbors (adj : List (String × NameSet)) (v : String) : NameSet :=
  match adj.find? (fun p => p.1 == v) with
  | some p => p.2
  | none => []

/-- Names reachable from `start` in **one or more** steps. `start ∈ result` iff
`start` lies on a cycle, which is exactly march's
`List.length scc > 1 || name ∈ direct` (`typecheck.ml:10951-10954`). -/
def reachFrom (adj : List (String × NameSet)) (start : String) : NameSet :=
  let rec go : Nat → NameSet → NameSet → NameSet
    | 0, _, seen => seen
    | _, [], seen => seen
    | Nat.succ fuel, v :: rest, seen =>
        let fresh := (neighbors adj v).filter (fun w => !seen.contains w)
        go fuel (rest ++ fresh) (nsUnion seen fresh)
  go (adj.length * adj.length + 1) [start] []

/-- The SCC of `f`: `f` itself plus every name mutually reachable with it.
Matches march's `scc_of` lookup, whose default for an absent name is `[name]`. -/
def sccOf (adj : List (String × NameSet)) (f : String) : NameSet :=
  nsAdd ((reachFrom adj f).filter (fun m => m != f && (reachFrom adj m).contains f)) f

/-! ## `enforce_tail_calls_in_decls` (`typecheck.ml:10902`) -/

/-- The single clause of a `DFn`, or `none` when the declaration has zero or
several — march's `filter_map` gives a multi-clause `DFn` no adjacency entry
and its check loop skips it outright (`typecheck.ml:10929-10933`, `:10967`). -/
def soleClause (d : Json) : Option Json := do
  match ← arr? (← get? d "fn") "clauses" with
  | [c] => pure c
  | _ => none

/-- Parameter names of a clause: `FPNamed`/`FPDefault` contribute their param's
name, `FPPat` every variable its pattern binds (`typecheck.ml:10957-10963`). -/
def clauseParams (clause : Json) : Option NameSet := do
  let ps ← arr? clause "params"
  ps.foldlM (fun acc p => do
    match ← kind? p with
    | "FPNamed" | "FPDefault" => pure (nsAdd acc (← fieldName? (← get? p "param") "name"))
    | "FPPat" => pure (nsUnion acc (← patVars (← get? p "pattern")))
    | _ => none) []

def declKind (d : Json) : Option String := kind? d

/-- Check one decl level. Does NOT recurse into `DMod` — see this module's
docstring for the empirical reason. -/
def checkDecls (decls : List Json) : Option String := Id.run do
  -- An extern has no body and cannot recurse; march subtracts these so a bare
  -- call to one is not resolved against a same-named ordinary function
  -- (`typecheck.ml:10903-10915`).
  let externNames : NameSet := decls.foldl (fun acc d =>
    if declKind d == some "DExtern" then
      match (do arr? (← get? d "extern") "fns") with
      | some fns => fns.foldl (fun a f => match fieldName? f "name" with
          | some n => nsAdd a n
          | none => a) acc
      | none => acc
    else acc) []

  let fnDecls := decls.filter (fun d => declKind d == some "DFn")
  let fnNames : NameSet := nsDiff (fnDecls.foldl (fun acc d =>
    match fieldName? (get? d "fn" |>.getD Json.null) "name" with
    | some n => nsAdd acc n
    | none => acc) []) externNames

  let adj : List (String × NameSet) := fnDecls.filterMap (fun d => do
    let name ← fieldName? (← get? d "fn") "name"
    let clause ← soleClause d
    let cs ← calls fnNames (← get? clause "body")
    pure (name, cs))

  for d in fnDecls do
    match (do
      let fn ← get? d "fn"
      let name ← fieldName? fn "name"
      let clause ← soleClause d
      let body ← get? clause "body"
      let params ← clauseParams clause
      let attrs := (arr? fn "attrs").getD []
      pure (name, body, params, attrs) : Option _) with
    | none => pure ()
    | some (name, body, params, attrs) =>
        let optedOut := attrs.any (fun a => str? a == some "no_warn_recursion")
        let scc := sccOf adj name
        let isRecursive := scc.length > 1 || nsMem (neighbors adj name) name
        if isRecursive && !optedOut then
          let r := chk name params true scc [] "" body
          -- Bail beats error: an unmodelled node anywhere in this body could
          -- have retracted the finding, so report nothing for this function.
          if !r.bailed then
            if let some msg := r.err then
              return some msg
  return none

/-- Entry point. Reads `envelope.module.decls`. A malformed or absent module is
`ok`, never an error: this pass must never be the reason a file changes verdict
for a non-tail-call reason. -/
def check (envelope : Json) : TailResult :=
  match (do checkDecls (← arr? (← get? envelope "module") "decls") : Option String) with
  | some msg => .violation msg
  | none => .ok

/-! ## Regression guards

Real `march --emit-core-ast` output (spans normalised to a placeholder), so a
guard fails if either the analysis or the emitter's shape drifts. Enforced with
`native_decide`, not just `#eval`: a regression breaks the BUILD.

Kept in-repo and binary-independent — `scripts/tailcall-probes.sh` is the
primary instrument, but it needs a march binary, so these three pin the core
judgments here where CI always runs them. -/

namespace Test

/-- `fn loopy(n) = if n == 0 do 0 else loopy(n + 1) + 1 end` — march ERRORs:
the recursive call is neither in tail position nor structurally decreasing.
This is the false-accept class the pass exists to close. -/
def loopyEnvelope : String :=
  r#"{"diagnostics":[],"format_version":3,"instantiations":[],"module":{"decls":[{"fn":{"attrs":[],"bounds":[],"clauses":[{"body":{"cond":{"args":[{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"n"},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"}},{"kind":"ELit","literal":{"kind":"LitInt","value":0},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"=="},"resolved_ty":{"args":[],"kind":"TCon","name":"Bool"}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Bool"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},"else_":{"args":[{"args":[{"args":[{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"n"},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"}},{"kind":"ELit","literal":{"kind":"LitInt","value":1},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"+"},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"loopy"},"resolved_ty":{"from":{"args":[],"kind":"TCon","name":"Int"},"kind":"TArrow","to":{"args":[],"kind":"TCon","name":"Int"}}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},{"kind":"ELit","literal":{"kind":"LitInt","value":1},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"+"},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},"kind":"EIf","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"then_":{"kind":"ELit","literal":{"kind":"LitInt","value":0},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}},"guard":null,"params":[{"kind":"FPNamed","param":{"lin":{"kind":"Unrestricted"},"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"n"},"ty":{"args":[],"kind":"TyCon","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"Int"}}}}],"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"doc":null,"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"loopy"},"ret_ty":{"args":[],"kind":"TyCon","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"Int"}},"vis":{"kind":"Public"}},"kind":"DFn","span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},{"fn":{"attrs":[],"bounds":[],"clauses":[{"body":{"args":[{"args":[{"args":[{"kind":"ELit","literal":{"kind":"LitInt","value":0},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"loopy"},"resolved_ty":{"from":{"args":[],"kind":"TCon","name":"Int"},"kind":"TArrow","to":{"args":[],"kind":"TCon","name":"Int"}}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"int_to_string"},"resolved_ty":{"from":{"args":[],"kind":"TCon","name":"Int"},"kind":"TArrow","to":{"args":[],"kind":"TCon","name":"String"}}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"String"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"println"},"resolved_ty":{"from":{"args":[],"kind":"TCon","name":"String"},"kind":"TArrow","to":{"elems":[],"kind":"TTuple"}}},"kind":"EApp","resolved_ty":{"elems":[],"kind":"TTuple"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},"guard":null,"params":[],"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"doc":null,"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"main"},"ret_ty":null,"vis":{"kind":"Public"}},"kind":"DFn","span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"M"}},"module_caps":[],"schemes":[],"verdict":"reject"}"#

/-- `fn fact(n) = if n <= 1 do 1 else fact(n - 1) * n end` — march WARNS and
allows: `n - 1` is an arithmetic reduction of a parameter, so the call is
structurally decreasing. Guards against the blanket "any non-tail recursive
call is an error" rule, which would be a false reject. -/
def factEnvelope : String :=
  r#"{"diagnostics":[],"format_version":3,"instantiations":[],"module":{"decls":[{"fn":{"attrs":[],"bounds":[],"clauses":[{"body":{"cond":{"args":[{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"n"},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"}},{"kind":"ELit","literal":{"kind":"LitInt","value":1},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"<="},"resolved_ty":{"args":[],"kind":"TCon","name":"Bool"}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Bool"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},"else_":{"args":[{"args":[{"args":[{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"n"},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"}},{"kind":"ELit","literal":{"kind":"LitInt","value":1},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"-"},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"fact"},"resolved_ty":{"from":{"args":[],"kind":"TCon","name":"Int"},"kind":"TArrow","to":{"args":[],"kind":"TCon","name":"Int"}}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"n"},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"*"},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},"kind":"EIf","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"then_":{"kind":"ELit","literal":{"kind":"LitInt","value":1},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}},"guard":null,"params":[{"kind":"FPNamed","param":{"lin":{"kind":"Unrestricted"},"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"n"},"ty":{"args":[],"kind":"TyCon","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"Int"}}}}],"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"doc":null,"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"fact"},"ret_ty":{"args":[],"kind":"TyCon","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"Int"}},"vis":{"kind":"Public"}},"kind":"DFn","span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},{"fn":{"attrs":[],"bounds":[],"clauses":[{"body":{"args":[{"args":[{"args":[{"kind":"ELit","literal":{"kind":"LitInt","value":5},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"fact"},"resolved_ty":{"from":{"args":[],"kind":"TCon","name":"Int"},"kind":"TArrow","to":{"args":[],"kind":"TCon","name":"Int"}}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"int_to_string"},"resolved_ty":{"from":{"args":[],"kind":"TCon","name":"Int"},"kind":"TArrow","to":{"args":[],"kind":"TCon","name":"String"}}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"String"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"println"},"resolved_ty":{"from":{"args":[],"kind":"TCon","name":"String"},"kind":"TArrow","to":{"elems":[],"kind":"TTuple"}}},"kind":"EApp","resolved_ty":{"elems":[],"kind":"TTuple"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},"guard":null,"params":[],"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"doc":null,"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"main"},"ret_ty":null,"vis":{"kind":"Public"}},"kind":"DFn","span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"M"}},"module_caps":[],"schemes":[],"verdict":"accept"}"#

/-- The `loopy` program with `@[no_warn_recursion]` on it — march accepts.
Guards the `fn.attrs` read, which `Elab` drops entirely; without it this file
would reject a program march's own escape hatch exempts. -/
def attrEnvelope : String :=
  r#"{"diagnostics":[],"format_version":3,"instantiations":[],"module":{"decls":[{"fn":{"attrs":["no_warn_recursion"],"bounds":[],"clauses":[{"body":{"cond":{"args":[{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"n"},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"}},{"kind":"ELit","literal":{"kind":"LitInt","value":0},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"=="},"resolved_ty":{"args":[],"kind":"TCon","name":"Bool"}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Bool"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},"else_":{"args":[{"args":[{"args":[{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"n"},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"}},{"kind":"ELit","literal":{"kind":"LitInt","value":1},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"+"},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"loopy"},"resolved_ty":{"from":{"args":[],"kind":"TCon","name":"Int"},"kind":"TArrow","to":{"args":[],"kind":"TCon","name":"Int"}}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},{"kind":"ELit","literal":{"kind":"LitInt","value":1},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"+"},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},"kind":"EIf","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"then_":{"kind":"ELit","literal":{"kind":"LitInt","value":0},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}},"guard":null,"params":[{"kind":"FPNamed","param":{"lin":{"kind":"Unrestricted"},"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"n"},"ty":{"args":[],"kind":"TyCon","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"Int"}}}}],"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"doc":null,"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"loopy"},"ret_ty":{"args":[],"kind":"TyCon","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"Int"}},"vis":{"kind":"Public"}},"kind":"DFn","span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},{"fn":{"attrs":[],"bounds":[],"clauses":[{"body":{"args":[{"args":[{"args":[{"kind":"ELit","literal":{"kind":"LitInt","value":0},"resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"loopy"},"resolved_ty":{"from":{"args":[],"kind":"TCon","name":"Int"},"kind":"TArrow","to":{"args":[],"kind":"TCon","name":"Int"}}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"Int"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"int_to_string"},"resolved_ty":{"from":{"args":[],"kind":"TCon","name":"Int"},"kind":"TArrow","to":{"args":[],"kind":"TCon","name":"String"}}},"kind":"EApp","resolved_ty":{"args":[],"kind":"TCon","name":"String"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"fn":{"kind":"EVar","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"println"},"resolved_ty":{"from":{"args":[],"kind":"TCon","name":"String"},"kind":"TArrow","to":{"elems":[],"kind":"TTuple"}}},"kind":"EApp","resolved_ty":{"elems":[],"kind":"TTuple"},"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},"guard":null,"params":[],"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"doc":null,"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"main"},"ret_ty":null,"vis":{"kind":"Public"}},"kind":"DFn","span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"M"}},"module_caps":[],"schemes":[],"verdict":"accept"}"#

private def verdictOf (s : String) : TailResult :=
  match Lean.Json.parse s with
  | .ok j => check j
  | .error _ => .ok

#eval show IO Unit from do
  IO.println s!"loopy={repr (verdictOf loopyEnvelope)}"
  IO.println s!"fact={repr (verdictOf factEnvelope)}"
  IO.println s!"attr={repr (verdictOf attrEnvelope)}"

example : (verdictOf loopyEnvelope).isViolation = true := by native_decide
example : (verdictOf factEnvelope).isViolation  = false := by native_decide
example : (verdictOf attrEnvelope).isViolation  = false := by native_decide

end Test

end MarchLean.TailCall
