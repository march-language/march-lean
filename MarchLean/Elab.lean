import Lean.Data.Json
import MarchLean.Syntax

/-!
# `MarchLean.Elab`

Decodes march's real `--emit-core-ast` **format_version 3** JSON envelope
into the `MarchLean.Syntax` types (Task 2). The envelope shape (verified
against `march`'s encoder, `lib/dump/ast_json.ml`, and the 8 real samples in
`.superpowers/sdd/samples/*.json` — NOT the task brief's placeholder
snippets, which guessed at some key paths before the real emitter existed):

```
{ "format_version": 3, "verdict": "accept"|"reject", "diagnostics": [...],
  "module": { "name": <name>, "decls": [<decl>...] },
  "schemes": [ {"ids":[Int...], "constraints":[<constraint>...], "body":<ty>} ... ],
  "instantiations": [ {"use_span":<span>, "ids":[Int...], "args":[<ty>...]} ... ] }
```

Every `kind`-tagged node is decoded by dispatching on its `"kind"` string.
**Decoding discipline**: an unrecognized/out-of-fragment `kind` decodes to
the corresponding `.unsupported` constructor — never an `Except.error`. Only
genuinely malformed JSON (a required key missing on a node whose kind we DO
recognize, or a JSON value of the wrong type) is an `Except.error` (which
propagates to the CLI as exit code 3). This lets the checker honestly skip
out-of-fragment programs instead of crashing on them.

Two distinct "ty" tag namespaces appear in the wild, and must not be
conflated:
- **Resolved type** (`T.ty`, from the typechecker's `resolved_ty` field on
  every expr node): tags `TCon`/`TArrow`/`TTuple`/`TRecord`/`TVar`/`TLin`/
  `TNat`/`TNatOp`/`TError`/`unsupported`. Decoded by `decodeTy`.
- **Surface type** (`ty`, the parsed-not-yet-elaborated annotation, e.g. on
  a `DType`'s constructor argument, which the emitter never resolves):
  tags `TyCon`/`TyVar`/`TyArrow`/`TyTuple`/`TyRecord`/`TyLinear`/`TyNat`/
  `TyNatOp`/`TyChan`/`TyRefine`. Decoded by `decodeSurfaceTy`.
-/

namespace MarchLean.Elab

open Lean (Json)
open MarchLean.Syntax

/-- Required object field. -/
def field (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{k}'"

def str (j : Json) : Except String String :=
  j.getStr?.mapError (fun _ => "expected string")

def kindOf (j : Json) : Except String String := do str (← field j "kind")

/-- Decode a resolved (`T.ty`) type node: `TCon`/`TArrow`/`TTuple`/`TRecord`/
`TVar`/`TLin`/`TNat`/`TNatOp`/`TError`. Anything else (including the
emitter's own `{"kind":"unsupported","what":"session"}` for `TChan`) decodes
to `Ty.unsupported` — recognized-but-out-of-fragment and totally-unknown
kinds are handled identically here, since both must skip, not error. -/
partial def decodeTy (j : Json) : Except String Ty := do
  match ← kindOf j with
  | "TCon" =>
      let name ← str (← field j "name")
      let args ← (← (← field j "args").getArr?.mapError (fun _ => "args not array")).toList.mapM decodeTy
      .ok (Ty.con name args)
  | "TArrow" => .ok (Ty.arrow (← decodeTy (← field j "from")) (← decodeTy (← field j "to")))
  | "TTuple" =>
      let elems ← (← (← field j "elems").getArr?.mapError (fun _ => "elems")).toList.mapM decodeTy
      .ok (Ty.tuple elems)
  | "TRecord" =>
      let fs ← (← (← field j "fields").getArr?.mapError (fun _ => "fields")).toList.mapM (fun f => do
        let n ← str (← field f "name")
        let t ← decodeTy (← field f "ty")
        pure (n, t))
      .ok (Ty.record fs)
  | "TVar" =>
      let id ← (← field j "id").getInt?.mapError (fun _ => "id")
      .ok (Ty.var id)
  | "TLin" =>
      let l ← str (← field j "lin")
      let lin := if l == "linear" then Lin.linear else if l == "affine" then Lin.affine else Lin.unrestricted
      .ok (Ty.lin lin (← decodeTy (← field j "ty")))
  | "TNat" => .ok (Ty.nat (← (← field j "n").getNat?.mapError (fun _ => "n")))
  | "TNatOp" =>
      .ok (Ty.natOp (← str (← field j "op")) (← decodeTy (← field j "a")) (← decodeTy (← field j "b")))
  | "TError" => .ok Ty.err
  | _ => .ok Ty.unsupported

/-- Decode the `resolved_ty` field on an expr node. Missing key or JSON
`null` both decode to `Ty.unsupported` — a node whose annotation is absent
must force a downstream skip, never a false accept (design §6). -/
def decodeResolvedTy (j : Json) : Except String Ty :=
  match j.getObjVal? "resolved_ty" with
  | .ok v => if v.isNull then .ok Ty.unsupported else decodeTy v
  | .error _ => .ok Ty.unsupported

def decodeSpan (j : Json) : Except String Span := do
  .ok { file := (← str (← field j "file")),
        startLine := (← (← field j "start_line").getNat?.mapError (fun _ => "sl")),
        startCol := (← (← field j "start_col").getNat?.mapError (fun _ => "sc")),
        endLine := (← (← field j "end_line").getNat?.mapError (fun _ => "el")),
        endCol := (← (← field j "end_col").getNat?.mapError (fun _ => "ec")) }

/-- Decode a `name` node (`{"txt":.., "span":{...}}`), returning both parts:
callers usually only need `txt`, but `EVar`/`EField` need the `span` too
(the instantiation-join key). -/
def decodeName (j : Json) : Except String (String × Span) := do
  let txt ← str (← field j "txt")
  let sp ← decodeSpan (← field j "span")
  pure (txt, sp)

/-- Decode a *surface* linearity tag: `{"kind":"Linear"|"Affine"|"Unrestricted"}`.
Used for `param.lin` / `binding.lin` (distinct from resolved `TLin`'s
lowercase-string `"lin"` field, handled inline inside `decodeTy`). -/
def decodeLin (j : Json) : Except String Lin := do
  match ← kindOf j with
  | "Linear" => .ok Lin.linear
  | "Affine" => .ok Lin.affine
  | _ => .ok Lin.unrestricted

/-- Decode a literal (`{"kind":"LitInt"/.., "value":..}`). Returns `none` for
an unrecognized literal kind (`LitAtom`, out of the A1 fragment) — `Lit` has
no `unsupported` constructor of its own, so the caller (`decodeTerm`'s
`ELit` arm) falls back to `Term.unsupported` on `none` rather than treating
it as a decode error. -/
def decodeLit (j : Json) : Except String (Option Lit) := do
  match ← kindOf j with
  | "LitInt" => .ok (some (Lit.int (← (← field j "value").getInt?.mapError (fun _ => "value"))))
  | "LitString" => .ok (some (Lit.str (← str (← field j "value"))))
  | "LitBool" => .ok (some (Lit.bool (← (← field j "value").getBool?.mapError (fun _ => "value"))))
  | "LitFloat" =>
      let v ← field j "value"
      let s := match v.getStr? with
        | .ok s => s
        | .error _ => v.compress
      .ok (some (Lit.float s))
  | _ => .ok none

/-- Decode a `pattern` node. `PatWild`/`PatVar`/`PatCon`/`PatTuple`/`PatLit`/
`PatRecord`/`PatAs`/`PatOr` map onto the `Pattern` constructors of the same
shape; `PatAtom` (actor-protocol atom patterns, out of the A1 fragment) →
`.unsupported`. -/
partial def decodePattern (j : Json) : Except String Pattern := do
  match ← kindOf j with
  | "PatWild" => .ok Pattern.wild
  | "PatVar" =>
      -- `PatVar` carries no `lin` of its own in the JSON — linearity for a
      -- bound name lives on the enclosing `binding`/`param`, not on a bare
      -- pattern — so a standalone decode (e.g. inside a match arm) defaults
      -- to `unrestricted`.
      let (txt, _) ← decodeName (← field j "name")
      .ok (Pattern.var txt Lin.unrestricted)
  | "PatCon" =>
      let (txt, _) ← decodeName (← field j "name")
      let args ← (← (← field j "args").getArr?.mapError (fun _ => "args")).toList.mapM decodePattern
      .ok (Pattern.con txt args)
  | "PatTuple" =>
      let elems ← (← (← field j "elements").getArr?.mapError (fun _ => "elements")).toList.mapM decodePattern
      .ok (Pattern.tuple elems)
  | "PatLit" =>
      match ← decodeLit (← field j "literal") with
      | some l => .ok (Pattern.lit l)
      | none => .ok Pattern.unsupported
  | "PatRecord" =>
      let fs ← (← (← field j "fields").getArr?.mapError (fun _ => "fields")).toList.mapM (fun f => do
        let (n, _) ← decodeName (← field f "name")
        let p ← decodePattern (← field f "pattern")
        pure (n, p))
      .ok (Pattern.record fs)
  | "PatAs" =>
      let p ← decodePattern (← field j "pattern")
      let (n, _) ← decodeName (← field j "name")
      .ok (Pattern.as n p)
  | "PatOr" =>
      let alts ← (← (← field j "patterns").getArr?.mapError (fun _ => "patterns")).toList.mapM decodePattern
      .ok (Pattern.or_ alts)
  | _ => .ok Pattern.unsupported

/-- Decode a *surface* `ty` node (`TyCon`/`TyArrow`/..; a different tag
namespace from the resolved `T.ty` decoded by `decodeTy` — see module doc).
Used only for `DType` constructor argument types, since the emitter never
attaches a `resolved_ty` to a declaration (only to expressions). `paramNames`
is the enclosing `DType`'s type-parameter name list, used to resolve a
`TyVar` reference to its positional `Ty.var` id; if the name isn't found
there we can't faithfully assign an id, so it decodes to `Ty.unsupported`. -/
partial def decodeSurfaceTy (paramNames : List String) (j : Json) : Except String Ty := do
  match ← kindOf j with
  | "TyCon" =>
      let (name, _) ← decodeName (← field j "name")
      let args ← (← (← field j "args").getArr?.mapError (fun _ => "args")).toList.mapM (decodeSurfaceTy paramNames)
      -- `Cap(perm)` is march's capability type — a `TyCon` named `Cap` APPLIED
      -- to a permission argument (`Cap(IO.Network)`). Under the A3 capability
      -- lattice design (design §5) this is now first-class and modeled: decode
      -- it to `Ty.con "Cap" args`, preserving the permission argument, so
      -- `CapCheck.capsInTy`'s `Ty.con "Cap" [Ty.con x _]` shape can match it and
      -- the capability checker (Check 1) can actually fire against real march
      -- output. The APPLIED test (`args ≠ []`) is still load-bearing: a
      -- *nullary* `Cap` is an ordinary user ADT (`type Cap = C(Int)` in
      -- accept/t80), NOT the capability type, and must keep flowing through the
      -- plain `Ty.con name args` path below. A capability is always
      -- `Cap(permission)`; a bare `Cap` never is. -/
      if name == "Cap" && !args.isEmpty then .ok (Ty.con "Cap" args)
      -- `Tagged(_, Realtime)` drives march's Check 7 realtime exclusion (A3
      -- slice (b)). An applied `Tagged` (mirroring the `Cap` carve-out above)
      -- decodes to `Ty.con "Tagged" args`, preserving both arguments, so
      -- `CapCheck`'s Check 7 can inspect the second argument's constructor
      -- name to detect `Tagged(_, Realtime)`. (Slice (a) mapped this to
      -- `Ty.unsupported` — Check 7 was out of scope then, so the honest move
      -- was to skip rather than silently ignore the tag.) A hypothetical
      -- nullary `Tagged` user ADT (none exists today) would stay a normal
      -- `Ty.con` here, same as bare `Cap`.
      --
      -- Un-skipping is safe ONLY because `CapCheck.capsInTy` also consumes
      -- decoded types and now carries its own explicit
      -- `| .con "Tagged" _ => []` arm (matching march's `cap_paths_in_surface_ty`
      -- carve-out for `Tagged`) placed ahead of its generic `.con` recursion.
      -- Check 7 was NOT the only consumer of this decoded type — that was the
      -- mistaken assumption the first time this arm was un-skipped, and it
      -- opened a false-reject hole: `capsInTy`'s generic `.con` arm descended
      -- into `Tagged`'s payload and found `Cap(_)` types nested inside a
      -- `Tagged(Cap(X), Realtime)` annotation, rejecting files march accepts.
      -- Any future change here must re-check every decoded-`Ty` consumer, not
      -- just the one this change was written for.
      --
      -- One more consequence of un-skipping: a module whose ONLY
      -- out-of-fragment marker used to be an applied `Tagged` annotation
      -- previously decoded to `Ty.unsupported`, which made
      -- `Decl.hasUnsupported` true for the enclosing decl and drove
      -- `checkOneModule`'s return-cap fragment gate to defer (skip) on it.
      -- Now that `Tagged` decodes to a real `Ty.con`, such a module has
      -- `Decl.hasUnsupported = false` and the return-cap gate can fire on it
      -- where it previously deferred.
      else if name == "Tagged" && !args.isEmpty then .ok (Ty.con "Tagged" args)
      else .ok (Ty.con name args)
  | "TyVar" =>
      let (name, _) ← decodeName (← field j "name")
      match paramNames.findIdx? (· == name) with
      | some i => .ok (Ty.var (Int.ofNat i))
      | none => .ok Ty.unsupported
  | "TyArrow" =>
      .ok (Ty.arrow (← decodeSurfaceTy paramNames (← field j "from")) (← decodeSurfaceTy paramNames (← field j "to")))
  | "TyTuple" =>
      let elems ← (← (← field j "elements").getArr?.mapError (fun _ => "elements")).toList.mapM (decodeSurfaceTy paramNames)
      .ok (Ty.tuple elems)
  | "TyRecord" =>
      let fs ← (← (← field j "fields").getArr?.mapError (fun _ => "fields")).toList.mapM (fun f => do
        let (n, _) ← decodeName (← field f "name")
        let t ← decodeSurfaceTy paramNames (← field f "ty")
        pure (n, t))
      .ok (Ty.record fs)
  | "TyLinear" =>
      let lin ← decodeLin (← field j "lin")
      .ok (Ty.lin lin (← decodeSurfaceTy paramNames (← field j "ty")))
  | "TyNat" => .ok (Ty.nat (← (← field j "value").getNat?.mapError (fun _ => "value")))
  | "TyNatOp" =>
      let opKind ← kindOf (← field j "op")
      let op := if opKind == "NatAdd" then "add" else "mul"
      .ok (Ty.natOp op (← decodeSurfaceTy paramNames (← field j "lhs")) (← decodeSurfaceTy paramNames (← field j "rhs")))
  | _ => .ok Ty.unsupported   -- TyChan (session type), TyRefine (refinement) — out of fragment

/-- Decode the optional surface type annotation carried on the `"ty"` key of a
`param`/`binding` object (emitter's `param_to_json`/`binding_to_json`: `("ty",
json_opt ty_to_json ...)` — so it's `null` when the author wrote no
annotation, else a surface `ty` node). A missing key or JSON `null` → `none`;
otherwise decode via `decodeSurfaceTy`. These annotations are top-level (no
enclosing `DType` type-parameter list), so `paramNames = []`: a `TyVar`
reference (a generic type param — out of the A1 fragment) decodes to
`Ty.unsupported`, which propagates through `Term.hasUnsupported`/
`Decl.hasUnsupported` to force a whole-file skip rather than mis-binding. -/
def decodeOptAnnot (j : Json) : Except String (Option Ty) :=
  match j.getObjVal? "ty" with
  | .ok v => if v.isNull then .ok none else do .ok (some (← decodeSurfaceTy [] v))
  | .error _ => .ok none


mutual

/-- Decode an expr node into a `Term`. Every arm reads the node's own
`resolved_ty` first (via `decodeResolvedTy`) so it's threaded as `ty` on
whichever constructor is produced, including the `unsupported` fallback for
any `kind` not handled below (`EPipe`/`EAnnot`/`EHole`/`EResultRef`/`ESigil`
— plus, by design, every march `kind` that does not exist yet). `Term` has a
dedicated `letfn` constructor for a future `ELetFn` decoder, but since no
sample exercises it this file does not guess at an undertested
currying/sequencing shape: `ELetFn` decodes to `opaque_` (below) instead.
**`ELet` reaches this dispatch directly, and MUST have an arm here.** An
earlier revision of this docstring asserted the opposite ("march's grammar
only produces `ELet` as one element of an `EBlock`'s expr list"), and that
assertion was FALSE — it cost a whole class of false skips. march's emitter
does not wrap a single-statement `do` block in an `EBlock` at all: a fn body
that is one `ELet` is emitted as a bare `ELet` node, and `decodeBlockStmts`
funnels an `EBlock`'s FINAL element straight back here too (`[last] =>
decodeTerm last`). With no `ELet` arm, both shapes fell to the
`| _ => Term.unsupported` fallback at the bottom of this match, DISCARDING the
binding's right-hand side — and with it any `println` / allocation /
`10 / 0` / non-exhaustive `match` hiding in it. march rejected
`fn f() do let q = println("leak") end`; we exited 2. (The narrow symptom
that surfaced this was an `EApp` whose `fn` is an `ERecordUpdate` — but the
app-fn position was a red herring: `bodyCalls`'s generic `.app fn args` arm
was always correct, it simply never got a term to walk.)

A trailing `ELet` has no continuation to be the `Term.let_` body, so this arm
supplies `Term.unsupported` as the body. That keeps the RHS structurally
where every `CapCheck` walk already expects it (a real `let_`, so
`divisionVerdict`'s fact/path retirement still applies to the bound name —
unlike `opaque_`, which must empty both channels) while `hasUnsupported`
stays `true` through the unsupported body, so `Compare.inferModule`'s step-(1)
skip gate still fires and `Infer`/`Linearity` never judge the node. A
non-`PatVar`/`PatWild` pattern cannot be curried into `Term.let_`'s
plain-`String` binder, so it decodes to `Term.opaque_ [rhs]` instead: still
cap-transparent, still out of fragment, and — because `opaque_` empties
`divisionVerdict`'s channels — it cannot let a stale fact about a name the
pattern rebinds manufacture a false reject.

**The `opaque_` arms.** Nine `kind`s — `ECond`, `ERecordUpdate`, `EAtom`,
`EAssert`, `EDbg`, `ELetFn`, `ELetQ`, `ESend`, `ESpawn` — are still not
modelled, but each can NEST arbitrary sub-expressions, and march's
`calls_in_expr` (`typecheck.ml:7704-7752`) walks into all of them. They
therefore decode to `Term.opaque_ children ty`, carrying exactly the
sub-expression list march's own walk descends into and in march's order, so
`CapCheck`'s cap-layer walks can find a `cap pure`/`deterministic`/
`no_alloc`/`no_panic` violation hiding inside one. `Term.opaque_` still
reports `hasUnsupported = true`, so nothing else about these files changes —
they still hit the whole-file skip gate. Child fields were read off the
emitter (`lib/dump/ast_json.ml:379-503`), NOT guessed:

| `kind`          | emitter fields                    | children (march order) |
|-----------------|-----------------------------------|------------------------|
| `ECond`         | `arms : [{cond, body}]`           | `cond`,`body` per arm, in order (`calls_in_expr`: `calls_in_expr (calls_in_expr a ce) be`) |
| `ERecordUpdate` | `base`, `fields : [{name,value}]` | `base` then each `value` |
| `EAtom`         | `atom`, `args`                    | `args` (`atom` is a bare string) |
| `EAssert`       | `expr`                            | `expr` |
| `EDbg`          | `expr` (NULLABLE — `dbg()`)       | `[]` when null, else `expr` |
| `ELetFn`        | `name`,`params`,`ret_ty`,`body`   | `body` only — `params` are `param_to_json` records (`name`/`ty`/`lin`), no exprs, and march's `ELetFn` arm walks only `body` |
| `ELetQ`         | `pattern`,`value`,`cont`          | `value` then `cont` |
| `ESend`         | `cap`, `msg`                      | `cap` then `msg` |
| `ESpawn`        | `actor`                           | `actor` |

`EPipe`/`ESigil` are deliberately NOT here: `Desugar` eliminates both before
emission (`lib/desugar/desugar.ml:543-586`, `:733-744`), so arms for them
would be dead code. `EAnnot`/`EHole`/`EResultRef` are also excluded — no
parser production reaches them here, and `EHole`/`EResultRef` are leaves with
no sub-expression a capability could hide in. -/
partial def decodeTerm (j : Json) : Except String Term := do
  let ty ← decodeResolvedTy j
  match ← kindOf j with
  | "ELit" =>
      match ← decodeLit (← field j "literal") with
      | some l => .ok (Term.lit l ty)
      | none => .ok (Term.unsupported ty)
  | "EVar" =>
      let (txt, sp) ← decodeName (← field j "name")
      .ok (Term.var txt sp ty)
  | "EApp" =>
      -- N-ary: march's `EApp` is one node `fn` + `args` list, carrying a real
      -- `resolved_ty`. Model it directly — no currying into synthetic nodes.
      let fn ← decodeTerm (← field j "fn")
      let args ← (← (← field j "args").getArr?.mapError (fun _ => "args")).toList.mapM decodeTerm
      .ok (Term.app fn args ty)
  | "ECon" =>
      let (name, _) ← decodeName (← field j "name")
      let args ← (← (← field j "args").getArr?.mapError (fun _ => "args")).toList.mapM decodeTerm
      .ok (Term.con name args ty)
  | "ELam" =>
      -- N-ary: march's `ELam` carries a `params` list (each param object has a
      -- `name` and a `lin`) and a `body`, with the node's own `resolved_ty` the
      -- whole (possibly multi-arrow) function type. Model directly — no currying.
      let paramsJ ← (← field j "params").getArr?.mapError (fun _ => "params")
      let params ← paramsJ.toList.mapM (fun p => do
        let (n, _) ← decodeName (← field p "name")
        let lin ← decodeLin (← field p "lin")
        let annot ← decodeOptAnnot p
        pure (n, lin, annot))
      let body ← decodeTerm (← field j "body")
      .ok (Term.lam params body ty)
  | "EBlock" =>
      let exprsJ ← (← field j "exprs").getArr?.mapError (fun _ => "exprs")
      decodeBlockStmts exprsJ.toList ty
  | "EMatch" =>
      let scrut ← decodeTerm (← field j "scrutinee")
      let branchesJ ← (← field j "branches").getArr?.mapError (fun _ => "branches")
      let arms ← branchesJ.toList.mapM (fun b => do
        let guardJ ← field b "guard"
        let g ← if guardJ.isNull then pure none else (some <$> decodeTerm guardJ)
        let p ← decodePattern (← field b "pattern")
        let bodyTerm ← decodeTerm (← field b "body")
        pure (p, g, bodyTerm))
      .ok (Term.match_ scrut arms ty)
  | "ETuple" =>
      let elemsJ ← (← field j "elements").getArr?.mapError (fun _ => "elements")
      let elems ← elemsJ.toList.mapM decodeTerm
      .ok (Term.tuple elems ty)
  | "ERecord" =>
      let fsJ ← (← field j "fields").getArr?.mapError (fun _ => "fields")
      let fs ← fsJ.toList.mapM (fun f => do
        let (n, _) ← decodeName (← field f "name")
        let v ← decodeTerm (← field f "value")
        pure (n, v))
      .ok (Term.record fs ty)
  | "EField" =>
      let target ← decodeTerm (← field j "target")
      let (n, sp) ← decodeName (← field j "field")
      .ok (Term.field target n sp ty)
  | "EIf" =>
      let c ← decodeTerm (← field j "cond")
      let t ← decodeTerm (← field j "then_")
      let e ← decodeTerm (← field j "else_")
      .ok (Term.ite c t e ty)
  -- ── The nine `opaque_` kinds (see this function's docstring for the
  -- field-by-field emitter correspondence). Shape is NOT modelled; only the
  -- child EXPRESSIONS march's `calls_in_expr` walks are carried.
  | "ECond" =>
      -- `arms : [{cond, body}]` — BOTH halves are expressions, and march's
      -- `ECond` arm folds `cond` then `body` for each arm in order.
      let armsJ ← (← field j "arms").getArr?.mapError (fun _ => "arms")
      let kids ← armsJ.toList.mapM (fun a => do
        let c ← decodeTerm (← field a "cond")
        let b ← decodeTerm (← field a "body")
        pure [c, b])
      .ok (Term.opaque_ kids.flatten ty)
  | "ERecordUpdate" =>
      let base ← decodeTerm (← field j "base")
      let fsJ ← (← field j "fields").getArr?.mapError (fun _ => "fields")
      let vals ← fsJ.toList.mapM (fun f => do decodeTerm (← field f "value"))
      .ok (Term.opaque_ (base :: vals) ty)
  | "EAtom" =>
      let argsJ ← (← field j "args").getArr?.mapError (fun _ => "args")
      let args ← argsJ.toList.mapM decodeTerm
      .ok (Term.opaque_ args ty)
  | "EAssert" =>
      let e ← decodeTerm (← field j "expr")
      .ok (Term.opaque_ [e] ty)
  | "EDbg" =>
      -- `dbg()` emits `"expr": null` (`json_opt expr_to_json`); march's own
      -- `EDbg (None, _)` arm contributes nothing, so an absent child is an
      -- EMPTY child list, not a decode error.
      let eJ ← field j "expr"
      if eJ.isNull then .ok (Term.opaque_ [] ty)
      else do .ok (Term.opaque_ [← decodeTerm eJ] ty)
  | "ELetFn" =>
      -- `params` carry no expressions (`param_to_json` = name/ty/lin) and
      -- march's `ELetFn` arm walks only `body`.
      let body ← decodeTerm (← field j "body")
      .ok (Term.opaque_ [body] ty)
  | "ELetQ" =>
      let value ← decodeTerm (← field j "value")
      let cont ← decodeTerm (← field j "cont")
      .ok (Term.opaque_ [value, cont] ty)
  | "ESend" =>
      let cap ← decodeTerm (← field j "cap")
      let msg ← decodeTerm (← field j "msg")
      .ok (Term.opaque_ [cap, msg] ty)
  | "ESpawn" =>
      let actor ← decodeTerm (← field j "actor")
      .ok (Term.opaque_ [actor] ty)
  -- A TRAILING `ELet` — a `do` block's last (or only) statement. See this
  -- function's docstring: this arm's absence silently discarded the binding's
  -- RHS, hiding `cap` violations from every `CapCheck` walk at once.
  | "ELet" =>
      let binding ← field j "binding"
      let patJ ← field binding "pattern"
      let rhs ← decodeTerm (← field binding "expr")
      match ← kindOf patJ with
      | "PatVar" =>
          let (n, _) ← decodeName (← field patJ "name")
          let lin ← decodeLin (← field binding "lin")
          let annot ← decodeOptAnnot binding
          .ok (Term.let_ n lin annot rhs (Term.unsupported ty) ty)
      | "PatWild" =>
          let lin ← decodeLin (← field binding "lin")
          let annot ← decodeOptAnnot binding
          .ok (Term.let_ "_" lin annot rhs (Term.unsupported ty) ty)
      | _ => .ok (Term.opaque_ [rhs] ty)
  | _ => .ok (Term.unsupported ty)

/-- Desugar an `EBlock`'s flat expr list into `Term`'s nested-`let_` shape.
An `ELet` element binds its pattern around the recursively-decoded rest of
the block. The pattern must be `PatVar`/`PatWild` — anything else can't be
curried into `Term.let_`'s plain-`String` binder, so rather than
misrepresenting the binding the element decodes to
`Term.opaque_ [rhs, rest]`. (It used to decode to a bare
`Term.unsupported blockTy`, which threw away BOTH the binding's RHS and the
entire remainder of the block: `let (a, b) = (println("leak"), 1); a` is a
march reject that we skipped. `opaque_` keeps both children visible to the
`CapCheck` walks while still reporting `hasUnsupported = true`, and — unlike
a synthetic `let_ "_"` — it empties `divisionVerdict`'s fact/path channels,
so a stale fact about a name the destructuring pattern rebinds cannot
manufacture a false reject.) A non-`ELet`
statement in non-tail position (e.g. a `print(..)` call whose result is
discarded) is sequenced the same way, under a synthetic `"_"` binder — this
is the standard let-sequencing encoding of `e; rest`, and is exactly the
"a block is nested lets" desugaring `Term`'s shape calls for (Task 2 report:
"EBlock desugars to nested let_/sequencing in the decoder"). Every
synthesized `let_` node carries the *block's own* `resolved_ty` (`blockTy`)
as its `ty`, since a let's type is its body's type, and the whole chain's
ultimate body is the block's final expr. -/
partial def decodeBlockStmts (exprs : List Json) (blockTy : Ty) : Except String Term := do
  match exprs with
  | [] => .ok (Term.unsupported blockTy)
  | [last] => decodeTerm last
  | e :: rest => do
      let k ← kindOf e
      if k == "ELet" then
        let binding ← field e "binding"
        let patJ ← field binding "pattern"
        let patKind ← kindOf patJ
        let nameOpt ← (match patKind with
          | "PatVar" => do
              let (n, _) ← decodeName (← field patJ "name")
              pure (some n)
          | "PatWild" => pure (some "_")
          | _ => pure none : Except String (Option String))
        match nameOpt with
        | none =>
            -- Out-of-fragment BINDER, not an out-of-fragment block: keep both
            -- the RHS and the rest of the block walkable (docstring above).
            let rhs ← decodeTerm (← field binding "expr")
            let body ← decodeBlockStmts rest blockTy
            .ok (Term.opaque_ [rhs, body] blockTy)
        | some name =>
            let lin ← decodeLin (← field binding "lin")
            let annot ← decodeOptAnnot binding
            let rhs ← decodeTerm (← field binding "expr")
            let body ← decodeBlockStmts rest blockTy
            .ok (Term.let_ name lin annot rhs body blockTy)
      else
        let stmt ← decodeTerm e
        let body ← decodeBlockStmts rest blockTy
        .ok (Term.let_ "_" Lin.unrestricted none stmt body blockTy)

end -- mutual decodeTerm / decodeBlockStmts

/-- Decode one `fn_param` (`FPNamed`/`FPPat`/`FPDefault`) into a plain
`(name, lin)` pair. `none` for `FPPat`/`FPDefault` — a bare pattern-param or
a default-valued param can't be curried into `Term`'s plain-named-param
`lam`/`dfn` shape faithfully, so the caller (`decodeFnParams`) propagates
`none` to force the whole declaration to `Decl.unsupported`. -/
def decodeFnParam (p : Json) : Except String (Option (String × Lin × Option Ty)) := do
  match ← kindOf p with
  | "FPNamed" =>
      let param ← field p "param"
      let (n, _) ← decodeName (← field param "name")
      let lin ← decodeLin (← field param "lin")
      let annot ← decodeOptAnnot param
      .ok (some (n, lin, annot))
  | _ => .ok none

/-- Decode every param in a clause's param list; `none` overall (not just
per-param) if *any* param isn't a plain `FPNamed`. -/
def decodeFnParams (ps : List Json) : Except String (Option (List (String × Lin × Option Ty))) := do
  let raw ← ps.mapM decodeFnParam
  if raw.any Option.isNone then .ok none
  else .ok (some (raw.filterMap id))

/-- Extract the `Cap(X)` argument's constructor name from a `DExtern`'s
`extern.cap_ty` node — a surface type shaped
`{"kind":"TyCon","name":{"txt":"Cap"},"args":[<capCon>]}` (verified against
real emitter output, `.superpowers/sdd/samples/t50_*.json`: the argument's
own `name.txt` is already the fully dot-joined cap path, e.g.
`"IO.FileSystem"` — no further joining needed). Returns `none` for anything
that isn't exactly this shape (an absent/null `cap_ty`, an empty `args`, or
an unexpected node) rather than failing the whole decode: an extern block
declaring no capability is legal March, and `Decl.dextern` must not force a
skip on account of it. -/
def decodeCapTyArg (j : Json) : Option String := do
  let kindJ ← j.getObjVal? "kind" |>.toOption
  let kind ← kindJ.getStr?.toOption
  guard (kind == "TyCon")
  let argsJ ← j.getObjVal? "args" |>.toOption
  let argsArr ← argsJ.getArr?.toOption
  let arg ← argsArr[0]?
  let nameJ ← arg.getObjVal? "name" |>.toOption
  let txtJ ← nameJ.getObjVal? "txt" |>.toOption
  txtJ.getStr?.toOption

/-- Every name a decl binds into its enclosing module's scope, for the
flattening-safety guard in `decodeModule` below. `dneeds`/`duse`/`dextern`
bind no term/type name of their own (a capability manifest entry, an import,
and — at this decoding granularity — an extern block's declared capability
carry no name into the value/type namespace); `dmod`'s own decls are walked
separately by `flattenedBindingNames`, one scope level at a time, so `dmod`
itself contributes nothing here. -/
def declBindingName : Decl → Option String
  | .dfn n _ _ _ => some n
  | .dlet n _ => some n
  | .dtype n _ _ => some n
  | .dmod _ _ | .dneeds _ | .duse _ | .dextern _ _ | .dproofcap _ | .dopts _ | .unsupported => none

/-- Every binding name reachable once Task 4 flattens the tree (`dmod` is
transparent to inference — its decls splice into the enclosing scope,
recursively at every nesting level). Used only to detect collisions before
that splicing exists; this file does not itself flatten anything. -/
partial def flattenedBindingNames (decls : List Decl) : List String :=
  decls.flatMap (fun d =>
    match d with
    | .dmod _ nested => flattenedBindingNames nested
    | _ => (declBindingName d).toList)

/-- Would flattening this decl tree (Task 4's transparent-`dmod`
approximation) collide two decls under the same name? Module decl counts are
small, so the O(n²) scan is fine. -/
def hasNameCollision (decls : List Decl) : Bool :=
  let names := flattenedBindingNames decls
  names.any (fun n => (names.filter (· == n)).length > 1)

/-- Decode a top-level `decl` node. `DFn`/`DLet`/`DType` are the A1 term/type
fragment; `DMod`/`DNeeds`/`DUse`/`DExtern`/`DProofCap` are the A3
module-structure and capability-declaration fragment (Task 2; `DProofCap`
added for Finding I1 — see `Decl.dproofcap`); `DOpts` is the A3 slice (c)
behavioral-capability-cap declaration fragment (Task 1 — see `Decl.dopts`).
Every other decl kind (`DActor`, `DProtocol`, `DSig`, `DInterface`, `DImpl`,
`DAlias`, `DAlwaysLinearType`, `DTransitions`, `DApp`, `DDeriving`, `DSatisfy`,
`DTest`, `DDescribe`, `DSetup`, `DSetupAll`) decodes to `Decl.unsupported`. -/
partial def decodeDecl (j : Json) : Except String Decl := do
  match ← kindOf j with
  | "DFn" => do
      let fn ← field j "fn"
      let (name, _) ← decodeName (← field fn "name")
      -- The declared return-type annotation (`ret_ty`), decoded as `Option Ty`
      -- (`none` for an unannotated `fn` or a `null` `ret_ty`). A refinement
      -- (`{Int | _ >= 0}` → `TyRefine`), a session channel, or any other
      -- out-of-fragment return type decodes (via `decodeSurfaceTy`) to a type
      -- containing `Ty.unsupported`; such a return forces the whole
      -- declaration to `Decl.unsupported` (below), so the file honestly skips
      -- rather than checking only the (in-fragment) body and ignoring the
      -- annotation march rejected against (reject/t72). A missing/`null`
      -- `ret_ty` imposes no such constraint. An IN-fragment annotation is
      -- threaded onto `Decl.dfn.retAnnot` so `CapCheck` can scan it for
      -- Check 1: march scans `param_tys @ ret_tys` (`check_module_needs`), and
      -- a `Cap(X)` in RETURN position is exactly the coverage gap this closes.
      -- (Commit `e671226` changed exactly this for the 0-param case: a
      -- 0-param clause below now decodes to `Decl.dfn name [] retTy body` —
      -- an empty-param `dfn`, not a `Decl.dlet` — so a 0-param `fn () :
      -- Cap(X)` DOES carry its return annotation into Check 1's scan, same
      -- as any N-ary `dfn`. `Decl.dlet` is reserved for a genuine top-level
      -- `let x = ...` binding, which has no return annotation at all — see
      -- the comment on the 0-param arm ~20 lines below.)
      let retTy ← (match fn.getObjVal? "ret_ty" with
        | .ok v => if v.isNull then pure none else do
            let t ← decodeSurfaceTy [] v
            pure (some t)
        | .error _ => pure none : Except String (Option Ty))
      let retUnsupported := match retTy with
        | some t => t.hasUnsupported
        | none => false
      -- `fn.bounds` — the BRACKET-syntax explicit type-variable bound list
      -- (`fn f[a : SomeADT](…)`, `parser.mly:386/414`, `Ast.fn_bounds`
      -- `ast.ml:231`), emitted as `[{name, ty}]` (`ast_json.ml:830`). This
      -- decoder models NO part of it, and march does NOT merely record it:
      -- `typecheck.ml:6926-6959` VALIDATES every bound and raises a hard error
      -- when it is neither a known ADT, a known interface, nor `Nat` —
      -- "Bound `X` is not a known ADT or interface name." /
      -- "Bound `X` on type variable `a` must be an ADT name, interface name,
      -- or `Nat`." Both were verified directly as live march rejects
      -- (`fn f[a : NoSuchThing](x : Int) : Int do x end` and
      -- `fn f[a : Int -> Int](…)`), and both were FALSE ACCEPTS here while
      -- this field went unread. A bound also pre-registers its type variable
      -- so param annotations can reference it, which the A1 fragment (whose
      -- `decodeSurfaceTy` maps every `TyVar` to `Ty.unsupported`) cannot
      -- represent at all. So a bounded `fn` is out of fragment, exactly like a
      -- guarded clause below: `Decl.unsupported` ⇒ honest whole-file skip.
      -- Costs nothing in coverage — zero of the 490 emittable corpus files
      -- under `specs/`, `examples/`, `stdlib/` carry a non-empty `bounds`.
      let hasBounds : Bool :=
        match fn.getObjVal? "bounds" with
        | .error _ => false
        | .ok v => match v.getArr? with
          | .error _ => false
          | .ok arr => !arr.isEmpty
      if hasBounds then .ok Decl.unsupported else do
      let clausesJ ← (← field fn "clauses").getArr?.mapError (fun _ => "clauses")
      match clausesJ.toList with
      | [clause] => do
          let guard ← field clause "guard"
          if !guard.isNull then
            -- A guarded clause can't be represented (`Decl.dfn`'s body is a
            -- plain `Term`, with no guard slot) — see Task 2's doc comment
            -- on `Decl.dfn`, which calls for `Decl.unsupported` here.
            .ok Decl.unsupported
          else if retUnsupported then
            .ok Decl.unsupported
          else do
            let paramsJ ← (← field clause "params").getArr?.mapError (fun _ => "params")
            let paramsOpt ← decodeFnParams paramsJ.toList
            let bodyJ ← field clause "body"
            match paramsOpt with
            | none => .ok Decl.unsupported
            | some [] =>
                -- 0-param clause: still a genuine `Ast.DFn` in march's real
                -- AST (verified directly: `fn fail() : Int do panic("boom")
                -- end` emits `"kind":"DFn"`, never `"kind":"DLet"`), NOT an
                -- `Ast.DLet`. march's behavioral-cap checks
                -- (`check_pure_module`/`check_deterministic_module`/
                -- `check_no_panic_module`, `typecheck.ml`) scan `Ast.DFn`
                -- ONLY — folding a 0-param clause to `Decl.dlet` (the old
                -- A2-era convenience) hid it from any `dfn`-only scan.
                -- Decoding it to `Decl.dfn name [] retTy body` instead — an
                -- empty param list, not a currying trick — keeps it visible
                -- to `CapCheck`'s dfn-only scan, matching march's own
                -- DFn-only behavioral scan exactly, and also lets it carry
                -- its `retTy` annotation into Check 1's return-cap scan
                -- (previously dropped for the 0-param case; see
                -- `capsInReturnSignature`'s docstring). A genuine top-level
                -- `Ast.DLet` (a real `let x = ...` binding, JSON
                -- `{"kind":"DLet",...}`) is unaffected — it still decodes via
                -- the separate `"DLet"` arm below to `Decl.dlet`.
                let body ← decodeTerm bodyJ
                .ok (Decl.dfn name [] retTy body)
            | some params =>
                -- N-ary: carry the whole param list directly (no currying),
                -- plus the (in-fragment) return annotation for Check 1.
                let body ← decodeTerm bodyJ
                .ok (Decl.dfn name params retTy body)
      | _ => .ok Decl.unsupported   -- 0 or 2+ clauses: multi-clause fns unsupported
  | "DLet" => do
      let binding ← field j "binding"
      let patJ ← field binding "pattern"
      match ← kindOf patJ with
      | "PatVar" =>
          let (name, _) ← decodeName (← field patJ "name")
          let rhs ← decodeTerm (← field binding "expr")
          .ok (Decl.dlet name rhs)
      | _ => .ok Decl.unsupported
  | "DType" => do
      let (name, _) ← decodeName (← field j "name")
      let paramsJ ← (← field j "params").getArr?.mapError (fun _ => "params")
      let paramNames ← paramsJ.toList.mapM (fun p => do
        let (n, _) ← decodeName p
        pure n)
      let defJ ← field j "def"
      match ← kindOf defJ with
      | "TDVariant" =>
          let variantsJ ← (← field defJ "variants").getArr?.mapError (fun _ => "variants")
          let ctors ← variantsJ.toList.mapM (fun v => do
            let (vname, _) ← decodeName (← field v "name")
            let argsJ ← (← field v "args").getArr?.mapError (fun _ => "args")
            let argTys ← argsJ.toList.mapM (decodeSurfaceTy paramNames)
            let resultTy := Ty.con name ((List.range paramNames.length).map (fun i => Ty.var (Int.ofNat i)))
            pure ({ name := vname, argTys, resultTy } : CtorSig))
          .ok (Decl.dtype name paramNames ctors)
      | _ => .ok Decl.unsupported   -- TDAlias / TDRecord: not an ADT-with-ctors shape
  | "DMod" => do
      let (name, _) ← decodeName (← field j "name")
      let declsJ ← (← field j "decls").getArr?.mapError (fun _ => "DMod.decls")
      let decls ← declsJ.toList.mapM decodeDecl
      .ok (Decl.dmod name decls)
  | "DNeeds" => do
      -- `paths` is a list of paths; each path is a list of name objects
      -- (`{"txt":…,"span":…}`) — join each inner list's `txt` with "." to
      -- get one dotted cap like "IO.FileRead" (verified shape, samples/t46).
      let pathsJ ← (← field j "paths").getArr?.mapError (fun _ => "DNeeds.paths")
      let paths ← pathsJ.toList.mapM (fun p => do
        let segsJ ← p.getArr?.mapError (fun _ => "DNeeds.path segments")
        let segs ← segsJ.toList.mapM (fun s => do let (t, _) ← decodeName s; pure t)
        pure (String.intercalate "." segs))
      .ok (Decl.dneeds paths)
  | "DUse" => do
      -- The imported module path lives at `use.path` (a name-object list).
      -- `use.selector.kind` distinguishes a plain whole-module `use Vault`
      -- (`"UseSingle"`) from a selective `use Array.{lst_rev}`
      -- (`"UseNames"`). Selective import selects specific names whose
      -- visibility/privacy A3 does not model (march's import-name-privacy
      -- rule, reject/t27, is out of this slice's fragment); a plain
      -- whole-module `use` stays in fragment for Check 4 (verified shape,
      -- samples/t39). Defensive: if `selector`/`selector.kind` is missing or
      -- an unexpected shape, fall back to the plain-`use` behavior rather
      -- than erroring.
      let useJ ← field j "use"
      let selectorKind : String :=
        match useJ.getObjVal? "selector" with
        | .error _ => "UseSingle"
        | .ok sel =>
            match sel.getObjVal? "kind" with
            | .error _ => "UseSingle"
            | .ok k => match k.getStr? with
              | .error _ => "UseSingle"
              | .ok s => s
      if selectorKind == "UseNames" then .ok Decl.unsupported
      else
        let pathJ ← (← field useJ "path").getArr?.mapError (fun _ => "DUse.path")
        let segs ← pathJ.toList.mapM (fun s => do let (t, _) ← decodeName s; pure t)
        .ok (Decl.duse (String.intercalate "." segs))
  | "DExtern" => do
      -- The capability type lives at `extern.cap_ty` (NOT top-level), and is
      -- a type node, not a string (verified shape, samples/t50). An
      -- absent/null `cap_ty`, or one that isn't a `Cap(X)` application,
      -- decodes to `none` rather than failing — a capability-free extern
      -- block is legal March.
      let extJ ← field j "extern"
      let capTy := match extJ.getObjVal? "cap_ty" with
        | .error _ => none
        | .ok v => if v.isNull then none else decodeCapTyArg v
      -- `extern.fns` is a list of extern-fn objects, each carrying its own
      -- `name` (verified shape: emitting `extern "libc" : Cap(X) do fn
      -- counter_migrate_state(...) ... end` — samples/t50-shaped). Extracting
      -- just the names (not the params/ret_ty) is enough for Check 8 (Finding
      -- I2): march attributes the BLOCK's declared capability to every extern
      -- fn whose name matches `is_migrate_fn_name`, regardless of that fn's
      -- own signature. A missing/malformed `fns` array degrades to `[]`
      -- rather than failing the whole decode — an extern block is still
      -- legal March even if this particular fact can't be extracted.
      let fnNames : List String :=
        match extJ.getObjVal? "fns" with
        | .error _ => []
        | .ok v =>
            match v.getArr? with
            | .error _ => []
            | .ok arr => arr.toList.filterMap (fun f => do
                let nameJ ← f.getObjVal? "name" |>.toOption
                let txtJ ← nameJ.getObjVal? "txt" |>.toOption
                txtJ.getStr?.toOption)
      .ok (Decl.dextern capTy fnNames)
  | "DProofCap" => do
      -- `proof cap X` — carries just the declared bare name (verified shape:
      -- `{"kind":"DProofCap","name":{"txt":"Migrated","span":{...}},...}`).
      -- In-fragment (Finding I1): see `Decl.dproofcap`'s docstring.
      let (name, _) ← decodeName (← field j "name")
      .ok (Decl.dproofcap name)
  | "DOpts" => do
      -- `opts no_panic, ...` — a bare list of cap names (verified shape:
      -- `{"kind":"DOpts","opts":["no_panic"],"span":{…}}`; `opts` is a plain
      -- `List String`, not a list of name objects like `DNeeds.paths`).
      let optsJ ← (← field j "opts").getArr?.mapError (fun _ => "DOpts.opts")
      let opts ← optsJ.toList.mapM str
      .ok (Decl.dopts opts)
  | _ => .ok Decl.unsupported

partial def decodeConstraint (j : Json) : Except String Constraint := do
  match ← kindOf j with
  | "CNum" => .ok (Constraint.num (← decodeTy (← field j "ty")))
  | "COrd" => .ok (Constraint.ord (← decodeTy (← field j "ty")))
  | "CInterface" => .ok (Constraint.interface (← str (← field j "name")) (← decodeTy (← field j "ty")))
  | "CADTBound" => .ok (Constraint.adtBound (← str (← field j "name")) (← decodeTy (← field j "ty")))
  | "CTNatBound" => .ok (Constraint.tnatBound (← decodeTy (← field j "ty")))
  | _ => .ok Constraint.unsupported

def decodeScheme (j : Json) : Except String Scheme := do
  let ids ← (← (← field j "ids").getArr?.mapError (fun _ => "ids")).toList.mapM
              (fun x => x.getInt?.mapError (fun _ => "id"))
  let cs ← (← (← field j "constraints").getArr?.mapError (fun _ => "cs")).toList.mapM decodeConstraint
  .ok { ids, constraints := cs, body := (← decodeTy (← field j "body")) }

/-- Decode an instantiation witness `{"use_span":<span>, "ids":[Int...],
"args":[<ty>...]}`. `use_span` keys the same span a `Term.var`/`Term.field`
node carries, joining a use-site to its scheme (Task 4/5's job). -/
def decodeInstantiation (j : Json) : Except String Instantiation := do
  let sp ← decodeSpan (← field j "use_span")
  let ids ← (← (← field j "ids").getArr?.mapError (fun _ => "ids")).toList.mapM
              (fun x => x.getInt?.mapError (fun _ => "id"))
  let args ← (← (← field j "args").getArr?.mapError (fun _ => "args")).toList.mapM decodeTy
  .ok { useSpan := sp, ids, args }

/-- Top-level: decode the whole envelope's `module` + witness tables. Real
shape (verified against `bin/main.ml`'s envelope-building code and all 8
samples — NOT the brief's guessed `module.mod_decls` path): the module's
decl list is at `module.decls`, and `schemes`/`instantiations` are siblings
of `module` at the envelope's top level (not nested inside it). -/
def decodeModule (envelope : Json) : Except String Module := do
  let modJson ← field envelope "module"
  -- The entry module's own bare name (`module.name.txt`, e.g. `"Db"` for a
  -- file whose whole content is `mod Db do … end`). Carried on `Module` only
  -- to key `CapCheck`'s proof-cap self-declaration exemption (Finding I1) —
  -- nothing else consumes it.
  let (entryName, _) ← decodeName (← field modJson "name")
  let declsJ ← (← field modJson "decls").getArr?.mapError (fun _ => "decls")
  let decls ← declsJ.toList.mapM decodeDecl
  -- A3 flattening-safety guard: Task 4's `dmod`-transparent-to-inference
  -- approximation splices every nested module's decls into one enclosing
  -- scope, which is only sound while no two decls collide under that
  -- flattening. Rather than mis-approximate a colliding file, force the
  -- existing whole-file skip gate (`Decl.hasUnsupported`, read by
  -- `Compare.inferModule`) by appending a sentinel `unsupported` decl —
  -- the real decoded tree is otherwise left untouched.
  let decls := if hasNameCollision decls then decls ++ [Decl.unsupported] else decls
  let schemesJ ← (← field envelope "schemes").getArr?.mapError (fun _ => "schemes")
  let schemes ← schemesJ.toList.mapM decodeScheme
  let instsJ ← (← field envelope "instantiations").getArr?.mapError (fun _ => "insts")
  let insts ← instsJ.toList.mapM decodeInstantiation
  -- A3: the (module_name, declared_needs) table march emits at
  -- format_version 3. Required, not optional: treating a missing key as an
  -- empty table would turn an emitter regression into a false accept,
  -- because Check 4 would silently find nothing to enforce.
  let capsJ ← (← field envelope "module_caps").getArr?.mapError (fun _ => "module_caps")
  let moduleCaps ← capsJ.toList.mapM (fun c => do
    let m ← (← field c "module").getStr?.mapError (fun _ => "module_caps.module")
    let needsJ ← (← field c "needs").getArr?.mapError (fun _ => "module_caps.needs")
    let needs ← needsJ.toList.mapM (fun n =>
      n.getStr?.mapError (fun _ => "module_caps.needs entry"))
    pure (m, needs))
  .ok { decls, schemes, insts, moduleCaps, entryName }

end MarchLean.Elab

-- Living sanity checks (kept as executable documentation, matching the
-- existing convention in `MarchLean/Json.lean`).
namespace MarchLean.Elab.Test
open Lean MarchLean.Elab MarchLean.Syntax

-- A TCon decodes to Ty.con.
#eval (do
  let j ← Json.parse "{\"kind\":\"TCon\",\"name\":\"Int\",\"args\":[]}"
  decodeTy j : Except String _)
-- expected: Except.ok (Ty.con "Int" [])

-- An unknown ty kind decodes to unsupported (not an error).
#eval (do
  let j ← Json.parse "{\"kind\":\"TChanWeird\"}"
  decodeTy j : Except String _)
-- expected: Except.ok Ty.unsupported

-- Real-emitter-sample decode coverage lives in `scripts/conformance-harness.sh`
-- (it pipes `march --emit-core-ast` through `march-lean-check` over the full
-- corpus). Build-time `IO.FS.readFile` of sample files was removed: the source
-- must not depend on data files at a relative path (they broke CI on a fresh
-- checkout — the sample dir is gitignored scratch, not tracked).

-- A3 Task 2: module structure + capability declarations decode.
-- Self-contained: JSON built inline, matching the VERIFIED shapes in
-- `.superpowers/sdd/task-2-verified-shapes.md` (name objects always carry a
-- real `span`, unlike the task brief's guessed placeholder JSON) — never
-- read from a corpus sample.

-- DNeeds: a single need with one dotted segment.
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"DNeeds","paths":[[{"txt":"IO","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}]],"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeDecl j))
  -- expect: Except.ok (Decl.dneeds ["IO"])

-- DNeeds: two needs, the second a multi-segment dotted path (IO.FileRead).
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"DNeeds","paths":[[{"txt":"Clock","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}],[{"txt":"IO","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},{"txt":"FileRead","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}]],"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeDecl j))
  -- expect: Except.ok (Decl.dneeds ["Clock", "IO.FileRead"])

-- DUse: plain whole-module use (`selector.kind == "UseSingle"`) still
-- decodes to Decl.duse — Check 4 needs it.
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"DUse","use":{"path":[{"txt":"Vault","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}],"selector":{"kind":"UseSingle"}},"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeDecl j))
  -- expect: Except.ok (Decl.duse "Vault")

-- DUse: selective `use Array.{lst_rev}` (`selector.kind == "UseNames"`)
-- decodes to Decl.unsupported — import-name privacy is out of A3's fragment
-- (reject/t27).
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"DUse","use":{"path":[{"txt":"Array","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}],"selector":{"kind":"UseNames","names":[{"txt":"lst_rev","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}]}},"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeDecl j))
  -- expect: Except.ok Decl.unsupported

-- DExtern: cap_ty present, extracting the Cap(X) argument's constructor name.
-- No `fns`, so `fnNames = []`.
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"DExtern","extern":{"lib_name":"libc","cap_ty":{"kind":"TyCon","name":{"txt":"Cap","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[{"kind":"TyCon","name":{"txt":"IO.FileSystem","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[]}]},"fns":[]},"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeDecl j))
  -- expect: Except.ok (Decl.dextern (some "IO.FileSystem") [])

-- DExtern: cap_ty null (a capability-free extern block) decodes to `none`,
-- not a decode failure.
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"DExtern","extern":{"lib_name":"libc","cap_ty":null,"fns":[]},"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeDecl j))
  -- expect: Except.ok (Decl.dextern none [])

-- Finding I2: DExtern with a `fns` entry, extracting its `name.txt` into
-- `fnNames` (verified shape: emitting `extern "libc" : Cap(IO.Foreign) do fn
-- counter_migrate_state(old : Int) : Int end`, samples/t50-shaped).
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"DExtern","extern":{"lib_name":"libc","cap_ty":{"kind":"TyCon","name":{"txt":"Cap","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[{"kind":"TyCon","name":{"txt":"IO.Foreign","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[]}]},"fns":[{"name":{"txt":"counter_migrate_state","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"params":[],"ret_ty":{"kind":"TyCon","name":{"txt":"Int","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[]}}]},"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeDecl j))
  -- expect: Except.ok (Decl.dextern (some "IO.Foreign") ["counter_migrate_state"])

-- Finding I1: DProofCap decodes to Decl.dproofcap, carrying the bare declared
-- name (verified shape, real emitter output for `proof cap Migrated`).
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"DProofCap","name":{"txt":"Migrated","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeDecl j))
  -- expect: Except.ok (Decl.dproofcap "Migrated")

-- A3 slice (c) Task 1: DOpts decodes to Decl.dopts, carrying the bare cap
-- names (verified real emitter shape for `opts no_panic`:
-- `{"kind":"DOpts","opts":["no_panic"],"span":{...}}` — `opts` is a plain
-- `List String`, not a list of name objects).
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"DOpts","opts":["no_panic"],"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeDecl j))
  -- expect: Except.ok (Decl.dopts ["no_panic"])

-- DMod: nested module, name + recursive decls (here containing a DNeeds).
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"DMod","name":{"txt":"Vault","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"decls":[{"kind":"DNeeds","paths":[[{"txt":"IO","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}]],"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}],"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeDecl j))
  -- expect: Except.ok (Decl.dmod "Vault" [Decl.dneeds ["IO"]])

-- Flattening-safety guard: a top-level `f` and a nested `mod Vault`'s `f`
-- would collide once Task 4 splices `Vault`'s decls into the enclosing
-- scope, so `decodeModule` must force the whole-file skip gate
-- (`Decl.hasUnsupported`) by appending a sentinel `unsupported` decl.
private def collisionSpan : String := r#"{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}"#
private def collisionLit : String :=
  r#"{"kind":"ELit","literal":{"kind":"LitInt","value":1},"resolved_ty":{"kind":"TCon","name":"Int","args":[]}}"#
-- A `DLet` decl node binding plain name `n`, built with `++` (not `s!`) to
-- avoid the interpolation-escaping ambiguity of mixing literal `{`/`}` with
-- `{var}` splices in a JSON-heavy string.
private def collisionDLet (n : String) : String :=
  "{\"kind\":\"DLet\",\"binding\":{\"pattern\":{\"kind\":\"PatVar\",\"name\":{\"txt\":\"" ++ n ++
    "\",\"span\":" ++ collisionSpan ++ "}},\"lin\":{\"kind\":\"Unrestricted\"},\"expr\":" ++ collisionLit ++
    "},\"span\":" ++ collisionSpan ++ "}"
private def collisionEnvelope (nestedName : String) : String :=
  "{\"format_version\":3,\"verdict\":\"accept\",\"diagnostics\":[],\"module\":{\"name\":{\"txt\":\"Server\",\"span\":" ++
    collisionSpan ++ "},\"decls\":[" ++ collisionDLet "f" ++ ",{\"kind\":\"DMod\",\"name\":{\"txt\":\"Vault\",\"span\":" ++
    collisionSpan ++ "},\"decls\":[" ++ collisionDLet nestedName ++ "],\"span\":" ++ collisionSpan ++
    "}]},\"schemes\":[],\"instantiations\":[],\"module_caps\":[]}"

-- Flattening-safety guard: a top-level `f` and a nested `mod Vault`'s `f`
-- would collide once Task 4 splices `Vault`'s decls into the enclosing
-- scope, so `decodeModule` must force the whole-file skip gate
-- (`Decl.hasUnsupported`) by appending a sentinel `unsupported` decl.
#eval show IO Unit from do
  match Json.parse (collisionEnvelope "f") with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    =>
      match decodeModule j with
      | .error e => IO.println s!"decode failed: {e}"
      | .ok m    => IO.println s!"hasUnsupported={m.decls.any Decl.hasUnsupported}"
  -- expect: hasUnsupported=true (guard fired on the "f"/"f" collision)

-- Same shape, but the nested module's name doesn't collide ("g" vs "f") —
-- the guard must NOT false-trigger on distinctly-named decls.
#eval show IO Unit from do
  match Json.parse (collisionEnvelope "g") with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    =>
      match decodeModule j with
      | .error e => IO.println s!"decode failed: {e}"
      | .ok m    => IO.println s!"hasUnsupported={m.decls.any Decl.hasUnsupported}"
  -- expect: hasUnsupported=false (distinct names, no collision)

-- module_caps: a minimal but complete v3 envelope decodes its moduleCaps
-- table, de-duplicated/sorted-in table form (the emitter's job, not ours) —
-- here just two entries.
#eval show IO Unit from do
  let j := Json.parse r#"{"format_version":3,"verdict":"accept","diagnostics":[],"module":{"name":{"txt":"Server","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"decls":[]},"schemes":[],"instantiations":[],"module_caps":[{"module":"A","needs":[]},{"module":"Vault","needs":["IO.FileRead"]}]}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    =>
      match decodeModule j with
      | .error e => IO.println s!"decode failed: {e}"
      | .ok m    => IO.println (repr m.moduleCaps)
  -- expect: Except.ok ... -> [("A", []), ("Vault", ["IO.FileRead"])]

-- module_caps: a MISSING key is a hard decode error, not an empty list — an
-- emitter regression here must not silently disable Check 4.
#eval show IO Unit from do
  let j := Json.parse r#"{"format_version":3,"verdict":"accept","diagnostics":[],"module":{"name":{"txt":"Server","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"decls":[]},"schemes":[],"instantiations":[]}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    =>
      match decodeModule j with
      | .error e => IO.println s!"decode failed as expected: {e}"
      | .ok _    => IO.println "UNEXPECTED: decoded ok, should have errored"
  -- expect: "decode failed as expected: missing field 'module_caps'"

-- A3 fix: an APPLIED `Cap(IO.Network)` param annotation now decodes to the
-- first-class capability con `Ty.con "Cap" [Ty.con "IO.Network" []]`, NOT
-- `Ty.unsupported` — this is the shape `CapCheck.capsInTy`'s
-- `Ty.con "Cap" [Ty.con x _]` match requires for Check 1 to ever fire.
#eval show IO Unit from do
  let j := Json.parse r#"{"ty":{"kind":"TyCon","name":{"txt":"Cap","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[{"kind":"TyCon","name":{"txt":"IO.Network","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[]}]}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeOptAnnot j))
  -- expect: Except.ok (some (Ty.con "Cap" [Ty.con "IO.Network" []]))

-- Regression guard: a NULLARY `Cap` (the user ADT `type Cap = C(Int)` from
-- accept/t80 — no applied argument) must still decode as an ordinary `Ty.con
-- "Cap" []`, i.e. it must NOT be mistaken for the capability con. Only the
-- APPLIED form is special-cased.
#eval show IO Unit from do
  let j := Json.parse r#"{"ty":{"kind":"TyCon","name":{"txt":"Cap","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[]}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeOptAnnot j))
  -- expect: Except.ok (some (Ty.con "Cap" []))

-- A3 slice (b): an APPLIED `Tagged(Int, Realtime)` param annotation now
-- decodes to `Ty.con "Tagged" [Ty.con "Int" [], Ty.con "Realtime" []]` —
-- preserving both arguments (neither `Int` nor `Realtime` is itself
-- unsupported) — so `Ty.hasUnsupported = false` and the file is NOT skipped
-- on this construct alone. `CapCheck`'s Check 7 (realtime exclusion) is what
-- now polices `Tagged(_, Realtime)` combined with an excluded `Cap`
-- (reject/t41), not the out-of-fragment skip gate (slice (a)'s behaviour).
#eval show IO Unit from do
  let j := Json.parse r#"{"ty":{"kind":"TyCon","name":{"txt":"Tagged","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[{"kind":"TyCon","name":{"txt":"Int","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[]},{"kind":"TyCon","name":{"txt":"Realtime","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[]}]}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    =>
      match decodeOptAnnot j with
      | .error e => IO.println s!"decode failed: {e}"
      | .ok none => IO.println "UNEXPECTED: none"
      | .ok (some t) => IO.println s!"decoded={repr t}, hasUnsupported={t.hasUnsupported}"
  -- expect: decoded=Ty.con "Tagged" [Ty.con "Int" [], Ty.con "Realtime" []], hasUnsupported=false

-- A TRAILING `ELet` reaches `decodeTerm` directly (march emits a
-- single-statement `do` block as a bare node, with no `EBlock` wrapper, and
-- `decodeBlockStmts` routes an `EBlock`'s FINAL element back here too) and
-- MUST keep its RHS. Before the `"ELet"` arm existed this fell to
-- `| _ => Term.unsupported`, silently discarding the right-hand side and
-- blinding `bodyCalls`/`bodyAllocates`/`divisionVerdict`/`matchesIn` at once.
-- The `let_`'s BODY is `Term.unsupported` (there is no continuation), which
-- is what keeps `hasUnsupported = true` and the file skipping.
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"ELet","resolved_ty":{"kind":"TCon","name":"Unit","args":[]},"binding":{"pattern":{"kind":"PatVar","name":{"txt":"q","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}},"lin":{"kind":"Unrestricted"},"expr":{"kind":"EVar","resolved_ty":{"kind":"TCon","name":"Unit","args":[]},"name":{"txt":"println","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}}}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    =>
      match decodeTerm j with
      | .error e => IO.println s!"decode failed: {e}"
      | .ok t => IO.println s!"decoded={repr t}, hasUnsupported={t.hasUnsupported}"
  -- expect: Term.let_ "q" .. (rhs = Term.var "println" ..) (body = Term.unsupported);
  -- hasUnsupported=true

-- A trailing `ELet` whose pattern is NOT `PatVar`/`PatWild` cannot be curried
-- into `Term.let_`'s plain-`String` binder, so it decodes to
-- `Term.opaque_ [rhs]` — still cap-transparent, still out of fragment.
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"ELet","resolved_ty":{"kind":"TCon","name":"Unit","args":[]},"binding":{"pattern":{"kind":"PatTuple","elements":[]},"lin":{"kind":"Unrestricted"},"expr":{"kind":"EVar","resolved_ty":{"kind":"TCon","name":"Unit","args":[]},"name":{"txt":"println","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}}}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    =>
      match decodeTerm j with
      | .error e => IO.println s!"decode failed: {e}"
      | .ok t => IO.println s!"decoded={repr t}, hasUnsupported={t.hasUnsupported}"
  -- expect: Term.opaque_ [Term.var "println" ..] (Ty.con "Unit" []); hasUnsupported=true

-- `fn.bounds` regression. A non-empty bracket-syntax bound list
-- (`fn f[a : NoSuchThing]() do 0 end`) must force `Decl.unsupported`: march
-- VALIDATES each bound (`typecheck.ml:6926-6959`) and rejects one that names
-- neither a known ADT, a known interface, nor `Nat`, so leaving this field
-- unread was a live FALSE ACCEPT (march exit 1, this checker exit 0 —
-- verified directly for both `[a : NoSuchThing]` and `[a : Int -> Int]`).
-- The two envelopes below differ ONLY in `bounds`.
private def dfnBoundsEmpty : String :=
  r#"{"kind":"DFn","fn":{"name":{"txt":"f","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"ret_ty":null,"bounds":[],"clauses":[{"guard":null,"params":[],"body":{"kind":"ELit","literal":{"kind":"LitInt","value":0},"resolved_ty":{"kind":"TCon","name":"Int","args":[]}}}]}}"#
private def dfnBoundsNonEmpty : String :=
  r#"{"kind":"DFn","fn":{"name":{"txt":"f","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"ret_ty":null,"bounds":[{"name":{"txt":"a","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"ty":{"kind":"TyCon","name":{"txt":"NoSuchThing","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[]}}],"clauses":[{"guard":null,"params":[],"body":{"kind":"ELit","literal":{"kind":"LitInt","value":0},"resolved_ty":{"kind":"TCon","name":"Int","args":[]}}}]}}"#

#eval show IO Unit from do
  for (label, src) in [("empty-bounds", dfnBoundsEmpty), ("nonempty-bounds", dfnBoundsNonEmpty)] do
    match Json.parse src with
    | .error e => IO.println s!"{label}: parse failed: {e}"
    | .ok j =>
        match decodeDecl j with
        | .error e => IO.println s!"{label}: decode failed: {e}"
        | .ok d => IO.println s!"{label}: unsupported={d.hasUnsupported}"
  -- expected: empty-bounds: unsupported=false
  -- expected: nonempty-bounds: unsupported=true

end MarchLean.Elab.Test
