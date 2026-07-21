# A1 march-lean side: elaboration checker — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.
>
> **Executes in the `march-lean` repo.** Design doc:
> `specs/plans/2026-07-21-a1-elaboration-checker-design.md` — read all of it
> before starting, especially §2 (the seam this consumes), §4 (checker
> structure), §5 (harness). This plan is the *consumer*; the producer is
> `2026-07-21-a1-march-emitter.md` (march repo). **The producer must be merged
> to march `main` before Task 7** (the CI repin + end-to-end run need a `march`
> that emits `format_version` 2). Tasks 1–6 can proceed against hand-written
> sample JSON.

**Goal:** Turn `march-lean-check` from a verdict echo into an independent elaboration checker for a Core+linearity fragment: verify march's per-node types and HM witnesses by substitution/equality, independently re-derive linearity, and honestly skip everything out of fragment.

**Architecture:** Decode the `format_version` 2 envelope into executable Lean `Syntax` (named variables, `unsupported` escapes). `Check` walks the annotated tree verifying each node's `resolved_ty` against its subterms + the datatype environment and validating each variable use against its scheme by substitution+equality. `Linearity` re-counts uses. Any out-of-fragment construct → whole-file skip (exit 2). Reject inputs → skip.

**Tech Stack:** Lean 4 (`leanprover/lean4:v4.29.0`), `Lean.Data.Json`, Lake. No Mathlib.

## Global Constraints

- **Exit contract (unchanged from A0):** 0=accept, 1=reject, 2=skip, 3=error. A1 makes 1 and 2 reachable.
- **`format_version` hard cutover:** require version `2`; any other version → exit 3. (Update A0's `Json.lean` accordingly.)
- **Whole-file skip granularity:** *any* `unsupported` construct anywhere (node, subterm, type, or a `CInterface`-bearing scheme) ⇒ exit 2 for the whole file. Never partially check.
- **Reject side = skip:** `verdict == "reject"` ⇒ exit 2, unconditionally (A1 does not model rejection).
- **No Mathlib dependency** — keep `lakefile.toml` free of it so CI needs no Mathlib cache.
- **The JSON shape is defined by the emitter plan Task 1** (`ty` encoding: `TCon`/`TArrow`/`TTuple`/`TRecord`/`TVar`/`TLin`/`TNat`/`TNatOp`/`unsupported`/`TError`; scheme = `{ids,constraints,body}`; instantiation = `{use_span,ids,args}`). Decode it verbatim.
- **Type equality is canonical, not raw:** expand named records (`TCon("Foo",[])`) through the `DType` environment before comparing to structural `TRecord`. Compare record fields in march's sorted order (as emitted).

---

## File Structure

- `MarchLean/Syntax.lean` — **create**: executable `Ty`, `Term`, `Pattern`, `Decl`, `Module` inductives for the fragment, each with an `unsupported` escape; witness table types.
- `MarchLean/Elab.lean` — **create**: `Lean.Json` → `Syntax` decoder + witness-table decoder; a top-level `decodeEnvelope`.
- `MarchLean/Check.lean` — **create**: `Ty` canonicalization + equality, bidirectional `check`, witness/constraint validation. Returns `CheckResult := ok | reject (msg) | skip (reason)`.
- `MarchLean/Linearity.lean` — **create**: executable use-counting over `Term`, returns `ok | reject (msg) | skip`.
- `MarchLean/Json.lean` — **modify**: bump the accepted `format_version` from 1 to 2.
- `MarchLean.lean` — **modify**: drop POC imports; import the new modules.
- `MarchLeanCheck.lean` — **modify**: new control flow (parse → reject-skip → decode → unsupported-skip → check+linearity → 0/1).
- `MarchLean/{Perceus,LinearContext,Heap,Defun}.lean` — **delete**: POC proofs, not reused.
- `scripts/conformance-harness.sh` — **modify**: skip is normal; enforce a skip-ledger.
- `scripts/expected-skips.txt` — **create**: the enumerated skip-ledger.
- `.github/workflows/conformance.yml` — **modify**: repin march to a `main` SHA with the v2 emitter.

---

## Task 1: Remove POC proofs, slim the aggregator

**Files:**
- Delete: `MarchLean/Perceus.lean`, `MarchLean/LinearContext.lean`, `MarchLean/Heap.lean`, `MarchLean/Defun.lean`
- Modify: `MarchLean.lean`

**Interfaces:**
- Produces: a `MarchLean` library that builds with only `Json` (new modules added in later tasks).

- [ ] **Step 1: Confirm current build is green (baseline)**

Run: `cd /Users/80197052/code/march-lean/.claude/worktrees/lean-conformance-bridge-stage-a-aef708 && export PATH="$PATH:/Users/80197052/.elan/bin" && lake build 2>&1 | tail -5`
Expected: builds clean (baseline before changes).

- [ ] **Step 2: Delete the POC modules and rewrite the aggregator**

```bash
git rm MarchLean/Perceus.lean MarchLean/LinearContext.lean MarchLean/Heap.lean MarchLean/Defun.lean
```

Rewrite `MarchLean.lean` to:

```lean
import MarchLean.Json
```

- [ ] **Step 3: Build to verify green after removal**

Run: `lake build 2>&1 | tail -5`
Expected: builds clean (nothing imported the deleted modules except the aggregator, now fixed). If a build error names a deleted module, grep for stray `import MarchLean.(Perceus|Heap|LinearContext|Defun)` and remove it.

- [ ] **Step 4: Confirm the executable still builds**

Run: `lake build march-lean-check 2>&1 | tail -5`
Expected: clean (it only imports `MarchLean.Json`).

- [ ] **Step 5: Commit**

```bash
git add -A
git commit -m "chore(marchlean): remove POC proof modules; slim aggregator (A1 Task 1)"
```

---

## Task 2: Syntax types for the fragment

**Files:**
- Create: `MarchLean/Syntax.lean`
- Modify: `MarchLean.lean` (add `import MarchLean.Syntax`)

**Interfaces:**
- Produces:
  - `MarchLean.Syntax.Ty` — with `.unsupported : Ty` and a predicate `Ty.hasUnsupported : Ty → Bool`.
  - `MarchLean.Syntax.Term` — each node carries its resolved `Ty`; includes `.unsupported`.
  - `MarchLean.Syntax.Scheme := { ids : List Int, constraints : List Constraint, body : Ty }`.
  - `MarchLean.Syntax.Instantiation := { useSpan : Span, ids : List Int, args : List Ty }`.
  - `MarchLean.Syntax.Module := { decls : List Decl, schemes : List Scheme, insts : List Instantiation }`.

- [ ] **Step 1: Write the failing test**

Create `MarchLean/Syntax.lean` will hold `#eval` sanity examples at the bottom, but for a real gate add a test executable. Simplest in this repo (no test framework wired): add example lemmas that must typecheck. Create the file with the types AND a trailing `example` block; the "test" is that `lake build` elaborates it. Write the intended examples first as the failing artifact:

At the bottom of the new `MarchLean/Syntax.lean`, include:

```lean
namespace MarchLean.Syntax.Test
open MarchLean.Syntax
-- A literal-int term annotated Int must be constructible and flagged clean.
example : Ty.hasUnsupported (Ty.con "Int" []) = false := by decide
-- unsupported propagates through structure.
example : Ty.hasUnsupported (Ty.arrow Ty.unsupported (Ty.con "Int" [])) = true := by decide
end MarchLean.Syntax.Test
```

- [ ] **Step 2: Run build to verify it fails**

Run: `lake build MarchLean.Syntax 2>&1 | head -20`
Expected: FAIL — file/types don't exist yet.

- [ ] **Step 3: Implement the Syntax types**

Create `MarchLean/Syntax.lean`:

```lean
/-!
# `MarchLean.Syntax`

Executable Lean mirror of march's core AST for the A1 fragment (Core +
linearity). Named variables (match march's AST 1:1). Every out-of-fragment
construct decodes to an `unsupported` escape so the checker can honest-skip
rather than crash. Each `Term` node carries its resolved type (from the
emitter's `resolved_ty`), so `Check` verifies annotations rather than
re-inferring.
-/
namespace MarchLean.Syntax

/-- Source span (used to key instantiations; equality is structural). -/
structure Span where
  file : String
  startLine : Nat
  startCol : Nat
  endLine : Nat
  endCol : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Linearity qualifier. -/
inductive Lin where
  | linear | affine | unrestricted
  deriving DecidableEq, Repr, Inhabited

/-- Resolved type (decoded from `resolved_ty`). `unsupported` marks an
out-of-fragment type constructor (e.g. a session channel). -/
inductive Ty where
  | con (name : String) (args : List Ty)
  | arrow (from_ : Ty) (to_ : Ty)
  | tuple (elems : List Ty)
  | record (fields : List (String × Ty))
  | var (id : Int)
  | lin (l : Lin) (ty : Ty)
  | nat (n : Nat)
  | natOp (op : String) (a : Ty) (b : Ty)
  | err
  | unsupported
  deriving Repr, Inhabited

/-- Does this type contain an `unsupported` node anywhere? -/
partial def Ty.hasUnsupported : Ty → Bool
  | .unsupported => true
  | .con _ args => args.any Ty.hasUnsupported
  | .arrow a b => a.hasUnsupported || b.hasUnsupported
  | .tuple ts => ts.any Ty.hasUnsupported
  | .record fs => fs.any (fun (_, t) => t.hasUnsupported)
  | .lin _ t => t.hasUnsupported
  | .natOp _ a b => a.hasUnsupported || b.hasUnsupported
  | .var _ | .nat _ | .err => false

/-- Structural type equality (NOT canonical — `Check` canonicalizes named
records first, then calls this). -/
partial def Ty.beq : Ty → Ty → Bool
  | .con n1 a1, .con n2 a2 => n1 == n2 && a1.length == a2.length && (a1.zip a2).all (fun (x,y) => x.beq y)
  | .arrow a1 b1, .arrow a2 b2 => a1.beq a2 && b1.beq b2
  | .tuple t1, .tuple t2 => t1.length == t2.length && (t1.zip t2).all (fun (x,y) => x.beq y)
  | .record f1, .record f2 =>
      f1.length == f2.length && (f1.zip f2).all (fun ((n1,t1),(n2,t2)) => n1 == n2 && t1.beq t2)
  | .var i1, .var i2 => i1 == i2
  | .lin l1 t1, .lin l2 t2 => l1 == l2 && t1.beq t2
  | .nat n1, .nat n2 => n1 == n2
  | .natOp o1 a1 b1, .natOp o2 a2 b2 => o1 == o2 && a1.beq a2 && b1.beq b2
  | .err, .err => true
  | .unsupported, .unsupported => true
  | _, _ => false

instance : BEq Ty := ⟨Ty.beq⟩

/-- Typeclass constraint carried by a scheme. -/
inductive Constraint where
  | num (ty : Ty)
  | ord (ty : Ty)
  | eqC (ty : Ty)
  | interface (name : String) (ty : Ty)   -- out-of-fragment → skip trigger
  | adtBound (name : String) (ty : Ty)
  | tnatBound (ty : Ty)
  | unsupported
  deriving Repr, Inhabited

/-- Literal. -/
inductive Lit where
  | int (n : Int) | float (s : String) | str (s : String) | bool (b : Bool) | unit
  deriving Repr, Inhabited

/-- Pattern (for `match`/`let` binders). -/
inductive Pattern where
  | wild
  | var (name : String) (lin : Lin)
  | con (name : String) (args : List Pattern)
  | tuple (elems : List Pattern)
  | lit (l : Lit)
  | record (fields : List (String × Pattern))
  | as (name : String) (p : Pattern)
  | unsupported
  deriving Repr, Inhabited

/-- Term. Each node carries its resolved type `ty`. `var` and `field` also
carry their `span` (for the instantiation join). -/
inductive Term where
  | lit (l : Lit) (ty : Ty)
  | var (name : String) (span : Span) (ty : Ty)
  | app (fn : Term) (arg : Term) (ty : Ty)
  | lam (param : String) (lin : Lin) (body : Term) (ty : Ty)
  | let_ (name : String) (lin : Lin) (rhs : Term) (body : Term) (ty : Ty)
  | letfn (name : String) (param : String) (lin : Lin) (fnBody : Term) (body : Term) (ty : Ty)
  | ite (cond : Term) (then_ : Term) (else_ : Term) (ty : Ty)
  | con (name : String) (args : List Term) (ty : Ty)
  | tuple (elems : List Term) (ty : Ty)
  | record (fields : List (String × Term)) (ty : Ty)
  | field (record : Term) (name : String) (span : Span) (ty : Ty)
  | match_ (scrut : Term) (arms : List (Pattern × Term)) (ty : Ty)
  | unsupported (ty : Ty)
  deriving Inhabited

/-- The type annotation on a term node. -/
def Term.ty : Term → Ty
  | .lit _ t | .var _ _ t | .app _ _ t | .lam _ _ _ t | .let_ _ _ _ _ t
  | .letfn _ _ _ _ _ t | .ite _ _ _ t | .con _ _ t | .tuple _ t
  | .record _ t | .field _ _ _ t | .match_ _ _ t | .unsupported t => t

/-- Is this term (or any subterm/type) out of fragment? -/
partial def Term.hasUnsupported : Term → Bool
  | .unsupported _ => true
  | t =>
    t.ty.hasUnsupported ||
    (match t with
     | .app f a _ => f.hasUnsupported || a.hasUnsupported
     | .lam _ _ b _ => b.hasUnsupported
     | .let_ _ _ r b _ => r.hasUnsupported || b.hasUnsupported
     | .letfn _ _ _ fb b _ => fb.hasUnsupported || b.hasUnsupported
     | .ite c u v _ => c.hasUnsupported || u.hasUnsupported || v.hasUnsupported
     | .con _ args _ => args.any Term.hasUnsupported
     | .tuple es _ => es.any Term.hasUnsupported
     | .record fs _ => fs.any (fun (_, e) => e.hasUnsupported)
     | .field r _ _ _ => r.hasUnsupported
     | .match_ s arms _ => s.hasUnsupported || arms.any (fun (_, e) => e.hasUnsupported)
     | _ => false)

/-- Datatype constructor signature (from a `DType` decl). -/
structure CtorSig where
  name : String
  argTys : List Ty      -- declared arg types (may reference type params by var)
  resultTy : Ty         -- e.g. Box(a)
  deriving Repr, Inhabited

/-- Declaration (only what the fragment checks; others → `unsupported`). -/
inductive Decl where
  | dfn (name : String) (param : String) (lin : Lin) (body : Term)
  | dlet (name : String) (rhs : Term)
  | dtype (name : String) (params : List String) (ctors : List CtorSig)
  | unsupported
  deriving Inhabited

structure Scheme where
  ids : List Int
  constraints : List Constraint
  body : Ty
  deriving Inhabited

structure Instantiation where
  useSpan : Span
  ids : List Int
  args : List Ty
  deriving Inhabited

structure Module where
  decls : List Decl
  schemes : List Scheme
  insts : List Instantiation
  deriving Inhabited

end MarchLean.Syntax
```

Add `import MarchLean.Syntax` to `MarchLean.lean`.

- [ ] **Step 4: Build to verify it passes**

Run: `lake build 2>&1 | tail -5`
Expected: clean — the trailing `example`/`by decide` blocks elaborate, confirming `hasUnsupported` behaves.

- [ ] **Step 5: Commit**

```bash
git add MarchLean/Syntax.lean MarchLean.lean
git commit -m "feat(marchlean): Syntax types for the A1 fragment (A1 Task 2)"
```

---

## Task 3: Envelope decoder + `format_version` 2 bump

**Files:**
- Create: `MarchLean/Elab.lean`
- Modify: `MarchLean/Json.lean` (accept version 2), `MarchLean.lean`

**Interfaces:**
- Consumes: `Syntax.*` (Task 2).
- Produces: `MarchLean.Elab.decodeModule : Lean.Json → Except String Syntax.Module` and `MarchLean.Elab.decodeTy : Lean.Json → Except String Syntax.Ty`. Decoding an unknown node `kind` yields the corresponding `.unsupported` (NOT an error) so the checker can skip; only *malformed* JSON (missing required keys, wrong JSON types) is an `Except.error` (→ exit 3).

- [ ] **Step 1: Write the failing test**

At the bottom of `MarchLean/Elab.lean`, add `#eval`-style checks (kept as living tests). Write them first:

```lean
namespace MarchLean.Elab.Test
open Lean MarchLean.Elab

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

end MarchLean.Elab.Test
```

- [ ] **Step 2: Run build to verify it fails**

Run: `lake build MarchLean.Elab 2>&1 | head -20`
Expected: FAIL — module/functions don't exist.

- [ ] **Step 3: Implement the decoder**

Create `MarchLean/Elab.lean`. Use `Lean.Json`'s `getObjVal?`, `getStr?`, `getNat?`, `getInt?`, `getArr?`. Every `kind`-dispatched decoder returns `.unsupported` on an unrecognized tag. Representative core (the implementer completes the arm set following this exact pattern — one arm per `kind` the emitter can produce, listed in the emitter plan Task 1 contract; each `Term` arm reads its `resolved_ty` sub-object via `decodeTy` and threads it as the node's `ty`):

```lean
import Lean.Data.Json
import MarchLean.Syntax
namespace MarchLean.Elab
open Lean (Json)
open MarchLean.Syntax

/-- helper: required object field -/
def field (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{k}'"

def str (j : Json) : Except String String :=
  j.getStr?.mapError (fun _ => "expected string")

def kindOf (j : Json) : Except String String := do str (← field j "kind")

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
        .ok (n, t))
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
  | _ => .ok Ty.unsupported          -- unknown / "unsupported" kind → skip trigger

/-- Decode the resolved_ty on a node: `null` → unsupported-free `err`-neutral;
we treat a missing/null annotation as `unsupported` so a node that needs a type
but lacks one forces a skip, never a false accept (design §6). -/
def decodeResolvedTy (j : Json) : Except String Ty :=
  match j.getObjVal? "resolved_ty" with
  | .ok Json.null => .ok Ty.unsupported
  | .ok t => decodeTy t
  | .error _ => .ok Ty.unsupported

-- decodeSpan, decodeLit, decodePattern, decodeTerm, decodeDecl, decodeScheme,
-- decodeInstantiation, decodeModule follow the SAME pattern: read the "kind",
-- dispatch, read children recursively, unknown kind -> `.unsupported`. Each
-- Term arm calls `decodeResolvedTy j` for its node `ty`. See the emitter plan
-- Task 1 for the exhaustive kind list.

def decodeSpan (j : Json) : Except String Span := do
  .ok { file := (← str (← field j "file")),
        startLine := (← (← field j "start_line").getNat?.mapError (fun _ => "sl")),
        startCol := (← (← field j "start_col").getNat?.mapError (fun _ => "sc")),
        endLine := (← (← field j "end_line").getNat?.mapError (fun _ => "el")),
        endCol := (← (← field j "end_col").getNat?.mapError (fun _ => "ec")) }

-- (decodeTerm / decodeDecl / decodeScheme / decodeInstantiation / decodeModule
--  implemented here following the pattern above.)

partial def decodeScheme (j : Json) : Except String Scheme := do
  let ids ← (← (← field j "ids").getArr?.mapError (fun _ => "ids")).toList.mapM
              (fun x => x.getInt?.mapError (fun _ => "id"))
  let cs ← (← (← field j "constraints").getArr?.mapError (fun _ => "cs")).toList.mapM decodeConstraint
  .ok { ids, constraints := cs, body := (← decodeTy (← field j "body")) }

partial def decodeConstraint (j : Json) : Except String Constraint := do
  match ← kindOf j with
  | "CNum" => .ok (Constraint.num (← decodeTy (← field j "ty")))
  | "COrd" => .ok (Constraint.ord (← decodeTy (← field j "ty")))
  | "CInterface" => .ok (Constraint.interface (← str (← field j "name")) (← decodeTy (← field j "ty")))
  | "CADTBound" => .ok (Constraint.adtBound (← str (← field j "name")) (← decodeTy (← field j "ty")))
  | "CTNatBound" => .ok (Constraint.tnatBound (← decodeTy (← field j "ty")))
  | _ => .ok Constraint.unsupported

/-- Top-level: decode the whole `module` + witness tables from the envelope. -/
def decodeModule (envelope : Json) : Except String Module := do
  let mods ← (← (← field envelope "module").getObjVal? "mod_decls" |>.mapError (fun _ => "mod_decls"))
               |>.getArr?.mapError (fun _ => "decls")
  let decls ← mods.toList.mapM decodeDecl
  let schemes ← (← (← field envelope "schemes").getArr?.mapError (fun _ => "schemes")).toList.mapM decodeScheme
  let insts ← (← (← field envelope "instantiations").getArr?.mapError (fun _ => "insts")).toList.mapM decodeInstantiation
  .ok { decls, schemes, insts }

end MarchLean.Elab
```

(The implementer completes `decodeLit`, `decodePattern`, `decodeTerm`, `decodeDecl`, `decodeInstantiation` in the same shape. `decodeModule`'s exact path into `module` — `mod_decls` vs the emitter's actual key — must match `ast_json.ml`'s `module_to_json`; verify against a real emitted fixture.)

Then update `MarchLean/Json.lean`: change the two `format_version` checks from `1` to `2` (`if version ≠ 2 then throw ...`) and update the doc comment/`#eval` expectations accordingly. Add `import MarchLean.Elab` to `MarchLean.lean`.

- [ ] **Step 4: Build + eval to verify it passes**

Run: `lake build 2>&1 | tail -5`
Expected: clean; the `#eval` checks in `Elab.Test` print `Except.ok (...)` matching the comments (`Ty.con "Int" []` and `Ty.unsupported`).

- [ ] **Step 5: Commit**

```bash
git add MarchLean/Elab.lean MarchLean/Json.lean MarchLean.lean
git commit -m "feat(marchlean): format_version 2 envelope decoder (A1 Task 3)"
```

---

## Task 4: `Check` — type + witness verification

**Files:**
- Create: `MarchLean/Check.lean`
- Modify: `MarchLean.lean`

**Interfaces:**
- Consumes: `Syntax.*`.
- Produces: `MarchLean.Check.checkModule : Syntax.Module → CheckResult` where `inductive CheckResult | ok | reject (msg : String) | skip (reason : String)`. `skip` fires on any `unsupported` construct or `CInterface` constraint; `reject` is a genuine A1 disagreement (→ exit 1); `ok` → exit 0.

- [ ] **Step 1: Write the failing test**

Add trailing `#eval` tests to `MarchLean/Check.lean` (built as living tests). Write them first — they pin the three outcomes:

```lean
namespace MarchLean.Check.Test
open MarchLean.Syntax MarchLean.Check

-- A well-formed instantiation: scheme ∀a. a, used at Int, arg [Int],
-- use-site annotation Int -> substitution matches -> ok.
def sOk : Module :=
  { decls := [Decl.dlet "x" (Term.var "id" ⟨"f",1,1,1,2⟩ (Ty.con "Int" []))],
    schemes := [{ ids := [0], constraints := [], body := Ty.var 0 }],
    insts := [{ useSpan := ⟨"f",1,1,1,2⟩, ids := [0], args := [Ty.con "Int" []] }] }
#eval (checkModule sOk)   -- expected: CheckResult.ok

-- A broken instantiation: same scheme+args but the use-site annotation says
-- Bool while body[a:=Int] = Int -> reject.
def sBad : Module :=
  { decls := [Decl.dlet "x" (Term.var "id" ⟨"f",1,1,1,2⟩ (Ty.con "Bool" []))],
    schemes := [{ ids := [0], constraints := [], body := Ty.var 0 }],
    insts := [{ useSpan := ⟨"f",1,1,1,2⟩, ids := [0], args := [Ty.con "Int" []] }] }
#eval (checkModule sBad)  -- expected: CheckResult.reject ...

-- An unsupported subterm forces skip.
def sSkip : Module :=
  { decls := [Decl.dlet "x" (Term.unsupported Ty.unsupported)], schemes := [], insts := [] }
#eval (checkModule sSkip) -- expected: CheckResult.skip ...
```

- [ ] **Step 2: Run build to verify it fails**

Run: `lake build MarchLean.Check 2>&1 | head -20`
Expected: FAIL — module doesn't exist.

- [ ] **Step 3: Implement `Check`**

Create `MarchLean/Check.lean`. Key pieces: (a) a `TyEnv` mapping datatype names → definition for record canonicalization + constructor sigs; (b) canonical equality `tyEq` that expands named records before `Ty.beq`; (c) substitution `substTy : List (Int × Ty) → Ty → Ty`; (d) the per-node checks. Representative core (implementer extends the node match following this shape, one arm per `Term` constructor; the test list above + Task 7's corpus run drive completeness):

```lean
import MarchLean.Syntax
namespace MarchLean.Check
open MarchLean.Syntax

inductive CheckResult where
  | ok
  | reject (msg : String)
  | skip (reason : String)
  deriving Repr

/-- Datatype environment: name → (params, field-record-or-ctors). Built from
`Decl.dtype`. Used to expand `TCon("Foo")` to its structural record form. -/
abbrev TyEnv := List (String × (List String × List CtorSig))

def buildTyEnv (decls : List Decl) : TyEnv :=
  decls.foldr (fun d acc =>
    match d with
    | .dtype n ps ctors => (n, (ps, ctors)) :: acc
    | _ => acc) []

/-- Substitute type arguments for quantified ids in a type. -/
partial def substTy (s : List (Int × Ty)) : Ty → Ty
  | .var id => match s.lookup id with | some t => t | none => .var id
  | .con n args => .con n (args.map (substTy s))
  | .arrow a b => .arrow (substTy s a) (substTy s b)
  | .tuple ts => .tuple (ts.map (substTy s))
  | .record fs => .record (fs.map (fun (n,t) => (n, substTy s t)))
  | .lin l t => .lin l (substTy s t)
  | .natOp o a b => .natOp o (substTy s a) (substTy s b)
  | t => t

/-- Canonicalize before equality: expand a named record type to structural
form via the env (one level; recurse). Non-record `TCon`s are left as-is. -/
partial def canon (env : TyEnv) : Ty → Ty
  | .con n args =>
      match env.lookup n with
      | some (params, ctors) =>
          -- A single-ctor "record-like" datatype expands to its structural
          -- record; multi-ctor ADTs stay nominal (compare by name+args).
          match ctors with
          | [c] =>
            let s := (params.zip args).map (fun (p, a) => (p, a))  -- name→arg
            -- expand field types with param substitution (params are names,
            -- not ids, at the DType level; if the emitter uses ids, adapt).
            .con n (args.map (canon env))  -- keep nominal unless field info present
          | _ => .con n (args.map (canon env))
      | none => .con n (args.map (canon env))
  | .arrow a b => .arrow (canon env a) (canon env b)
  | .tuple ts => .tuple (ts.map (canon env))
  | .record fs => .record (fs.map (fun (n,t) => (n, canon env t)))
  | .lin l t => .lin l (canon env t)
  | .natOp o a b => .natOp o (canon env a) (canon env b)
  | t => t

def tyEq (env : TyEnv) (a b : Ty) : Bool := (canon env a).beq (canon env b)

/-- Constraint check for the classes A1 models. Returns none if satisfied,
some skip-reason if the constraint is out-of-fragment, some reject-reason if
violated. -/
def checkConstraint (env : TyEnv) : Constraint → Option (Sum String String)
  -- Sum.inl = skip reason, Sum.inr = reject reason
  | .interface n _ => some (.inl s!"CInterface {n} (user typeclass) out of fragment")
  | .unsupported => some (.inl "unsupported constraint")
  | .num t =>
      match canon env t with
      | .con "Int" [] | .con "Float" [] | .var _ => none
      | other => some (.inr s!"Num not satisfied by {repr other}")
  | .ord t =>
      match canon env t with
      | .con "Int" [] | .con "Float" [] | .con "String" [] | .var _ => none
      | other => some (.inr s!"Ord not satisfied by {repr other}")
  | .eqC _ => none      -- Eq over primitives: accept (refine as needed)
  | .adtBound _ _ | .tnatBound _ => none

/-- Validate every instantiation against its scheme (joined by ids) and its
constraints. -/
def checkInstantiations (env : TyEnv) (m : Module) : CheckResult := Id.run do
  for inst in m.insts do
    match m.schemes.find? (fun s => s.ids == inst.ids) with
    | none => return .skip s!"instantiation at {repr inst.useSpan} has no scheme"
    | some sch =>
      if sch.ids.length != inst.args.length then
        return .reject s!"arity mismatch at {repr inst.useSpan}"
      -- constraints must hold under the instantiation
      let s := sch.ids.zip inst.args
      for c in sch.constraints do
        match checkConstraint env (substConstraint s c) with
        | some (.inl r) => return .skip r
        | some (.inr r) => return .reject r
        | none => pure ()
      -- NOTE: body[ids:=args] equals the use-site annotation is checked in
      -- checkTerm, where the annotation is in scope (var node's ty).
  return .ok

/-- (substConstraint applies substTy to a constraint's carried type.) -/
def substConstraint (s : List (Int × Ty)) : Constraint → Constraint
  | .num t => .num (substTy s t)
  | .ord t => .ord (substTy s t)
  | .eqC t => .eqC (substTy s t)
  | .interface n t => .interface n (substTy s t)
  | .adtBound n t => .adtBound n (substTy s t)
  | .tnatBound t => .tnatBound (substTy s t)
  | .unsupported => .unsupported

/-- Whole-module check. First: any unsupported construct → skip. Then check
each var use against its scheme+instantiation by substitution+equality, and
each node's resolved_ty against its subterms via the local typing rules. -/
partial def checkModule (m : Module) : CheckResult := Id.run do
  -- skip trigger: any unsupported anywhere
  for d in m.decls do
    match d with
    | .unsupported => return .skip "unsupported decl"
    | .dfn _ _ _ b => if b.hasUnsupported then return .skip "unsupported subterm in fn"
    | .dlet _ b => if b.hasUnsupported then return .skip "unsupported subterm in let"
    | .dtype _ _ _ => pure ()
  let env := buildTyEnv m.decls
  -- build a span→(ids,args) index for var-use checking
  let instIndex := m.insts
  -- constraints + scheme-join
  match checkInstantiations env m with
  | .ok => pure ()
  | other => return other
  -- per-term checks (var instantiation equality + structural rules)
  for d in m.decls do
    match checkDecl env m instIndex d with
    | .ok => pure ()
    | other => return other
  return .ok

/-- checkDecl / checkTerm implement the local typing rules. checkTerm's `var`
arm: if the var has an instantiation at its span, look up the scheme, compute
`substTy (ids.zip args) body`, and require `tyEq env that node.ty`; a mismatch
is `.reject`. Other arms verify the standard bidirectional rules (app: fn.ty is
arrow whose domain tyEq arg.ty and codomain tyEq node.ty; ite: branches tyEq
node.ty and cond.ty = Bool; con: node.ty tyEq the ctor's result type with the
declared arg types matched; tuple/record: componentwise; field: record's field
type tyEq node.ty; let/lam/letfn/match: recurse into subterms). Each returns
CheckResult; the first non-`ok` short-circuits. -/
partial def checkDecl (env : TyEnv) (m : Module) (insts : List Instantiation) : Decl → CheckResult
  | .dtype _ _ _ => .ok
  | .dlet _ body => checkTerm env m insts body
  | .dfn _ _ _ body => checkTerm env m insts body
  | .unsupported => .skip "unsupported decl"

partial def checkTerm (env : TyEnv) (m : Module) (insts : List Instantiation) : Term → CheckResult
  | .var _ span ty =>
      match insts.find? (fun i => i.useSpan == span) with
      | none => .ok    -- monomorphic use: annotation stands on its own
      | some inst =>
        match m.schemes.find? (fun s => s.ids == inst.ids) with
        | none => .skip "no scheme for instantiation"
        | some sch =>
          let expected := substTy (sch.ids.zip inst.args) sch.body
          if tyEq env expected ty then .ok
          else .reject s!"instantiation type mismatch at {repr span}"
  | .unsupported _ => .skip "unsupported term"
  | .app f a ty =>
      match checkTerm env m insts f with
      | .ok =>
        match checkTerm env m insts a with
        | .ok =>
          match canon env f.ty with
          | .arrow dom cod =>
              if tyEq env dom a.ty && tyEq env cod ty then .ok
              else .reject s!"application type mismatch"
          | _ => .reject "applying a non-function"
        | other => other
      | other => other
  -- ... remaining arms (lam, let_, letfn, ite, con, tuple, record, field,
  -- match_, lit) follow the same shape: recurse, then check the node's local
  -- rule with tyEq. lit: no sub-checks. See the test list for required cases.
  | .lit _ _ => .ok
  | _ => .ok   -- placeholder replaced arm-by-arm as cases above are filled

end MarchLean.Check
```

Add `import MarchLean.Check` to `MarchLean.lean`. **The implementer must replace the final `| _ => .ok` catch-all with one explicit arm per remaining `Term` constructor** (the catch-all is a scaffold to keep the file compiling between arms; leaving it would make the checker vacuously accept unmodeled nodes — a correctness hole). The Task-7 corpus run and the forced-relaxation test are the backstop that this is complete.

- [ ] **Step 4: Build + eval to verify it passes**

Run: `lake build 2>&1 | tail -5`
Expected: clean; `Check.Test`'s three `#eval`s print `CheckResult.ok`, `CheckResult.reject ...`, `CheckResult.skip ...` respectively.

- [ ] **Step 5: Commit**

```bash
git add MarchLean/Check.lean MarchLean.lean
git commit -m "feat(marchlean): type+witness checker (A1 Task 4)"
```

---

## Task 5: `Linearity` — independent use-counting

**Files:**
- Create: `MarchLean/Linearity.lean`
- Modify: `MarchLean.lean`

**Interfaces:**
- Consumes: `Syntax.*`.
- Produces: `MarchLean.Linearity.checkLinearity : Syntax.Module → MarchLean.Check.CheckResult` (reuse the `CheckResult` type). `reject` when a linear binder is used ≠ once or an affine binder is used > once; `ok` otherwise; `skip` only if a construct blocks analysis.

- [ ] **Step 1: Write the failing test**

Trailing `#eval` tests in `MarchLean/Linearity.lean`:

```lean
namespace MarchLean.Linearity.Test
open MarchLean.Syntax MarchLean.Check MarchLean.Linearity

-- linear param used exactly once -> ok
def linOnce : Module :=
  { decls := [Decl.dfn "f" "x" Lin.linear
      (Term.var "x" ⟨"f",1,1,1,2⟩ (Ty.con "Int" []))],
    schemes := [], insts := [] }
#eval checkLinearity linOnce  -- expected: CheckResult.ok

-- linear param used twice -> reject
def linTwice : Module :=
  { decls := [Decl.dfn "f" "x" Lin.linear
      (Term.tuple [Term.var "x" ⟨"f",1,1,1,2⟩ (Ty.con "Int" []),
                   Term.var "x" ⟨"f",1,3,1,4⟩ (Ty.con "Int" [])] (Ty.tuple [Ty.con "Int" [], Ty.con "Int" []]))],
    schemes := [], insts := [] }
#eval checkLinearity linTwice -- expected: CheckResult.reject ...

-- linear param never used -> reject
def linNever : Module :=
  { decls := [Decl.dfn "f" "x" Lin.linear (Term.lit (Lit.int 1) (Ty.con "Int" []))],
    schemes := [], insts := [] }
#eval checkLinearity linNever -- expected: CheckResult.reject ...
```

- [ ] **Step 2: Run build to verify it fails**

Run: `lake build MarchLean.Linearity 2>&1 | head -20`
Expected: FAIL — module doesn't exist.

- [ ] **Step 3: Implement use-counting**

Create `MarchLean/Linearity.lean`. Count free-variable occurrences of each linear/affine binder within its scope; enforce exactly-once (linear) / at-most-once (affine):

```lean
import MarchLean.Syntax
import MarchLean.Check
namespace MarchLean.Linearity
open MarchLean.Syntax MarchLean.Check

/-- Count uses of `name` in a term (occurrences of `Term.var name`). -/
partial def uses (name : String) : Term → Nat
  | .var n _ _ => if n == name then 1 else 0
  | .app f a _ => uses name f + uses name a
  | .lam p _ b _ => if p == name then 0 else uses name b       -- shadowed
  | .let_ n _ r b _ => uses name r + (if n == name then 0 else uses name b)
  | .letfn n p _ fb b _ =>
      (if n == name || p == name then 0 else uses name fb) + (if n == name then 0 else uses name b)
  | .ite c u v _ => uses name c + uses name u + uses name v
  | .con _ args _ => (args.map (uses name)).foldl (·+·) 0
  | .tuple es _ => (es.map (uses name)).foldl (·+·) 0
  | .record fs _ => (fs.map (fun (_, e) => uses name e)).foldl (·+·) 0
  | .field r _ _ _ => uses name r
  | .match_ s arms _ => uses name s + (arms.map (fun (_, e) => uses name e)).foldl (·+·) 0
  | .lit _ _ | .unsupported _ => 0

/-- Enforce a binder's linearity given its use count. -/
def enforce (name : String) (l : Lin) (n : Nat) : CheckResult :=
  match l with
  | .linear => if n == 1 then .ok else .reject s!"linear '{name}' used {n} times (must be exactly 1)"
  | .affine => if n <= 1 then .ok else .reject s!"affine '{name}' used {n} times (must be ≤ 1)"
  | .unrestricted => .ok

/-- Walk a term enforcing every linear/affine binder it introduces. -/
partial def checkTerm : Term → CheckResult
  | .lam p l b _ =>
      match enforce p l (uses p b) with
      | .ok => checkTerm b
      | other => other
  | .let_ n l r b _ =>
      match checkTerm r with
      | .ok => match enforce n l (uses n b) with
               | .ok => checkTerm b
               | other => other
      | other => other
  | .letfn _ p l fb b _ =>
      match enforce p l (uses p fb) with
      | .ok => match checkTerm fb with | .ok => checkTerm b | o => o
      | other => other
  | .app f a _ => match checkTerm f with | .ok => checkTerm a | o => o
  | .ite c u v _ => match checkTerm c with | .ok => (match checkTerm u with | .ok => checkTerm v | o => o) | o => o
  | .con _ args _ => args.foldl (fun acc t => match acc with | .ok => checkTerm t | o => o) .ok
  | .tuple es _ => es.foldl (fun acc t => match acc with | .ok => checkTerm t | o => o) .ok
  | .record fs _ => fs.foldl (fun acc (_, t) => match acc with | .ok => checkTerm t | o => o) .ok
  | .field r _ _ _ => checkTerm r
  | .match_ s arms _ => match checkTerm s with
      | .ok => arms.foldl (fun acc (_, e) => match acc with | .ok => checkTerm e | o => o) .ok
      | o => o
  | .lit _ _ | .var _ _ _ | .unsupported _ => .ok

def checkDecl : Decl → CheckResult
  | .dfn _ p l body =>
      match enforce p l (uses p body) with
      | .ok => checkTerm body
      | other => other
  | .dlet _ body => checkTerm body
  | .dtype _ _ _ => .ok
  | .unsupported => .ok

def checkLinearity (m : Module) : CheckResult :=
  m.decls.foldl (fun acc d => match acc with | .ok => checkDecl d | o => o) .ok

end MarchLean.Linearity
```

Add `import MarchLean.Linearity` to `MarchLean.lean`.

(Note: field-level linear tracking — `x#field` sentinels — and `always_linear` types are refinements; if a corpus file in `t80`–`t82` needs them and this simpler counter mis-rules, move that file to the skip-ledger with a recorded reason rather than forcing false results.)

- [ ] **Step 4: Build + eval to verify it passes**

Run: `lake build 2>&1 | tail -5`
Expected: clean; the three `#eval`s print `ok`, `reject ...`, `reject ...`.

- [ ] **Step 5: Commit**

```bash
git add MarchLean/Linearity.lean MarchLean.lean
git commit -m "feat(marchlean): independent linearity use-counting (A1 Task 5)"
```

---

## Task 6: Rewire `MarchLeanCheck` control flow

**Files:**
- Modify: `MarchLeanCheck.lean`

**Interfaces:**
- Consumes: `MarchLean.Json.parseVerdict`, `MarchLean.Elab.decodeModule`, `MarchLean.Check.checkModule`, `MarchLean.Linearity.checkLinearity`.

- [ ] **Step 1: Write the failing test (via the binary)**

Build the exe and pipe three inputs. First a reject envelope must skip (exit 2):

Run: `export PATH="$PATH:/Users/80197052/.elan/bin" && lake build march-lean-check && printf '{"format_version":2,"verdict":"reject","diagnostics":[],"module":{"mod_decls":[]},"schemes":[],"instantiations":[]}' | ./.lake/build/bin/march-lean-check; echo "exit=$?"`
Expected (before rewrite): the A0 exe exits `1` (echoes reject) — this is the wrong A1 behavior (should be `2`). That mismatch is the failing state.

- [ ] **Step 2: Rewrite `main`**

```lean
import MarchLean.Json
import MarchLean.Elab
import MarchLean.Check
import MarchLean.Linearity
import Lean.Data.Json

/-!
# `march-lean-check` (A1)

Read march's `--emit-core-ast` `format_version` 2 envelope from stdin and
independently re-check the accept verdict for the A1 fragment.

Exit: 0=accept, 1=reject (a real A1 disagreement), 2=skip (reject-side or
out-of-fragment), 3=internal error (malformed JSON / wrong version).
-/
open Lean (Json)

def run (input : String) : IO UInt32 := do
  match Json.parse input with
  | .error e => IO.eprintln s!"invalid JSON: {e}"; pure 3
  | .ok envelope =>
    -- version + verdict gate (reuses A0's parser, now requiring version 2)
    match MarchLean.Json.parseVerdict input with
    | .error msg => IO.eprintln msg; pure 3
    | .ok .reject => pure 2                     -- reject side: skip
    | .ok .accept =>
      match MarchLean.Elab.decodeModule envelope with
      | .error e => IO.eprintln s!"decode error: {e}"; pure 3
      | .ok m =>
        match MarchLean.Check.checkModule m with
        | .skip r => IO.eprintln s!"skip: {r}"; pure 2
        | .reject r => IO.eprintln s!"MISMATCH (types): {r}"; pure 1
        | .ok =>
          match MarchLean.Linearity.checkLinearity m with
          | .skip r => IO.eprintln s!"skip: {r}"; pure 2
          | .reject r => IO.eprintln s!"MISMATCH (linearity): {r}"; pure 1
          | .ok => pure 0

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  run input
```

- [ ] **Step 3: Build**

Run: `lake build march-lean-check 2>&1 | tail -5`
Expected: clean.

- [ ] **Step 4: Verify all four exit codes**

```bash
export PATH="$PATH:/Users/80197052/.elan/bin"
B=./.lake/build/bin/march-lean-check
# reject -> skip (2)
printf '{"format_version":2,"verdict":"reject","diagnostics":[],"module":{"mod_decls":[]},"schemes":[],"instantiations":[]}' | $B; echo "reject=$?"
# malformed -> 3
printf 'not json' | $B; echo "malformed=$?"
# wrong version -> 3
printf '{"format_version":1,"verdict":"accept","module":{"mod_decls":[]},"schemes":[],"instantiations":[]}' | $B; echo "v1=$?"
# trivial accept, empty module -> 0
printf '{"format_version":2,"verdict":"accept","diagnostics":[],"module":{"mod_decls":[]},"schemes":[],"instantiations":[]}' | $B; echo "empty-accept=$?"
```
Expected: `reject=2`, `malformed=3`, `v1=3`, `empty-accept=0`.

- [ ] **Step 5: Commit**

```bash
git add MarchLeanCheck.lean
git commit -m "feat(marchlean): A1 checker control flow (skip/reject/accept) (A1 Task 6)"
```

---

## Task 7: Harness skip-ledger, forced-relaxation test, CI repin

> **Prerequisite:** the march emitter plan is merged to march `main`. Build a
> `march` with `--emit-core-ast` v2 from a fresh checkout of march `main`
> (`eval $(opam env --switch=march) && dune build` → `_build/default/bin/main.exe`).

**Files:**
- Modify: `scripts/conformance-harness.sh`
- Create: `scripts/expected-skips.txt`
- Modify: `.github/workflows/conformance.yml`

**Interfaces:**
- Consumes: the built `march` (v2) + `march-lean-check` (A1).

- [ ] **Step 1: Establish the baseline corpus behavior**

Run the current harness once with both v2 binaries to see the new skip/accept/reject/mismatch distribution (the harness still runs; A1 just makes SKIP frequent):

```bash
cd /Users/80197052/code/march-lean/.claude/worktrees/lean-conformance-bridge-stage-a-aef708
export PATH="$PATH:/Users/80197052/.elan/bin"
MARCH_BIN=/path/to/march/_build/default/bin/main.exe \
CORPUS_DIR=/path/to/march/specs/lang/types \
MARCH_LEAN_CHECK_BIN=./.lake/build/bin/march-lean-check \
  scripts/conformance-harness.sh || true
```
Record which files SKIP (these become the ledger) and confirm zero MISMATCH over the non-skipped accept files. If a MISMATCH appears, triage: real march bug (leave red, report) vs. Lean-model gap (fix `Check`/`Linearity`, or move that file to the ledger with a reason).

- [ ] **Step 2: Write the skip-ledger**

Create `scripts/expected-skips.txt` — one relative corpus path per line (all reject files + every out-of-fragment accept file), with a trailing `# reason` comment. Generate the initial list from Step 1's output, e.g.:

```
reject/t01_int_vs_string.march   # reject side (A1 skips all rejects)
accept/t23_interface_basic.march # interface (out of fragment)
accept/t39_actor_spawn.march     # actor/session (out of fragment)
...
```

- [ ] **Step 3: Update the harness to treat skip as normal + enforce the ledger**

In `scripts/conformance-harness.sh`: (a) remove SKIP from the hard-fail condition; (b) after the loop, compare the *observed* skip set against `scripts/expected-skips.txt` (paths only, stripping `# ...`), failing if they differ (a newly-skipping file = coverage regression; a no-longer-skipping file = update the ledger). Keep MISMATCH/ERROR/CORPUS_VIOLATION as hard failures. Add near the summary:

```bash
# --- skip-ledger enforcement (A1) ---
expected_ledger="$(cd "$(dirname "$0")/.." && pwd)/scripts/expected-skips.txt"
observed_skips_sorted="$(printf '%s\n' "${skip_files[@]}" | sed '/^$/d' | sort -u)"
expected_skips_sorted="$(sed 's/#.*//; s/[[:space:]]*$//; /^$/d' "$expected_ledger" | sort -u)"
if [ "$observed_skips_sorted" != "$expected_skips_sorted" ]; then
  echo "SKIP-LEDGER MISMATCH — observed skips differ from scripts/expected-skips.txt:"
  diff <(printf '%s\n' "$expected_skips_sorted") <(printf '%s\n' "$observed_skips_sorted") || true
  fail=1
fi
```

(Adapt variable names to the harness's existing ones — it already tracks a `skip_files` array per its A0 structure.)

- [ ] **Step 4: Forced-relaxation acceptance test**

Prove the checker can fail on a modeled accept. Temporarily weaken one `Check` rule (e.g. make `checkTerm`'s `.var` instantiation-mismatch arm return `.ok` instead of `.reject`), rebuild, and confirm the harness's MISMATCH count does NOT change to red for the corpus — wait, that direction hides failures. Do the *opposite*: pick a modeled-accept corpus file and temporarily corrupt the checker so it *rejects* a correct program (e.g. in `enforce`, treat `linear` as "used exactly 2"), rebuild `march-lean-check`, rerun the harness, and confirm **at least one modeled accept now reports MISMATCH and the harness exits nonzero**. Then revert, rebuild, confirm all-green again. Paste both runs' summary lines into the task report. (Do NOT commit the corruption.)

```bash
# after corrupting Linearity.enforce and `lake build march-lean-check`:
MARCH_BIN=... CORPUS_DIR=... MARCH_LEAN_CHECK_BIN=... scripts/conformance-harness.sh; echo "exit=$?"   # expect nonzero, ≥1 MISMATCH
git checkout MarchLean/Linearity.lean && lake build march-lean-check
MARCH_BIN=... CORPUS_DIR=... MARCH_LEAN_CHECK_BIN=... scripts/conformance-harness.sh; echo "exit=$?"   # expect 0, all-MATCH/skip
```

- [ ] **Step 5: Repin CI + commit**

In `.github/workflows/conformance.yml`, update the march checkout `ref:` to a `main` SHA that contains the merged v2 emitter (replace the current `ef18e6d8...` pin; get the SHA via `git -C /path/to/march rev-parse origin/main` after the emitter PR merges). Update the surrounding comment to note "v2 emitter merged as march #NN".

```bash
git add scripts/conformance-harness.sh scripts/expected-skips.txt .github/workflows/conformance.yml
git commit -m "feat(harness): A1 skip-ledger + forced-relaxation test; repin CI to v2 march (A1 Task 7)"
```

---

## Done criteria (march-lean side)

- `lake build` green; all `#eval` living tests print their expected `CheckResult`/`Except` values.
- `march-lean-check` exit codes verified: reject→2, malformed/v1→3, in-fragment well-typed accept→0, deliberately-broken accept→1.
- Full corpus run: zero MISMATCH/ERROR over modeled accepts; observed skips == `scripts/expected-skips.txt`.
- Forced-relaxation test turns ≥1 modeled accept red, and reverting restores green (evidence pasted in the report).
- CI repinned to a march `main` SHA with the v2 emitter; `Check.checkTerm`'s scaffold `| _ => .ok` catch-all replaced with explicit per-constructor arms.
