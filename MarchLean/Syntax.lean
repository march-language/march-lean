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
  -- H3: a `TError` should never appear in accept output; if it does, honest-skip
  -- rather than check a file built on an elaboration error.
  | .err => true
  | .var _ | .nat _ => false

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
  -- Or-pattern (`p1 | p2 | ...`), march's `Ast.PatOr` (`ast.ml:49`), emitted
  -- as `{"kind":"PatOr","patterns":[...]}` (`dump/ast_json.ml`). march's
  -- `norm_pat_rows` expands a `PatOr` at every depth during exhaustiveness
  -- (`typecheck.ml:3966`) — `MarchLean.CapCheck.matchExhaustive` mirrors that
  -- by unioning each alternative's covered constructors (A3 slice (c) review
  -- finding C1).
  | or_ (alts : List Pattern)
  | unsupported
  deriving Repr, Inhabited

/-- Does this pattern contain an `unsupported` node anywhere? -/
partial def Pattern.hasUnsupported : Pattern → Bool
  | .unsupported => true
  | .con _ args => args.any Pattern.hasUnsupported
  | .tuple ps => ps.any Pattern.hasUnsupported
  | .record fs => fs.any (fun (_, p) => p.hasUnsupported)
  | .as _ p => p.hasUnsupported
  | .or_ alts => alts.any Pattern.hasUnsupported
  | .wild | .var _ _ | .lit _ => false

/-- Term. Each node carries its resolved type `ty`. `var` and `field` also
carry their `span` (for the instantiation join). -/
inductive Term where
  | lit (l : Lit) (ty : Ty)
  | var (name : String) (span : Span) (ty : Ty)
  | app (fn : Term) (args : List Term) (ty : Ty)
  -- Each param carries its optional SURFACE type annotation (`Option Ty`, the
  -- text the author wrote — `Int` in `fn f(x : Int)`). `Infer` unifies an
  -- annotated param with its annotation (march-faithful: an annotated binder
  -- HAS that type by definition); an unannotated param stays inferred.
  | lam (params : List (String × Lin × Option Ty)) (body : Term) (ty : Ty)
  -- `annot` is the let-binding's optional surface type annotation (`let x : Int
  -- = ...`); `Infer` unifies the rhs against it before generalizing.
  | let_ (name : String) (lin : Lin) (annot : Option Ty) (rhs : Term) (body : Term) (ty : Ty)
  | letfn (name : String) (param : String) (lin : Lin) (paramAnnot : Option Ty) (fnBody : Term) (body : Term) (ty : Ty)
  | ite (cond : Term) (then_ : Term) (else_ : Term) (ty : Ty)
  | con (name : String) (args : List Term) (ty : Ty)
  | tuple (elems : List Term) (ty : Ty)
  | record (fields : List (String × Term)) (ty : Ty)
  | field (record : Term) (name : String) (span : Span) (ty : Ty)
  -- Each arm's middle field is its optional `when` guard (A3 slice (c) Task
  -- 3) — `none` for a guardless arm, `some g` for `pat when g -> body`. A
  -- guardless arm's pattern counts toward `no_panic`'s exhaustiveness
  -- coverage (`CapCheck.matchExhaustive`); a guarded arm's does not, mirroring
  -- march's `check_exhaustiveness` (`typecheck.ml:4546`), which computes
  -- coverage over the GUARDLESS branches only.
  | match_ (scrut : Term) (arms : List (Pattern × Option Term × Term)) (ty : Ty)
  /-- **Out-of-fragment node that nonetheless CARRIES its child expressions.**

  Decoded (`Elab.decodeTerm`) from the nine march `kind`s whose own shape this
  fragment does not model but which can nest ARBITRARY sub-expressions:
  `ECond`, `ERecordUpdate`, `EAtom`, `EAssert`, `EDbg`, `ELetFn`, `ELetQ`,
  `ESend`, `ESpawn`. march's `calls_in_expr` (`typecheck.ml:7704`) is TOTAL
  over `Ast.expr` and descends into every one of them, so a `cap pure` /
  `cap deterministic` / `cap no_alloc` / `cap no_panic` violation can hide
  inside one. Decoding them to `unsupported` DISCARDED those children, so the
  capability layer could not see the violation and the file silently skipped
  (exit 2) where march rejected (exit 1).

  `children` is exactly the sub-expression list march's own walk descends
  into, in march's order — see each new arm of `Elab.decodeTerm`, keyed field
  by field to the emitter (`lib/dump/ast_json.ml`). NOTHING about the node's
  own semantics is modelled: not its shape, not its binders, not its
  evaluation order, not its arm structure. It is a bag of subterms.

  **`Term.hasUnsupported` is hard-coded `true` for this constructor** (see
  below), so a file containing one still trips `Compare.inferModule`'s
  whole-file skip gate exactly as `unsupported` does. `Infer` and `Linearity`
  therefore NEVER see an `opaque_` node, and this constructor carries ZERO
  false-reject exposure: the only pass that can act on it is
  `CapCheck.checkCaps`, which `MarchLeanCheck.run` invokes BEFORE that gate.
  Named `opaque_` (not `opaque`) because `opaque` is a Lean keyword — same
  trailing-underscore convention as `let_`/`match_`/`or_`. -/
  | opaque_ (children : List Term) (ty : Ty)
  | unsupported (ty : Ty)
  deriving Repr, Inhabited

/-- The type annotation on a term node. -/
def Term.ty : Term → Ty
  | .lit _ t | .var _ _ t | .app _ _ t | .lam _ _ t | .let_ _ _ _ _ _ t
  | .letfn _ _ _ _ _ _ t | .ite _ _ _ t | .con _ _ t | .tuple _ t
  | .record _ t | .field _ _ _ t | .match_ _ _ t | .opaque_ _ t
  | .unsupported t => t

/-- Does an optional surface annotation carry an out-of-fragment type? An
absent annotation is always in-fragment; a present one is out of fragment iff
its type is. Used by `Term.hasUnsupported`/`Decl.hasUnsupported` so an
annotation naming an unsupported type forces the whole-file skip. -/
def optTyHasUnsupported : Option Ty → Bool
  | none => false
  | some t => t.hasUnsupported

/-- Is this term (or any subterm/type) out of fragment? -/
partial def Term.hasUnsupported : Term → Bool
  | .unsupported _ => true
  -- LOAD-BEARING, and deliberately NOT a recursion into `children`: an
  -- `opaque_` node is out of fragment BY CONSTRUCTION (its own shape is
  -- unmodelled), independent of whether its children happen to be modelled.
  -- Hard-coding `true` is what keeps `Compare.inferModule`'s whole-file skip
  -- gate firing on exactly the files it fired on before this constructor
  -- existed, which is the entire reason carrying the children costs nothing
  -- in false-reject exposure. Do not "improve" this to
  -- `children.any hasUnsupported`.
  | .opaque_ _ _ => true
  | t =>
    t.ty.hasUnsupported ||
    (match t with
     | .app f args _ => f.hasUnsupported || args.any Term.hasUnsupported
     | .lam ps b _ => ps.any (fun (_, _, a) => optTyHasUnsupported a) || b.hasUnsupported
     | .let_ _ _ annot r b _ => optTyHasUnsupported annot || r.hasUnsupported || b.hasUnsupported
     | .letfn _ _ _ pa fb b _ => optTyHasUnsupported pa || fb.hasUnsupported || b.hasUnsupported
     | .ite c u v _ => c.hasUnsupported || u.hasUnsupported || v.hasUnsupported
     | .con _ args _ => args.any Term.hasUnsupported
     | .tuple es _ => es.any Term.hasUnsupported
     | .record fs _ => fs.any (fun (_, e) => e.hasUnsupported)
     | .field r _ _ _ => r.hasUnsupported
     | .match_ s arms _ => s.hasUnsupported ||
         arms.any (fun (p, g, e) => p.hasUnsupported || (g.map Term.hasUnsupported).getD false || e.hasUnsupported)
     | _ => false)

/-- A declaration's visibility — march's `Ast.visibility`, the `fn` vs `pfn`
distinction. Emitted on every `DFn` as `fn.vis`
(`{"kind":"Public"}` / `{"kind":"Private"}` — `lib/dump/ast_json.ml`'s
`visibility_to_json`, threaded from `fn_def_to_json`).

Carried because march's **Check 6** (proof-cap production enforcement,
`typecheck.ml:8091-8140`) branches on it: a PRIVATE function of a proof cap's
own declaring module may not mint that cap, while a PUBLIC one may — public
functions of the declaring module ARE the minting surface. Without this field
the two are indistinguishable and Check 6's same-module branch cannot be
modelled at all (it was a confirmed false accept; see
`CapCheck.checkOneModule`'s Check 6 block).

Named `pub`/`priv` rather than `public`/`private` because both of those are
Lean keywords. The decoder defaults to `pub` on ANY unrecognised or missing
`vis` payload — `pub` is the verdict-free value (Check 6's same-module branch
fires only on `priv`), so a decode failure degrades to no-reject, never to a
false reject. -/
inductive Vis where
  | pub | priv
  deriving DecidableEq, Repr, Inhabited

/-- Datatype constructor signature (from a `DType` decl). -/
structure CtorSig where
  name : String
  argTys : List Ty      -- declared arg types (may reference type params by var)
  resultTy : Ty         -- e.g. Box(a)
  deriving Repr, Inhabited

/-- Declaration (only what the fragment checks; others → `unsupported`). -/
inductive Decl where
  /-- Function declaration, modeled N-ARILY to match march's `DFn` faithfully
  (`params : List`, a clause's full parameter list). No currying — the whole
  param list is carried directly, so no synthetic intermediate nodes with
  unknown types are invented. A 0-param clause decodes to `dlet` instead. If
  the decoder can't represent a clause faithfully (multiple clauses, non-plain
  params, or a guard), it falls back to `Decl.unsupported`. The emitter attaches
  `resolved_ty` only to the *body* expression, not to the function itself, so a
  `dfn` carries no arrow type of its own; params' types (when needed) come from
  the enclosing context, not from a node field. Each param carries its optional
  surface type annotation (`Option Ty`) — `Infer` unifies an annotated param
  with its annotation.

  `retAnnot` is the function's optional surface RETURN-type annotation (the
  `Cap(IO.Network)` in `fn f(…) : Cap(IO.Network)`), decoded from the emitter's
  `ret_ty`. It is `none` for an unannotated `fn`, and — like a param annotation
  — is always in fragment when present, because the decoder forces the whole
  declaration to `Decl.unsupported` when the return annotation is out of
  fragment. `CapCheck.capsInReturnSignature` scans it so Check 1 covers
  `param_tys @ ret_tys` exactly as march's `check_module_needs` does, and
  `Infer.inferModule'`'s `dfn` arm unifies the inferred BODY type against it,
  exactly as it already does for each param annotation — march checks a
  clause's body against its declared return type, and leaving this
  unconstrained was a live false-accept class (see that arm's comment).

  `vis` is the `fn`/`pfn` marker (see `Vis`), read ONLY by Check 6. It is the
  FIRST field purely so the many hand-built fixtures below and in `CapCheck`
  read `Decl.dfn .pub "name" …`; nothing about the position is semantic. -/
  | dfn (vis : Vis) (name : String) (params : List (String × Lin × Option Ty)) (retAnnot : Option Ty) (body : Term)
  | dlet (name : String) (rhs : Term)
  | dtype (name : String) (params : List String) (ctors : List CtorSig)
  /-- A nested module, `mod Name do … end`. Carried as a TREE because `needs`
  is scoped to its own module: Check 1 asks whether *this* module's declared
  needs cover the `Cap(X)` types in *this* module's signatures. Inference, by
  contrast, treats a module as transparent and splices its decls into the
  enclosing scope (see `flattenDecls` below) — an approximation that holds
  only while names do not collide across sibling modules, which
  `Elab.decodeModule` guards against. -/
  | dmod (name : String) (decls : List Decl)
  /-- `needs IO.FileRead, IO.Clock` — the module's capability manifest, as
  dot-joined paths. -/
  | dneeds (paths : List String)
  /-- `use Vault` — a module import, as a dot-joined path. Drives Check 4. -/
  | duse (path : String)
  /-- An `extern "lib" : Cap(X) do … end` block. `capTy` is the dot-joined
  `X`, or `none` when the block declares no capability. `fnNames` is every
  extern fn's own name declared inside the block (`extern.fns[*].name.txt`,
  verified shape: `.superpowers/sdd/samples/t50_*.json`), independent of
  `capTy` — an extern block always carries a (possibly empty) `fns` list, cap
  or no cap. `capTy` drives Check 5; `fnNames` additionally drives Check 8
  (Finding I2 — an extern fn matching `is_migrate_fn_name` inherits the
  block's declared capability into its `own_caps` in march, exactly like a
  `DFn`'s own signature/body caps do). -/
  | dextern (capTy : Option String) (fnNames : List String)
  /-- `proof cap X` — declares `X` a nominal proof capability owned by this
  module. In-fragment (unlike slice (a), which mapped it to `Decl.unsupported`
  since Check 1's self-declaration exemption was out of scope then): carrying
  the bare declared name lets `CapCheck` recognize when a `Cap(Mod.X)` used in
  THIS module's own signatures is self-covered by this very declaration,
  mirroring march's `env.proof_caps` self-declaration exemption
  (`typecheck.ml:6966-6970`) for the one shape that mechanism actually reaches
  (see `CapCheck.checkCaps`'s docstring on `entryName` for the precise,
  narrower-than-it-looks scope of that exemption). -/
  | dproofcap (name : String)
  /-- `opts no_panic, ...` — a declaration's behavioral-capability-cap
  self-declaration list (A3 slice (c)), as bare cap names (e.g. `"no_panic"`).
  In-fragment (`hasUnsupported = false`): the real emitted JSON is
  `{"kind":"DOpts","opts":["no_panic"],"span":{…}}` (verified), and `opts` is
  a plain `List String` — no further decoding needed. -/
  | dopts (opts : List String)
  | unsupported
  deriving Repr, Inhabited

/-- Is this declaration (or any term/type it carries) out of fragment?
`dtype` carries no terms, but its constructor signatures may reference
out-of-fragment types, so those are checked too. The four A3 constructors are
IN fragment on their own (`dneeds`/`duse`/`dextern` carry no term/type of
their own); `dmod` recurses into its nested decls, since one of those could
still be an unsupported `dfn`/`dlet`/`dtype`. Marked `partial`: the recursion
through `List Decl` inside `dmod` isn't structurally recognized by the
kernel, matching how `Term.hasUnsupported` handles its own nesting. -/
partial def Decl.hasUnsupported : Decl → Bool
  | .unsupported => true
  | .dfn _ _ params retAnnot body =>
      params.any (fun (_, _, a) => optTyHasUnsupported a)
        || optTyHasUnsupported retAnnot || body.hasUnsupported
  | .dlet _ body => body.hasUnsupported
  | .dtype _ _ ctors =>
      ctors.any (fun c => c.argTys.any Ty.hasUnsupported || c.resultTy.hasUnsupported)
  | .dmod _ decls => decls.any Decl.hasUnsupported
  | .dneeds _ => false
  | .duse _ => false
  | .dextern _ _ => false
  | .dproofcap _ => false
  | .dopts _ => false

/-- Splice nested `dmod` decls into a single flat list, for the passes that
treat a module as a transparent scope (inference, linearity). Cap checking
does NOT use this — `needs` is scoped to its module, so `CapCheck` walks the
tree instead (see `Decl.dmod`'s docstring).

This is an approximation of march, which scopes names per module and supports
qualified cross-module references. It is sound only while names do not collide
across sibling modules; `Elab.decodeModule` refuses files where they do.
Marked `partial`: the recursion through `List Decl` inside `dmod` isn't
structurally recognized by the kernel, matching `Decl.hasUnsupported`. -/
partial def flattenDecls : List Decl → List Decl
  | [] => []
  | .dmod _ inner :: rest => flattenDecls inner ++ flattenDecls rest
  | d :: rest => d :: flattenDecls rest

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
  /-- The v3 `module_caps` envelope table: `(module name, declared needs)`
  pairs, keyed by bare module name (duplicates already resolved by the
  emitter — see `Elab.decodeModule`). Only records modules nested one level
  below the file's top-level module; NOT a complete module→needs map (see
  the A3 Task 2 shape-limits note). Drives Check 4.
  Defaults to `[]` so the many hand-built `Module` test fixtures elsewhere
  (`Linearity.lean`, `Compare.lean`, `Infer.lean`) that predate A3 and don't
  exercise capability checking keep compiling unchanged. -/
  moduleCaps : List (String × List String) := []
  /-- The bare name of the FILE'S OWN entry module (the envelope's
  `module.name`, e.g. `"Db"` for a file whose entire content is `mod Db do …
  end`). Used ONLY by `CapCheck.checkCaps` to key the proof-cap
  self-declaration exemption (Finding I1) at the top level — see that
  function's docstring for why the exemption is narrower than "same bare
  module name" and applies ONLY at this outermost level, never to a nested
  `dmod`. Defaults to `""` so the many hand-built `Module` fixtures elsewhere
  that predate this field keep compiling unchanged (an empty `entryName`
  simply means no self-declared cap will ever match, since a real cap path is
  never literally `".X"`). -/
  entryName : String := ""
  deriving Inhabited

end MarchLean.Syntax

namespace MarchLean.Syntax.Test
open MarchLean.Syntax
-- A literal-int term annotated Int must be constructible and flagged clean.
-- `Ty.hasUnsupported` is a `partial def` (nested recursion through `List.any`
-- isn't structurally-recognized by the kernel), so plain `decide` gets stuck
-- unfolding it; `native_decide` evaluates via the compiler instead.
example : Ty.hasUnsupported (Ty.con "Int" []) = false := by native_decide
-- unsupported propagates through structure.
example : Ty.hasUnsupported (Ty.arrow Ty.unsupported (Ty.con "Int" [])) = true := by native_decide
-- H3: `TError` is a skip trigger — a TError anywhere flags the type.
example : Ty.hasUnsupported Ty.err = true := by native_decide
example : Ty.hasUnsupported (Ty.tuple [Ty.con "Int" [], Ty.err]) = true := by native_decide

-- Regression for the false-accept bug where `Term.hasUnsupported`'s
-- `match_` arm discarded the `Pattern` component of each arm, so an
-- `unsupported` pattern nested in a match arm was invisible.
private def intTy : Ty := Ty.con "Int" []
private def dummySpan : Span := ⟨"f", 0, 0, 0, 0⟩
private def okScrut : Term := Term.lit (Lit.int 0) intTy
private def okArm : Pattern × Option Term × Term := (Pattern.wild, none, Term.lit (Lit.int 1) intTy)
private def badArm : Pattern × Option Term × Term := (Pattern.unsupported, none, Term.lit (Lit.int 1) intTy)
-- Nested inside a `con` pattern too, not just at the top level of the arm.
private def badNestedArm : Pattern × Option Term × Term :=
  (Pattern.con "Some" [Pattern.unsupported], none, Term.lit (Lit.int 1) intTy)

-- A match with only clean patterns/arms is in-fragment.
example : Term.hasUnsupported (Term.match_ okScrut [okArm] intTy) = false := by native_decide
-- A match with an `unsupported` pattern directly in an arm must be flagged
-- (this is exactly what the old code missed: `fun (_, e) => e.hasUnsupported`
-- ignored the pattern).
example : Term.hasUnsupported (Term.match_ okScrut [okArm, badArm] intTy) = true := by native_decide
-- Same, but the `unsupported` is nested inside a constructor pattern.
example : Term.hasUnsupported (Term.match_ okScrut [okArm, badNestedArm] intTy) = true := by native_decide
-- `Pattern.hasUnsupported` itself, standalone: top-level and nested.
example : Pattern.hasUnsupported Pattern.wild = false := by native_decide
example : Pattern.hasUnsupported Pattern.unsupported = true := by native_decide
example : Pattern.hasUnsupported (Pattern.tuple [Pattern.wild, Pattern.unsupported]) = true := by
  native_decide
example : Pattern.hasUnsupported (Pattern.as "x" Pattern.unsupported) = true := by native_decide
-- `Pattern.or_`: clean alternatives are in-fragment; an `unsupported`
-- alternative anywhere in the list is not (A3 slice (c) review finding C1).
example : Pattern.hasUnsupported (Pattern.or_ [Pattern.con "Red" [], Pattern.con "Green" []]) = false := by
  native_decide
example : Pattern.hasUnsupported (Pattern.or_ [Pattern.con "Red" [], Pattern.unsupported]) = true := by
  native_decide

end MarchLean.Syntax.Test
