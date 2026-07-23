import Lean.Data.Json
import MarchLean.Syntax

/-!
# `MarchLean.Elab`

Decodes march's real `--emit-core-ast` **format_version 2** JSON envelope
into the `MarchLean.Syntax` types (Task 2). The envelope shape (verified
against `march`'s encoder, `lib/dump/ast_json.ml`, and the 8 real samples in
`.superpowers/sdd/samples/*.json` — NOT the task brief's placeholder
snippets, which guessed at some key paths before the real emitter existed):

```
{ "format_version": 2, "verdict": "accept"|"reject", "diagnostics": [...],
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
`PatRecord`/`PatAs` map onto the `Pattern` constructors of the same shape;
`PatAtom` (actor-protocol atom patterns, out of the A1 fragment) → `.unsupported`. -/
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
      -- to a permission argument (`Cap(IO.Network)`), out of the Core+linearity
      -- fragment (A2 models no capability discipline). Decode it to
      -- `Ty.unsupported` so a signature like `fn listen(cap : Cap(IO.Network),
      -- ...)` trips the whole-file skip gate (`Decl.hasUnsupported`) rather than
      -- being mistaken for an ordinary ADT and letting the residual program
      -- falsely accept (reject/t36). The APPLIED test (`args ≠ []`) is load-
      -- bearing: a *nullary* `Cap` is an ordinary user ADT (`type Cap = C(Int)`
      -- in accept/t80), NOT the capability type, and must stay in fragment. A
      -- capability is always `Cap(permission)`; a bare `Cap` never is. -/
      if name == "Cap" && !args.isEmpty then .ok Ty.unsupported
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
any `kind` not handled below (`ECond`/`EPipe`/`EAnnot`/`EHole`/`EAtom`/
`ESend`/`ESpawn`/`EResultRef`/`EDbg`/`ELetFn`/`ELetQ`/`EAssert`/`ESigil` —
none of these appear in the 8 real samples; `Term` has a dedicated `letfn`
constructor for a future `ELetFn` decoder, but since no sample exercises it
this task leaves it on the unsupported fallback rather than guessing at an
undertested currying/sequencing shape). `ELet` is handled only via
`decodeBlockStmts` (inside `EBlock`) — it never reaches this dispatch
directly, since march's grammar only produces `ELet` as one element of an
`EBlock`'s expr list. -/
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
        let guard ← field b "guard"
        if !guard.isNull then
          -- guarded arms aren't representable (`Term.match_`'s arms carry no
          -- guard) — surface as an unsupported arm rather than silently
          -- dropping the guard and risking a false accept.
          pure (Pattern.unsupported, Term.unsupported Ty.unsupported)
        else do
          let p ← decodePattern (← field b "pattern")
          let bodyTerm ← decodeTerm (← field b "body")
          pure (p, bodyTerm))
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
  | _ => .ok (Term.unsupported ty)

/-- Desugar an `EBlock`'s flat expr list into `Term`'s nested-`let_` shape.
An `ELet` element binds its pattern (must be `PatVar`/`PatWild` — anything
else can't be curried into `Term.let_`'s plain-`String` binder, so the whole
block decodes to `Term.unsupported` rather than misrepresenting the
binding) around the recursively-decoded rest of the block. A non-`ELet`
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
        | none => .ok (Term.unsupported blockTy)
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
  | .dfn n _ _ => some n
  | .dlet n _ => some n
  | .dtype n _ _ => some n
  | .dmod _ _ | .dneeds _ | .duse _ | .dextern _ | .unsupported => none

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
fragment; `DMod`/`DNeeds`/`DUse`/`DExtern` are the A3 module-structure and
capability-declaration fragment (Task 2). Every other decl kind (`DActor`,
`DProtocol`, `DSig`, `DInterface`, `DImpl`, `DAlias`, `DProofCap`, `DOpts`,
`DAlwaysLinearType`, `DTransitions`, `DApp`, `DDeriving`, `DSatisfy`, `DTest`,
`DDescribe`, `DSetup`, `DSetupAll`) decodes to `Decl.unsupported`. -/
partial def decodeDecl (j : Json) : Except String Decl := do
  match ← kindOf j with
  | "DFn" => do
      let fn ← field j "fn"
      let (name, _) ← decodeName (← field fn "name")
      -- The declared return-type annotation. A refinement (`{Int | _ >= 0}` →
      -- `TyRefine`), a session channel, or any other out-of-fragment return
      -- type decodes (via `decodeSurfaceTy`) to a type containing
      -- `Ty.unsupported`. The `Decl.dfn`/`Decl.dlet` shapes carry no
      -- return-type field, so we cannot thread it through — instead, a
      -- return type that is out of fragment forces the whole declaration to
      -- `Decl.unsupported`, so the file honestly skips rather than checking
      -- only the (in-fragment) body and ignoring the annotation march
      -- rejected against (reject/t72). A missing or `null` `ret_ty` (an
      -- unannotated `fn`) imposes no such constraint.
      let retUnsupported ← (match fn.getObjVal? "ret_ty" with
        | .ok v => if v.isNull then pure false else do
            let t ← decodeSurfaceTy [] v
            pure t.hasUnsupported
        | .error _ => pure false : Except String Bool)
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
                -- 0-param clause: a plain value binding.
                let body ← decodeTerm bodyJ
                .ok (Decl.dlet name body)
            | some params =>
                -- N-ary: carry the whole param list directly (no currying).
                let body ← decodeTerm bodyJ
                .ok (Decl.dfn name params body)
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
      -- The imported module path lives at `use.path` (a name-object list);
      -- `use.selector` is ignored — Check 4 only needs the module name
      -- (verified shape, samples/t39).
      let useJ ← field j "use"
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
      .ok (Decl.dextern capTy)
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
  .ok { decls, schemes, insts, moduleCaps }

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

-- DUse: module path, ignoring `use.selector`.
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"DUse","use":{"path":[{"txt":"Vault","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}],"selector":{"kind":"UseSingle"}},"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeDecl j))
  -- expect: Except.ok (Decl.duse "Vault")

-- DExtern: cap_ty present, extracting the Cap(X) argument's constructor name.
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"DExtern","extern":{"lib_name":"libc","cap_ty":{"kind":"TyCon","name":{"txt":"Cap","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[{"kind":"TyCon","name":{"txt":"IO.FileSystem","span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}},"args":[]}]},"fns":[]},"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeDecl j))
  -- expect: Except.ok (Decl.dextern (some "IO.FileSystem"))

-- DExtern: cap_ty null (a capability-free extern block) decodes to `none`,
-- not a decode failure.
#eval show IO Unit from do
  let j := Json.parse r#"{"kind":"DExtern","extern":{"lib_name":"libc","cap_ty":null,"fns":[]},"span":{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}}"#
  match j with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => IO.println (repr (decodeDecl j))
  -- expect: Except.ok (Decl.dextern none)

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

end MarchLean.Elab.Test
