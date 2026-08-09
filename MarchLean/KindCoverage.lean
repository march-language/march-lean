import Lean.Data.Json
import MarchLean.Elab

/-!
# `MarchLean.KindCoverage`

**Self-interrogation of `MarchLean.Elab`'s `"kind"` dispatch.** Answers, for
an arbitrary `kind` string, the question `scripts/decoder-coverage.sh` needs:

> if march emits a node tagged `"kind":"K"`, what does this decoder actually
> do with it?

This module exists because the two worst defects in this project were the
same mechanical oversight — march emits a node kind, `Elab.decodeTerm` has
no arm for it, and the node silently degrades:

- **`ELet`** had no arm, so a `do` block whose sole statement is a `let`
  DISCARDED the binding's right-hand side, blinding all four `CapCheck`
  capability walks at once.
- **`EAnnot`** had no arm, and `Desugar` synthesizes one for every `app`
  block (`desugar.ml:929`), so a `cap` violation inside an `app` body was
  invisible.

Both were rationalised away by reasoning from march's *grammar* ("no parser
production reaches this kind"). That reasoning is unsound: `Desugar` sits
between the parser and the emitter and manufactures nodes with no surface
syntax. The only sound test is to compare *what the corpus actually emits*
against *what this decoder actually does* — which is what this module makes
mechanically checkable.

## Why probing, and not a declared table

The obvious implementation is a hand-written `handledKinds : List String`
next to the decoder, printed on demand. It does not work, and the reason is
worth stating: deleting the `"ELet"` arm from `decodeTerm` would not change
such a table, so the coverage check would keep passing while the exact
historical bug was reintroduced. A parallel declaration can only ever
restate the author's belief about the code.

So this module instead **runs the real decoder** on a synthetic node bearing
the kind under test, and classifies what comes back. The answer is derived
from the live match arms, so it cannot drift from them; removing an arm
changes the answer immediately.

## Classification

Each *dispatch site* (one `kindOf`-driven `match` in `Elab.lean`) is probed
twice: once with the kind under test, and once with `sentinelKind`, a string
march can never emit. Comparing the two renderings separates "this kind has
its own arm" from "this kind is indistinguishable from a kind that does not
exist".

| `Category`     | meaning                                                           |
|----------------|-------------------------------------------------------------------|
| `modeled`      | an arm exists and yields a real modelled constructor               |
| `opaque_`      | an arm exists and yields `Term.opaque_` — shape unmodelled, but the child expressions survive for the `CapCheck` walks |
| `unsupported`  | an arm exists and yields an `.unsupported` sentinel — children discarded |
| `fellThrough`  | no arm: the decoder cannot tell this kind from one that does not exist |
| `probeError`   | an arm exists but demanded a field this module's fixture does not supply — the fixture is stale, fix it here |

`opaque_`, `unsupported` and `fellThrough` are all *degraded* outcomes, and
`scripts/decoder-coverage.sh` requires every one of them to be declared in
`scripts/decoder-degraded-kinds.txt` with its category. Keeping the three
distinct is what makes the `EAnnot` regression catchable: dropping that arm
moves `EAnnot` from `opaque_` to `fellThrough`, and the declared category no
longer matches. Collapsing them into one "degraded" bucket would let that
deletion pass unnoticed.

`probeError` cannot be reached by a kind with no arm — the catch-all of every
site returns `.ok` — so it always means "a new arm appeared and this file
needs a new fixture field". The script treats it as a hard failure.

## Namespaces

march tags nodes at several levels (expressions, declarations, patterns,
resolved types, surface types, literals, ...) and this module probes every
one of them, reporting which site(s) recognised the kind. A kind recognised
at *more than one* site would mean the tag namespaces genuinely overlap and
a bare kind string is not enough to identify a node; the script fails on
that too. Today no march tag is reused across namespaces (they are prefixed
`E`/`D`/`Pat`/`Lit`/`Ty`/`T`/`TD`/`C`/`FP`/`Nat`/`Use`), and the ambiguity
check is what keeps that from being an assumption.

## Fixtures

Each site supplies a JSON object carrying *every* field any of its arms
reads, so that an arm which exists always gets far enough to produce a
value rather than a missing-field error. Where one object cannot satisfy
every arm (`decodeLit`'s `value` is an int, a string or a bool depending on
the literal kind) the site lists several fixtures and the best result wins.
-/

namespace MarchLean.KindCoverage

open Lean (Json)
open MarchLean.Syntax
open MarchLean.Elab

/-- A `kind` string march's emitter can never produce. Probing a site with
this is how "has its own arm" is told apart from "reached the catch-all". -/
def sentinelKind : String := "__march_lean_no_such_kind__"

/-- What a dispatch site does with a given `kind`. See the module docstring
for the full contract; `rank` orders them so that the most informative
outcome across several fixtures / several sites wins. -/
inductive Category where
  /-- An arm exists and produces a real modelled constructor. -/
  | modeled
  /-- An arm exists and produces `Term.opaque_`: children survive. -/
  | opaque_
  /-- An arm exists and produces an `.unsupported` sentinel: children lost. -/
  | unsupported
  /-- An arm exists but the fixture below is missing a field it reads. -/
  | probeError
  /-- No arm: indistinguishable from a kind that does not exist. -/
  | fellThrough
  deriving Repr, Inhabited

def Category.name : Category → String
  | .modeled => "modeled"
  | .opaque_ => "opaque"
  | .unsupported => "unsupported"
  | .probeError => "probe-error"
  | .fellThrough => "fell-through"

/-- Strict total order used to pick the best of several probe results.
Distinct for every constructor, so `rank` equality is also equality. -/
def Category.rank : Category → Nat
  | .modeled => 4
  | .opaque_ => 3
  | .unsupported => 2
  | .probeError => 1
  | .fellThrough => 0

/-- One probe's result: a canonical rendering (compared against the
sentinel's rendering to detect a catch-all) plus the shape category the
decoded value falls into. -/
structure Outcome where
  render : String
  cat : Category
  deriving Inhabited

/-- Wrap a decoder result. A decode *error* means an arm existed and read a
field the fixture lacks — never a catch-all, which always returns `.ok`. -/
def outcome [Repr α] (shape : α → Category) : Except String α → Outcome
  | .error e => { render := "<decode error: " ++ e ++ ">", cat := .probeError }
  | .ok v => { render := toString (repr v), cat := shape v }

/-- Parse a fixture and run one decoder over it. -/
def probe [Repr α] (shape : α → Category) (dec : Json → Except String α) (src : String) : Outcome :=
  match Json.parse src with
  | .error e => { render := "<fixture is not valid JSON: " ++ e ++ ">", cat := .probeError }
  | .ok j => outcome shape (dec j)

/-! ### Shape classifiers

One per decoded type. `Term` is the only type with an `opaque_` constructor;
everywhere else the degraded outcome is the type's own `.unsupported` (or
`none`, for the two decoders returning `Option`). -/

def tyShape : Ty → Category
  | .unsupported => .unsupported
  | _ => .modeled

def termShape : Term → Category
  | .unsupported _ => .unsupported
  | .opaque_ _ _ => .opaque_
  | _ => .modeled

def patternShape : Pattern → Category
  | .unsupported => .unsupported
  | _ => .modeled

def declShape : Decl → Category
  | .unsupported => .unsupported
  | _ => .modeled

def constraintShape : Constraint → Category
  | .unsupported => .unsupported
  | _ => .modeled

/-- `Lin` has no "unsupported" constructor: `decodeLin`'s catch-all *defaults*
to `unrestricted`. The sentinel comparison, not this function, is what
detects that fall-through. -/
def linShape : Lin → Category := fun _ => .modeled

/-- `decodeLit` and `decodeFnParam` signal "out of fragment" with `none`. -/
def optShape {α : Type} : Option α → Category
  | none => .unsupported
  | some _ => .modeled

/-! ### Fixture fragments

Small, valid, in-fragment JSON nodes the site fixtures below are assembled
from. Built with `++` rather than `s!` interpolation: these strings are
dense in literal `{`/`}`, which `s!` would try to read as splices. -/

private def spanJ : String :=
  "{\"file\":\"f\",\"start_line\":1,\"start_col\":1,\"end_line\":1,\"end_col\":2}"

/-- A `name` node. The text is `"a"` so that the `surface_ty` site's `TyVar`
arm resolves against its `paramNames` list (also `["a"]`) instead of
degrading to `Ty.unsupported`, which would make a real arm look like a
fall-through. -/
private def nameJ : String := "{\"txt\":\"a\",\"span\":" ++ spanJ ++ "}"

/-- A resolved (`T.ty`) type node. -/
private def rtyJ : String := "{\"kind\":\"TCon\",\"name\":\"Int\",\"args\":[]}"

/-- A surface (`ty`) type node. -/
private def styJ : String := "{\"kind\":\"TyCon\",\"name\":" ++ nameJ ++ ",\"args\":[]}"

private def litJ : String := "{\"kind\":\"LitInt\",\"value\":0}"

/-- An in-fragment expression node, used for every child-expression slot. -/
private def exprJ : String :=
  "{\"kind\":\"ELit\",\"literal\":" ++ litJ ++ ",\"resolved_ty\":" ++ rtyJ ++ "}"

/-- A `PatVar` pattern: the one shape both `decodeTerm`'s `ELet` arm and
`decodeDecl`'s `DLet` arm accept without degrading. -/
private def patVarJ : String := "{\"kind\":\"PatVar\",\"name\":" ++ nameJ ++ "}"

private def linJ : String := "{\"kind\":\"Unrestricted\"}"

private def bindingJ : String :=
  "{\"pattern\":" ++ patVarJ ++ ",\"lin\":" ++ linJ ++ ",\"ty\":null,\"expr\":" ++ exprJ ++ "}"

private def fnJ : String :=
  "{\"name\":" ++ nameJ ++ ",\"ret_ty\":null,\"bounds\":[],\"clauses\":[{\"guard\":null,\"params\":[],\"body\":"
    ++ exprJ ++ "}]}"

private def externJ : String := "{\"lib_name\":\"l\",\"cap_ty\":null,\"fns\":[]}"

/-! ### Dispatch sites

One entry per `kindOf`-driven `match` in `Elab.lean`. Adding a dispatch
there without adding a site here would leave that namespace unchecked, so
the list is deliberately exhaustive and ordered to mirror the file. -/

/-- A `kind`-dispatching `match` in `Elab.lean`, plus the fixtures needed to
reach every one of its arms. -/
structure Site where
  name : String
  probes : List (String → Outcome)

/-- `decodeTy` — resolved (`T.ty`) type tags. -/
private def resolvedTySite : Site :=
  { name := "resolved_ty"
    probes := [fun k =>
      probe tyShape decodeTy <|
        "{\"kind\":\"" ++ k ++ "\",\"name\":\"Int\",\"args\":[],\"from\":" ++ rtyJ
          ++ ",\"to\":" ++ rtyJ ++ ",\"elems\":[],\"fields\":[],\"id\":0,\"lin\":\"unrestricted\",\"ty\":"
          ++ rtyJ ++ ",\"n\":0,\"op\":\"add\",\"a\":" ++ rtyJ ++ ",\"b\":" ++ rtyJ ++ "}"] }

/-- `decodeSurfaceTy` — surface (`ty`) type tags. `paramNames` is `["a"]` so
the `TyVar` arm can resolve `nameJ` positionally. -/
private def surfaceTySite : Site :=
  { name := "surface_ty"
    probes := [fun k =>
      probe tyShape (decodeSurfaceTy ["a"]) <|
        "{\"kind\":\"" ++ k ++ "\",\"name\":" ++ nameJ ++ ",\"args\":[],\"from\":" ++ styJ
          ++ ",\"to\":" ++ styJ ++ ",\"elements\":[],\"fields\":[],\"lin\":" ++ linJ ++ ",\"ty\":"
          ++ styJ ++ ",\"value\":0,\"op\":{\"kind\":\"NatAdd\"},\"lhs\":" ++ styJ ++ ",\"rhs\":"
          ++ styJ ++ "}"] }

/-- The `op` tag nested in a surface `TyNatOp`. `decodeSurfaceTy` reads it as
`if opKind == "NatAdd" then "add" else "mul"`, so `NatMul` is a genuine
fall-through and the sentinel comparison reports it as one. -/
private def natOpSite : Site :=
  { name := "nat_op"
    probes := [fun k =>
      probe tyShape (decodeSurfaceTy ["a"]) <|
        "{\"kind\":\"TyNatOp\",\"op\":{\"kind\":\"" ++ k ++ "\"},\"lhs\":" ++ styJ ++ ",\"rhs\":"
          ++ styJ ++ "}"] }

/-- `decodeLin` — surface linearity tags. Its catch-all *defaults* to
`unrestricted` rather than flagging anything, so `Unrestricted` itself is a
fall-through here. That is not a bug to fix in `Elab.lean` but a fact to
declare: a hypothetical fourth linearity would be silently read as
`unrestricted`. -/
private def linSite : Site :=
  { name := "lin"
    probes := [fun k => probe linShape decodeLin ("{\"kind\":\"" ++ k ++ "\"}")] }

/-- `decodeLit`. Three fixtures, because `value` is an int, a string or a
bool depending on the literal kind and no single object satisfies all
three. -/
private def literalSite : Site :=
  { name := "literal"
    probes :=
      [ fun k => probe optShape decodeLit ("{\"kind\":\"" ++ k ++ "\",\"value\":0}")
      , fun k => probe optShape decodeLit ("{\"kind\":\"" ++ k ++ "\",\"value\":\"s\"}")
      , fun k => probe optShape decodeLit ("{\"kind\":\"" ++ k ++ "\",\"value\":true}") ] }

/-- `decodePattern`. -/
private def patternSite : Site :=
  { name := "pattern"
    probes := [fun k =>
      probe patternShape decodePattern <|
        "{\"kind\":\"" ++ k ++ "\",\"name\":" ++ nameJ ++ ",\"args\":[],\"elements\":[],\"literal\":"
          ++ litJ ++ ",\"fields\":[],\"pattern\":{\"kind\":\"PatWild\"},\"patterns\":[]}"] }

/-- `decodeTerm` — the expression tags, and the site both historical defects
lived at. `exprs` holds one element (not zero) because an empty `EBlock`
decodes to `Term.unsupported`, which is exactly the catch-all's answer and
would make the `EBlock` arm read as a fall-through. -/
private def exprSite : Site :=
  { name := "expr"
    probes := [fun k =>
      probe termShape decodeTerm <|
        "{\"kind\":\"" ++ k ++ "\",\"resolved_ty\":" ++ rtyJ ++ ",\"literal\":" ++ litJ
          ++ ",\"name\":" ++ nameJ ++ ",\"fn\":" ++ exprJ ++ ",\"args\":[],\"params\":[],\"body\":"
          ++ exprJ ++ ",\"exprs\":[" ++ exprJ ++ "],\"scrutinee\":" ++ exprJ
          ++ ",\"branches\":[],\"elements\":[],\"fields\":[],\"target\":" ++ exprJ ++ ",\"field\":"
          ++ nameJ ++ ",\"cond\":" ++ exprJ ++ ",\"then_\":" ++ exprJ ++ ",\"else_\":" ++ exprJ
          ++ ",\"arms\":[],\"base\":" ++ exprJ ++ ",\"expr\":" ++ exprJ ++ ",\"value\":" ++ exprJ
          ++ ",\"cont\":" ++ exprJ ++ ",\"cap\":" ++ exprJ ++ ",\"msg\":" ++ exprJ ++ ",\"actor\":"
          ++ exprJ ++ ",\"binding\":" ++ bindingJ ++ "}"] }

/-- `decodeFnParam` — the `fn_param` wrapper tags. -/
private def fnParamSite : Site :=
  { name := "fn_param"
    probes := [fun k =>
      probe optShape decodeFnParam <|
        "{\"kind\":\"" ++ k ++ "\",\"param\":{\"name\":" ++ nameJ ++ ",\"lin\":" ++ linJ
          ++ ",\"ty\":null}}"] }

/-- `decodeDecl` — the top-level declaration tags. -/
private def declSite : Site :=
  { name := "decl"
    probes := [fun k =>
      probe declShape decodeDecl <|
        "{\"kind\":\"" ++ k ++ "\",\"fn\":" ++ fnJ ++ ",\"binding\":" ++ bindingJ ++ ",\"name\":"
          ++ nameJ ++ ",\"params\":[],\"def\":{\"kind\":\"TDVariant\",\"variants\":[]},\"decls\":[]"
          ++ ",\"paths\":[],\"use\":{\"path\":[" ++ nameJ
          ++ "],\"selector\":{\"kind\":\"UseSingle\"}},\"extern\":" ++ externJ ++ ",\"opts\":[]}"] }

/-- The `def` tag nested in a `DType` (`TDVariant` / `TDAlias` / `TDRecord`),
dispatched inside `decodeDecl`'s `DType` arm. -/
private def typeDefSite : Site :=
  { name := "type_def"
    probes := [fun k =>
      probe declShape decodeDecl <|
        "{\"kind\":\"DType\",\"name\":" ++ nameJ ++ ",\"params\":[],\"def\":{\"kind\":\"" ++ k
          ++ "\",\"variants\":[]}}"] }

/-- The `use.selector` tag, dispatched inside `decodeDecl`'s `DUse` arm.
Only `UseNames` has an arm; every other selector *defaults* to the plain
whole-module import, so `UseSingle` reads as a fall-through. -/
private def useSelectorSite : Site :=
  { name := "use_selector"
    probes := [fun k =>
      probe declShape decodeDecl <|
        "{\"kind\":\"DUse\",\"use\":{\"path\":[" ++ nameJ ++ "],\"selector\":{\"kind\":\"" ++ k
          ++ "\"}}}"] }

/-- `decodeConstraint` — scheme-constraint tags. -/
private def constraintSite : Site :=
  { name := "constraint"
    probes := [fun k =>
      probe constraintShape decodeConstraint <|
        "{\"kind\":\"" ++ k ++ "\",\"ty\":" ++ rtyJ ++ ",\"name\":\"a\"}"] }

/-- Every `kind`-dispatching `match` in `Elab.lean`. -/
def sites : List Site :=
  [ resolvedTySite, surfaceTySite, natOpSite, linSite, literalSite, patternSite,
    exprSite, fnParamSite, declSite, typeDefSite, useSelectorSite, constraintSite ]

/-- Probe one site with one kind. `probeError` is reported as-is (a stale
fixture must be loud); otherwise a rendering identical to the sentinel's
means the kind reached the site's catch-all. Best fixture wins. -/
def siteCategory (s : Site) (k : String) : Category :=
  s.probes.foldl (init := Category.fellThrough) fun best p =>
    let o := p k
    let baseline := p sentinelKind
    let c : Category :=
      match o.cat with
      | .probeError => .probeError
      | _ => if o.render == baseline.render then .fellThrough else o.cat
    if c.rank > best.rank then c else best

/-- What every site does with one kind. -/
structure KindReport where
  kind : String
  /-- Best category across all sites. -/
  cat : Category
  /-- Sites that recognised the kind (category other than `fellThrough`).
  More than one means the tag namespaces overlap — see the module doc. -/
  sites : List String

def classify (k : String) : KindReport :=
  let per := sites.map (fun s => (s.name, siteCategory s k))
  let recognised := per.filter (fun (_, c) => c.rank > Category.fellThrough.rank)
  let best := per.foldl (fun b (_, c) => if c.rank > b.rank then c else b) Category.fellThrough
  { kind := k, cat := best, sites := recognised.map (·.1) }

/-- One TSV line per kind: `KIND<TAB>CATEGORY<TAB>SITES`, where `SITES` is a
comma-separated list of the sites that recognised the kind, or `-` for none.
This is the whole interface `scripts/decoder-coverage.sh` consumes. -/
def report (kinds : List String) : String :=
  String.intercalate "\n" <| kinds.map fun k =>
    let r := classify k
    k ++ "\t" ++ r.cat.name ++ "\t" ++ (if r.sites.isEmpty then "-" else String.intercalate "," r.sites)

end MarchLean.KindCoverage

-- Living sanity checks (executable documentation, matching the convention in
-- `MarchLean/Json.lean` and `MarchLean/Elab.lean`). These pin the classifier
-- against the two historical defects and against one representative of every
-- category, so a change that made every kind look `modeled` — the vacuous-pass
-- failure mode this whole module exists to prevent — breaks the build.
namespace MarchLean.KindCoverage.Test
open MarchLean.KindCoverage

#eval show IO Unit from do
  IO.println (report ["ELet", "EAnnot", "ETuple", "ECond", "DActor", "UseNames",
                      "Unrestricted", "NatMul", "TCon", "TyCon", "PatVar", "LitString"])
  -- expect:
  --   ELet         modeled       expr
  --   EAnnot       opaque        expr
  --   ETuple       modeled       expr
  --   ECond        opaque        expr
  --   DActor       fell-through  -
  --   UseNames     unsupported   use_selector
  --   Unrestricted fell-through  -
  --   NatMul       fell-through  -
  --   TCon         modeled       resolved_ty
  --   TyCon        modeled       surface_ty
  --   PatVar       modeled       pattern
  --   LitString    modeled       literal

/-- The `ELet` regression, enforced at build time: `decodeTerm`'s `ELet` arm
must produce a real `Term.let_`. With the arm deleted the kind falls to
`| _ => Term.unsupported`, the classifier reports `fellThrough`, and this
fails to compile. -/
example : (classify "ELet").cat.rank = Category.modeled.rank := by native_decide

/-- The `EAnnot` regression. `EAnnot` is *deliberately* `opaque_` — the child
expression survives for the `CapCheck` walks even though the ascription's
typing rule is unmodelled. Pinning the exact category (not merely
"recognised") is what makes deleting the arm detectable: it would drop to
`fellThrough`. -/
example : (classify "EAnnot").cat.rank = Category.opaque_.rank := by native_decide

/-- A kind march emits and this decoder deliberately does not model at all. -/
example : (classify "DActor").cat.rank = Category.fellThrough.rank := by native_decide

/-- No march tag is recognised at two dispatch sites at once; the coverage
script relies on a bare kind string identifying one namespace. -/
example : ((classify "ELet").sites.length ≤ 1) = true := by native_decide

end MarchLean.KindCoverage.Test
