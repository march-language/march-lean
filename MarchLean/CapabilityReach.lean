import MarchLean.CapCheck
import MarchLean.Linearity
import MarchLean.EffectGraph
import MarchLean.GrantCheck

/-!
Independent capability reach for the modeled term fragment. Free references
respect lexical binders; function rows close over references to other functions.
This checks direct builtin needs (1b) and the entry main's IO grant. It does not
reintroduce the removed rule that every Cap-parameter function is a grant point.
Unknown declarations defer this analysis; inference still enforces its own
fragment boundary. No compiler verdict or diagnostics enter this calculation.
-/
namespace MarchLean.CapabilityReach
open MarchLean.Syntax MarchLean.CapCheck

partial def references (bound : List String) : Term → List String
  | .var n _ _ => if bound.contains n then [] else [n]
  | .app f xs _ => references bound f ++ xs.flatMap (references bound)
  | .lam ps body _ => references (ps.map (·.1) ++ bound) body
  | .let_ n _ _ rhs body _ => references bound rhs ++ references (n :: bound) body
  | .letfn n p _ _ rhs body _ =>
      references (p :: n :: bound) rhs ++ references (n :: bound) body
  | .ite c t e _ => [c, t, e].flatMap (references bound)
  | .con _ xs _ | .tuple xs _ => xs.flatMap (references bound)
  | .record fs _ => fs.flatMap (fun (_, t) => references bound t)
  | .field t _ _ _ => references bound t
  | .match_ t arms _ => references bound t ++ arms.flatMap (fun (p, g, b) =>
      let bs := p.boundNames ++ bound
      (g.toList.flatMap (references bs)) ++ references bs b)
  | .opaque_ _ _ | .unsupported _ | .lit _ _ => []

structure Function where
  name : String
  modPrefix : String
  needs : List String
  params : List (String × Lin × Option Ty)
  refs : List String
  signatureCaps : List String

partial def functions (modPrefix : String) (ds : List Decl) : List Function :=
  ds.flatMap fun d => match d with
  | .dfn n ps ret body => [{
      name := modPrefix ++ n, modPrefix, needs := declaredNeeds ds, params := ps,
      refs := references (ps.map (·.1)) body,
      signatureCaps := ps.flatMap (fun p => p.2.2.toList.flatMap capsInTy) ++
        ret.toList.flatMap capsInTy }]
  | .dmod n children => functions (modPrefix ++ n ++ ".") children
  | _ => []

/-- Resolve local declarations before considering a builtin of the same name. -/
def resolve (fs : List Function) (entry modPrefix n : String) : Option String :=
  let candidates := [modPrefix ++ n, n,
    if n.startsWith (entry ++ ".") then n.drop (entry.length + 1) |>.toString else n]
  candidates.find? (fun c => fs.any (fun f => f.name == c))

def directCaps (fs : List Function) (entry : String) (f : Function) : List String :=
  f.refs.flatMap fun n =>
    if (resolve fs entry f.modPrefix n).isSome then []
    else (builtinCaps.find? (fun b => b.1 == n)).toList.map Prod.snd

/-- Public compatibility name for the verified row-closure implementation. -/
abbrev closeRows := MarchLean.EffectGraph.closeRows

/-- Export the finite graph actually consumed by the verified closure. The
extraction/resolution of this graph is a separate trust boundary. -/
def effectGraph (fs : List Function) (entry : String) : MarchLean.EffectGraph.Graph := {
  edges := fs.map fun f =>
    (f.name, f.refs.filterMap (resolve fs entry f.modPrefix)),
  initial := fs.map fun f =>
    (f.name, (directCaps fs entry f ++ f.signatureCaps).eraseDups) }

/-- Grant result with a deterministic call-path diagnostic. General theorems
in Calculus.Grants relate this exact function to finite graph reachability. -/
def checkGrant (g : MarchLean.EffectGraph.Graph) (name : String)
    (grants : List String) : CapResult :=
  let caps := MarchLean.EffectGraph.lookup (MarchLean.EffectGraph.inferReach g) name
  match MarchLean.GrantCheck.uncovered grants caps with
  | none => .ok
  | some cap =>
    let pathDiagnostic := match MarchLean.EffectGraph.findPath g.vertices.length g name cap with
      | some path => s!" (call path: {String.intercalate " → " path})"
      | none => ""  -- unreachable for a reported effect: grant_reject_witness
    .violation s!"{name}'s capability grant does not cover reachable `{cap}`{pathDiagnostic}"

partial def hasUnmodeledDecls (ds : List Decl) : Bool := ds.any fun d =>
  match d with
  | .dmod _ children => hasUnmodeledDecls children
  -- Extern effects, top-level value bindings and imports need richer resolution.
  | .dextern _ _ | .dlet _ _ | .duse _ => true
  | _ => d.hasUnsupported

def check (m : Module) : CapResult := Id.run do
  if hasUnmodeledDecls m.decls then
    return .skip "capability reach requires modeled declarations without imports, externs or top-level values"
  let fs := functions "" m.decls
  -- March's injected prelude has rows for these names. Its current row
  -- accumulation retains those effects even when a user declaration shadows
  -- the function; the export omits the prelude and cannot explain that merge.
  if fs.any (fun f => f.name == "println" || f.name == "print") then
    return .skip "user declaration overlaps an injected console function row"
  for f in fs do
    if let some c := (directCaps fs m.entryName f).find? (fun c => !covered f.needs c) then
      return .violation s!"Check 1b: `{f.name}` references a builtin requiring `{c}`, absent from its module's needs"
  if let some main := fs.find? (fun f => f.name == "main") then
    let grants := main.params.flatMap (fun p => p.2.2.toList.flatMap capsInTy)
    return checkGrant (effectGraph fs m.entryName) "main" grants
  return .ok
end MarchLean.CapabilityReach
