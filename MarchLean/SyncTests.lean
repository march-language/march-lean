import MarchLean.Elab
import MarchLean.CapCheck
import MarchLean.CapabilityReach

open MarchLean MarchLean.Syntax

-- March now inspects capabilities inside Tagged payloads.
example : CapCheck.capsInTy (.con "Tagged" [.con "Cap" [.con "IO.Console" []],
    .con "Realtime" []]) = ["IO.Console"] := by native_decide

namespace MarchLean.SyncTests
private def unit := Ty.con "Unit" []
private def call (name : String) := Term.app (.var name ⟨"", 0, 0, 0, 0⟩ unit) [] unit
private def cap (name : String) := Ty.con "Cap" [.con name []]
private def grantModule (grants : List String) : Module := {
  decls := [.dneeds ["IO.Console", "IO.Clock"],
    .dfn "helper" [] none (call "println"),
    .dfn "main" (grants.map (fun c => ("_cap", Lin.unrestricted, some (cap c)))) none (call "helper")],
  schemes := [], insts := [], moduleCaps := [] }
example : (CapabilityReach.check (grantModule [])).isViolation = true := by native_decide
example : (CapabilityReach.check (grantModule ["IO.Clock"])).isViolation = true := by native_decide
example : (CapabilityReach.check (grantModule ["IO.Console"])).isViolation = false := by native_decide
example : (CapabilityReach.check (grantModule ["IO"])).isViolation = false := by native_decide
-- Module-level shadowing must not turn a user function into an IO builtin.
example : (CapabilityReach.check { (grantModule []) with
    decls := [.dfn "println" [] none (.lit .unit unit),
              .dfn "main" [] none (call "println")] }).isViolation = false := by native_decide
-- Check 1b applies even in a library with no main.
example : (CapabilityReach.check { (grantModule []) with
    decls := [.dfn "f" [] none (call "println")] }).isViolation = true := by native_decide
end MarchLean.SyncTests

namespace MarchLean.SyncTests
private def res := Ty.con "Res" []
private def moved (consume : Bool) : Module := {
  decls := [.dfn "f" [("h", .linear, some res)] none
    (.let_ "h2" .unrestricted none (.var "h" ⟨"",0,0,0,0⟩ res)
      (if consume then .var "h2" ⟨"",0,0,0,0⟩ res else .lit (.int 0) (.con "Int" [])) res)],
  schemes := [], insts := [], moduleCaps := [] }
example : (match Linearity.checkLinearity (moved false) with
    | .reject _ => true | _ => false) = true := by native_decide
example : (match Linearity.checkLinearity (moved true) with
    | .ok => true | _ => false) = true := by native_decide
end MarchLean.SyncTests

-- A module-wide manifest is an upper bound, not evidence that an import uses IO.
example : (CapCheck.checkCaps CapCheck.useUncovered).isViolation = false := by native_decide

-- Explicit affine is an intentional weakening, not an implicit move qualifier.
example : (match Linearity.checkLinearity {
    decls := [.dfn "f" [("h", .linear, some (.con "Int" []))] none
      (.let_ "a" .affine none (.var "h" ⟨"",0,0,0,0⟩ (.con "Int" []))
        (.lit (.int 0) (.con "Int" [])) (.con "Int" []))],
    schemes := [], insts := [], moduleCaps := [] } with
    | .ok => true | _ => false) = true := by native_decide
