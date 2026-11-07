import MarchLean.EffectGraph
import MarchLean.GrantCheck
import MarchLean.CapabilityReach

/-! Finite regression guards, separate from the general kernel proofs. -/
namespace MarchLean.EffectGraphTests
open MarchLean.EffectGraph MarchLean.GrantCheck

def chain : Graph := {
  edges := [("main", ["a"]), ("a", ["b"]), ("b", ["end"])],
  initial := [("main", []), ("a", []), ("b", []), ("end", ["IO.Console"])] }

-- Four vertices require three edge-propagation rounds. This is the mutation target.
example : lookup (closeRows 3 chain.edges chain.initial) "main" = ["IO.Console"] := by decide
example : lookup (closeRows 2 chain.edges chain.initial) "main" = [] := by decide
example : lookup (inferReach chain) "main" = ["IO.Console"] := by decide
example : findPath chain.vertices.length chain "main" "IO.Console" =
    some ["main", "a", "b", "end"] := by decide

def cycle : Graph := {
  edges := [("main", ["a"]), ("a", ["b"]), ("b", ["a"])],
  initial := [("main", []), ("a", []), ("b", ["IO.Clock"])] }
example : lookup (inferReach cycle) "main" = ["IO.Clock"] := by decide
example : findPath cycle.vertices.length cycle "main" "IO.Clock" =
    some ["main", "a", "b"] := by decide
example : findPath cycle.vertices.length cycle "main" "IO.Console" = none := by decide

def diamond : Graph := {
  edges := [("main", ["left", "right"]), ("left", ["end"]), ("right", ["end"])],
  initial := [("main", []), ("left", []), ("right", []), ("end", ["IO.Console"])] }
example : lookup (inferReach diamond) "main" = ["IO.Console"] := by decide
-- Diagnostic tie-breaking is deterministic, but is not part of set semantics.
example : findPath diamond.vertices.length diamond "main" "IO.Console" =
    some ["main", "left", "end"] := by decide

def disconnected : Graph := {
  edges := [("main", ["missing"])],
  initial := [("main", []), ("unreachable", ["IO.Console"])] }
example : lookup (inferReach disconnected) "main" = [] := by decide
example : lookup (inferReach disconnected) "missing" = [] := by decide
example : inferReach { edges := [("ghost", ["ghost"])], initial := [] } = [] := by decide
-- First-match lookup is explicit even for malformed duplicate-key tables.
example : lookup (inferReach { edges := [], initial := [("f", []), ("f", ["IO.Console"])] }) "f" = [] := by decide
example : grantCovers [] [] = true := by decide
example : grantCovers ["IO"] ["IO.Console", "IO.Clock"] = true := by decide
example : grantCovers ["IO.Clock"] ["IO.Console"] = false := by decide
example : grantCovers ["IO.Console", "IO.Clock"] ["IO.Console", "IO.Clock"] = true := by decide
example : grantCovers [] ["Proof.Checked"] = true := by decide
example : uncovered [] ["IO.Clock", "IO.Console"] = some "IO.Clock" := by decide

open MarchLean.Syntax MarchLean.CapabilityReach
private def ref (n : String) : Term := Term.var n ⟨"", 0, 0, 0, 0⟩ (.con "Unit" [])
-- References in closure bodies are charged at creation in the modeled analysis.
example : references [] (.lam [] (ref "println") (.con "Unit" [])) = ["println"] := by native_decide
-- A lambda binder or local let shadows the same-named global builtin.
example : references [] (.lam [("println", .unrestricted, none)] (ref "println") (.con "Unit" [])) = [] := by native_decide
example : references [] (.let_ "println" .unrestricted none
    (.lit .unit (.con "Unit" [])) (ref "println") (.con "Unit" [])) = [] := by native_decide

end MarchLean.EffectGraphTests

namespace MarchLean.EffectGraphTests
open MarchLean.EffectGraph
-- Store each preceding round once, newest first, for linear-depth diagnostics.
example : history 4 chain.edges chain.initial =
    [rounds 3 chain.edges chain.initial, rounds 2 chain.edges chain.initial,
     rounds 1 chain.edges chain.initial, chain.initial] := by decide
end MarchLean.EffectGraphTests
