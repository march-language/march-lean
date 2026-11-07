import MarchLean.EffectGraph
import MarchLean.CapLattice

/-! The executable IO-grant judgment. Non-IO proof/FFI roots are deliberately
outside this check, matching March's entry grant boundary. -/
namespace MarchLean.GrantCheck
open MarchLean.EffectGraph MarchLean.CapLattice

def covered (grants : List String) (cap : String) : Bool :=
  grants.any (fun grant => capSubsumes grant cap)

def uncovered (grants caps : List String) : Option String :=
  caps.find? (fun cap => capSubsumes "IO" cap && !covered grants cap)

def grantCovers (grants caps : List String) : Bool := (uncovered grants caps).isNone

end MarchLean.GrantCheck
