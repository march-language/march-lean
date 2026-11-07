import MarchLean.Calculus.Grants
import MarchLean.Calculus.Scopes
import Lean.Util.CollectAxioms

/-! Fail if a public capability theorem gains an extra trust assumption.
Finite native regression examples are deliberately outside this audit. -/
open Lean in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations : Array Name := #[
    ``MarchLean.Calculus.Reachability.inferReach_iff,
    ``MarchLean.Calculus.Reachability.fuel_adequate,
    ``MarchLean.Calculus.Reachability.inferReach_least,
    ``MarchLean.Calculus.Reachability.inferReach_fixed,
    ``MarchLean.Calculus.Reachability.inferReach_witness,
    ``MarchLean.Calculus.Grants.grant_accept_iff,
    ``MarchLean.Calculus.Grants.grant_mono,
    ``MarchLean.Calculus.Grants.checkGrant_ok_iff,
    ``MarchLean.Calculus.Grants.executable_bridge,
    ``MarchLean.Calculus.Grants.grant_reject_witness,
    ``MarchLean.Calculus.Concrete.normalize_nodup,
    ``MarchLean.Calculus.Concrete.normalize_sublist,
    ``MarchLean.Calculus.Concrete.normalize_covered,
    ``MarchLean.Calculus.Concrete.normalize_idem,
    ``MarchLean.Calculus.Scopes.scopeSubsumes_refl,
    ``MarchLean.Calculus.Scopes.scopeSubsumes_trans,
    ``MarchLean.Calculus.Scopes.scopeSubsumes_antisymm,
    ``MarchLean.Calculus.Scopes.subsumesAuthority_refl,
    ``MarchLean.Calculus.Scopes.subsumesAuthority_trans,
    ``MarchLean.Calculus.Scopes.subsumesAuthority_antisymm,
    ``MarchLean.Calculus.Scopes.covered_iff,
    ``MarchLean.Calculus.Scopes.covered_mono]
  for declaration in declarations do
    for dependency in (← collectAxioms declaration) do
      unless allowed.contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
  logInfo m!"Audited {declarations.size} capability theorems: only standard Lean axioms."
