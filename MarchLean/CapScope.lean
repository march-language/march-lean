import MarchLean.CapLattice

/-! Lexical filesystem scope containment, matching `lib/caps/cap_scope.ml`.
This model makes no claims about symlinks, races, or OS sandbox enforcement.
The export format's empty-string sentinel is a decoding convention: `ofPath ""`
is an actual relative empty path, never unbounded authority.
-/
namespace MarchLean.CapScope

inductive Scope where
  | unbounded
  | path (absolute : Bool) (segments : List String)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Normalize lexically, including dropping `..` above a relative root,
as the OCaml implementation does. -/
def Scope.ofPath (raw : String) : Scope :=
  let segments := (raw.splitOn "/").foldl (fun acc segment =>
    if segment == "" || segment == "." then acc
    else if segment == ".." then acc.tail
    else segment :: acc) []
  .path (raw.startsWith "/") segments.reverse

def scopeSubsumes : Scope → Scope → Bool
  | .unbounded, _ => true
  | .path _ _, .unbounded => false
  | .path a xs, .path b ys => a == b && xs.isPrefixOf ys

structure Authority where
  cap : String
  scope : Scope := .unbounded
  deriving BEq, DecidableEq, Repr, Inhabited

def subsumesAuthority (grant requirement : Authority) : Bool :=
  CapLattice.capSubsumes grant.cap requirement.cap &&
    scopeSubsumes grant.scope requirement.scope

def covered (grants : List Authority) (requirement : Authority) : Bool :=
  grants.any (fun grant => subsumesAuthority grant requirement)

-- Native-evaluated conformance pins (separate from general kernel proofs), including the raw/sentinel distinction.
example : scopeSubsumes (Scope.ofPath "/etc") (Scope.ofPath "/etc/a") = true := by native_decide
example : scopeSubsumes (Scope.ofPath "/etc") (Scope.ofPath "/etcpasswd") = false := by native_decide
example : Scope.ofPath "/a/../etc//./" = Scope.ofPath "/etc" := by native_decide
example : Scope.ofPath "../../a/../etc" = Scope.ofPath "etc" := by native_decide
example : scopeSubsumes (Scope.ofPath "/etc") (Scope.ofPath "etc/a") = false := by native_decide
example : scopeSubsumes (Scope.ofPath "") .unbounded = false := by native_decide
example : Scope.ofPath "" = .path false [] := by native_decide
example : Scope.ofPath "/" = .path true [] := by native_decide
example : scopeSubsumes .unbounded (Scope.ofPath "") = true := by native_decide

end MarchLean.CapScope
