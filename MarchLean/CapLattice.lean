/-!
# The IO capability lattice

A faithful port of march's `lib/caps/cap_lattice.ml:17-60`, which is the single
source of truth shared by `March_typecheck.Typecheck` and
`March_refinecheck.Cap_infer`.

**The table has 20 entries.** `core-march-types.md` §2.8.1 says "18 entries" in
three places and `lang/capabilities.md`'s tree omits two; both are stale. The
entries the docs miss are `IO.Signal` and `IO.WebSocket`. Modelling 18 would
give wrong subsumption for those two, so this port is taken from the OCaml
source, not the prose.
-/
namespace MarchLean.CapLattice

/-- The capability hierarchy: `(cap_path, parent_path)`. Mirrors
`cap_lattice.ml`'s `hierarchy` list exactly, including order. -/
def hierarchy : List (String × Option String) :=
  [ ("IO",                  none),
    ("IO.Console",          some "IO"),
    ("IO.FileSystem",       some "IO"),
    ("IO.FileRead",         some "IO.FileSystem"),
    ("IO.FileWrite",        some "IO.FileSystem"),
    ("IO.Network",          some "IO"),
    ("IO.NetConnect",       some "IO.Network"),
    ("IO.NetListen",        some "IO.Network"),
    ("IO.Process",          some "IO"),
    ("IO.Clock",            some "IO"),
    ("IO.Random",           some "IO"),
    ("IO.Signal",           some "IO"),
    ("IO.Database",         some "IO.NetConnect"),
    ("IO.Spawn",            some "IO"),
    ("IO.Mut",              some "IO"),
    ("IO.Telemetry",        some "IO"),
    ("IO.NetConnect.TLS",   some "IO.NetConnect"),
    ("IO.WebSocket",        some "IO.NetConnect"),
    ("IO.Foreign",          some "IO"),
    ("IO.Foreign.Blocking", some "IO.Foreign") ]

/-- The parent of a capability, or `none` for a root or an unknown (FFI) name. -/
def capParent (c : String) : Option String :=
  match hierarchy.find? (fun (n, _) => n == c) with
  | some (_, p) => p
  | none        => none

/-- `capAncestors c` is `c` followed by every ancestor up to the root,
most-specific first: `capAncestors "IO.FileRead" = ["IO.FileRead",
"IO.FileSystem", "IO"]`.

A name **absent from the table returns just itself** — this is the FFI-cap
base case (`cap_lattice.ml`'s `| _ -> acc'` arm) and is load-bearing: FFI caps
like `LibC` are their own roots with no subtyping relationship to anything.

`fuel` is the recursion bound. `hierarchy.length` is a safe bound because the
table is a finite forest with no cycles, so no chain can exceed its size; the
parameter exists only to make the function structurally terminating. -/
def capAncestorsFuel : Nat → String → List String
  | 0,        c => [c]
  | fuel + 1, c =>
      match capParent c with
      | some p => c :: capAncestorsFuel fuel p
      | none   => [c]

def capAncestors (c : String) : List String :=
  capAncestorsFuel hierarchy.length c

/-- `capSubsumes parent child` — is `parent` an ancestor of, or equal to,
`child`? **Reflexive** (`capAncestors X` always starts with `X`) and
**directional** (a broader declared cap covers a narrower used one, never the
reverse). Two siblings never subsume each other. -/
def capSubsumes (parent child : String) : Bool :=
  (capAncestors child).contains parent

/-- Drop any cap subsumed by another cap already present, preserving the
relative order of the survivors: `normalize ["IO", "IO.FileRead"] = ["IO"]`
regardless of the order they were given in. -/
def normalize (caps : List String) : List String :=
  caps.filter (fun c => !caps.any (fun other => other != c && capSubsumes other c))

end MarchLean.CapLattice

namespace MarchLean.CapLattice

-- reflexivity
#eval (capSubsumes "IO" "IO" : Bool)                        -- expect true
-- root covers a child (accept/t46)
#eval (capSubsumes "IO" "IO.Network" : Bool)                -- expect true
-- mid-tier covers a deeper descendant (accept/t48)
#eval (capSubsumes "IO.Network" "IO.NetConnect" : Bool)     -- expect true
-- directional: a child does NOT grant its parent (reject/t37)
#eval (capSubsumes "IO.FileRead" "IO" : Bool)               -- expect false
-- siblings never cover each other (reject/t38)
#eval (capSubsumes "IO.FileRead" "IO.FileWrite" : Bool)     -- expect false
#eval (capSubsumes "IO.FileWrite" "IO.FileRead" : Bool)     -- expect false
-- the two entries the prose docs omit
#eval (capSubsumes "IO" "IO.Signal" : Bool)                 -- expect true
#eval (capSubsumes "IO.NetConnect" "IO.WebSocket" : Bool)   -- expect true
-- FFI caps: absent from the table, so they are their own root and
-- subsume nothing but themselves (cap_lattice.ml's `| _ -> acc'` arm)
#eval (capSubsumes "LibC" "LibC" : Bool)                    -- expect true
#eval (capSubsumes "IO" "LibC" : Bool)                      -- expect false
#eval (capAncestors "LibC")                                 -- expect ["LibC"]
-- ancestor chain order: most-specific first
#eval (capAncestors "IO.FileRead")   -- expect ["IO.FileRead", "IO.FileSystem", "IO"]
-- normalize: the broader cap absorbs the narrower, either order
#eval (normalize ["IO", "IO.FileRead"])   -- expect ["IO"]
#eval (normalize ["IO.FileRead", "IO"])   -- expect ["IO"]
-- normalize keeps genuinely independent siblings
#eval (normalize ["IO.FileRead", "IO.FileWrite"])
  -- expect ["IO.FileRead", "IO.FileWrite"]

end MarchLean.CapLattice
