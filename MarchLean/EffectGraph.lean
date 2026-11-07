import Lean

/-! Executable finite effect rows. Lookup is first-match, including duplicate
keys; the proofs reason about this same lookup rather than an idealized map. -/
namespace MarchLean.EffectGraph

abbrev Table := List (String × List String)

def lookup (rows : Table) (name : String) : List String :=
  ((rows.find? (fun r => r.1 == name)).map Prod.snd).getD []

def names (rows : Table) : List String := rows.map Prod.fst

def step (edges rows : Table) : Table :=
  rows.map fun (name, caps) =>
    (name, (caps ++ (lookup edges name).flatMap (lookup rows)).eraseDups)

/-- The original tail-recursive implementation, factored out of CapabilityReach. -/
def closeRows (fuel : Nat) (edges rows : Table) : Table :=
  match fuel with
  | 0 => rows
  | n + 1 => closeRows n edges (step edges rows)

/-- The same iteration, in the induction-friendly order. -/
def rounds (fuel : Nat) (edges rows : Table) : Table :=
  match fuel with
  | 0 => rows
  | n + 1 => step edges (rounds n edges rows)

structure Graph where
  edges : Table
  initial : Table
  deriving Inhabited

def Graph.vertices (g : Graph) : List String := names g.initial

def inferReach (g : Graph) : Table := closeRows g.vertices.length g.edges g.initial

/-- Compute every round once; retain earlier tables newest-first. There is
exactly one `step` call per successor, not a fresh closure at each path hop. -/
def buildHistory : Nat → Table → Table → Table × List Table
  | 0, _, rows => (rows, [])
  | n + 1, edges, rows =>
    let previous := buildHistory n edges rows
    (step edges previous.1, previous.1 :: previous.2)

def history (fuel : Nat) (edges rows : Table) : List Table :=
  (buildHistory fuel edges rows).2

/-- Descend the cached rounds, selecting the first edge that still reaches the
effect at the smaller depth. Initial effects take priority over call edges. -/
def pathFromHistory : List Table → Graph → String → String → Option (List String)
  | [], g, f, cap => if (lookup g.initial f).contains cap then some [f] else none
  | previous :: rest, g, f, cap =>
    if (lookup g.initial f).contains cap then some [f]
    else if g.vertices.contains f then
      match (lookup g.edges f).find? (fun next => (lookup previous next).contains cap) with
      | none => none
      | some next => (pathFromHistory rest g next cap).map (f :: ·)
    else none

/-- Deterministic rejection witness with one cached closure pass. The proof
layer establishes the same decreasing-fuel equations as the uncached search. -/
def findPath (fuel : Nat) (g : Graph) (f cap : String) : Option (List String) :=
  pathFromHistory (history fuel g.edges g.initial) g f cap

end MarchLean.EffectGraph
