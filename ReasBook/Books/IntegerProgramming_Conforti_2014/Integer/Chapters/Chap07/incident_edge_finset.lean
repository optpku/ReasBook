import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

noncomputable section

section Chap07IncidentEdgeFinset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- The graph edges incident with the vertex `v`. -/
def incidentEdgeFinset (G : SimpleGraph V) (v : V) : Finset G.edgeSet :=
  letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  Finset.univ.filter fun e ↦ v ∈ (e : Sym2 V)

/-- An edge-coordinate belongs to `incidentEdgeFinset G v` exactly when it is incident to `v`. -/
theorem mem_incidentEdgeFinset_iff
    {v : V} {e : G.edgeSet} :
    e ∈ incidentEdgeFinset G v ↔ v ∈ (e : Sym2 V) := by
  simp [incidentEdgeFinset]

end Chap07IncidentEdgeFinset
