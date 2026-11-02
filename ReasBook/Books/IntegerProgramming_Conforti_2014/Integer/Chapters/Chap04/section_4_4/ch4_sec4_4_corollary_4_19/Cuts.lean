import Mathlib.Combinatorics.SimpleGraph.Basic

namespace SimpleGraph

section Cuts

universe u

variable {V : Type u} (G : SimpleGraph V)

section Finite

variable [Fintype V]

/-- The cut edges `δ(S)` of a vertex set `S`, regarded as a finset of edge coordinates of `G`. -/
noncomputable def cutEdgeFinset (S : Set V) : Finset G.edgeSet :=
  let _ : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  let _ : DecidablePred fun e : G.edgeSet ↦ ∃ u ∈ S, ∃ v ∉ S, s(u, v) = (e : Sym2 V) :=
    Classical.decPred _
  Finset.univ.filter fun e ↦ ∃ u ∈ S, ∃ v ∉ S, s(u, v) = (e : Sym2 V)

/-- The cut edges `δ(S)` in the edge coordinates of `G`. -/
notation "δ[" G "] " S:arg => cutEdgeFinset G S

/-- An edge-coordinate belongs to `δ[G] S` exactly when one endpoint lies in `S` and the other
lies outside `S`. -/
theorem mem_cutEdgeFinset_iff {S : Set V} {e : G.edgeSet} :
    e ∈ δ[G] S ↔ ∃ u ∈ S, ∃ v ∉ S, s(u, v) = (e : Sym2 V) := by
  classical
  simp [cutEdgeFinset]

end Finite
end Cuts

end SimpleGraph
