module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite

public section

namespace SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

/-- The edge boundary `δ(S)` of a vertex set `S`, realized as the edge set of `G.between S Sᶜ`. -/
def cutEdgeSet (S : Set V) : Set (Sym2 V) :=
  (G.between S Sᶜ).edgeSet

/-- Membership in `G.cutEdgeSet S` means that the edge joins a vertex in `S` to a vertex outside
`S`. -/
theorem mem_cutEdgeSet_iff {S : Set V} {u v : V} :
    s(u, v) ∈ G.cutEdgeSet S ↔
      G.Adj u v ∧ ((u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)) := by
  -- Expose the boundary graph and normalize its edge membership.
  simp only [cutEdgeSet, mem_edgeSet, between_adj, Set.mem_compl_iff]
  constructor
  · rintro ⟨hAdj, hCross | hCross⟩
    · exact ⟨hAdj, Or.inl hCross⟩
    · exact ⟨hAdj, Or.inr ⟨hCross.2, hCross.1⟩⟩
  · rintro ⟨hAdj, hCross | hCross⟩
    · exact ⟨hAdj, Or.inl hCross⟩
    · exact ⟨hAdj, Or.inr ⟨hCross.2, hCross.1⟩⟩

/-- An edge set is a cut when it is the boundary `δ(S)` of some vertex set `S`. -/
def IsCut (F : Set (Sym2 V)) : Prop :=
  ∃ S : Set V, F = G.cutEdgeSet S

/-- An edge set is a cut exactly when it is `G.cutEdgeSet S` for some vertex set `S`. -/
theorem isCut_iff {F : Set (Sym2 V)} :
    G.IsCut F ↔ ∃ S : Set V, F = G.cutEdgeSet S := by
  -- The characterization is exactly the definition of `IsCut`.
  rfl

/-- An edge set is a proper cut when it is the boundary `δ(S)` of a nonempty proper vertex set
`S`. -/
def IsProperCut (F : Set (Sym2 V)) : Prop :=
  ∃ S : Set V, S.Nonempty ∧ S ≠ Set.univ ∧ F = G.cutEdgeSet S

/-- An edge set is a proper cut exactly when it is `G.cutEdgeSet S` for some nonempty proper
vertex set `S`. -/
theorem isProperCut_iff {F : Set (Sym2 V)} :
    G.IsProperCut F ↔ ∃ S : Set V, S.Nonempty ∧ S ≠ Set.univ ∧ F = G.cutEdgeSet S := by
  -- The characterization is exactly the definition of `IsProperCut`.
  rfl

/-- Every proper cut is a cut. -/
theorem IsProperCut.isCut {F : Set (Sym2 V)} (hF : G.IsProperCut F) :
    G.IsCut F := by
  -- Forget the side conditions from the proper-cut witness.
  rcases hF with ⟨S, hS_nonempty, hS_proper, hF⟩
  exact ⟨S, hF⟩

/-- The singleton cut `δ({v})` agrees with the canonical incidence set of `v`. -/
theorem cutEdgeSet_singleton_eq_incidenceSet (v : V) :
    G.cutEdgeSet ({v} : Set V) = G.incidenceSet v := by
  -- Compare membership on unordered edge representatives.
  ext e
  induction e using Sym2.ind with
  | h u w =>
      rw [mem_cutEdgeSet_iff]
      simp only [incidenceSet, Set.mem_sep_iff, mem_edgeSet, Sym2.mem_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hAdj, hCross | hCross⟩
        · exact ⟨hAdj, Or.inl hCross.1.symm⟩
        · exact ⟨hAdj, Or.inr hCross.1.symm⟩
      · rintro ⟨hAdj, rfl | rfl⟩
        · exact ⟨hAdj, Or.inl ⟨rfl, hAdj.ne.symm⟩⟩
        · exact ⟨hAdj, Or.inr ⟨rfl, hAdj.ne⟩⟩

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_4_definition_2_20/Cuts.lean
The cardinality of the singleton cut `δ({v})` is the degree of `v` when the local boundary of
`v` is finite. -/
theorem card_cutEdgeSet_singleton_eq_degree (v : V)
    [Fintype (G.neighborSet v)] [Fintype (G.cutEdgeSet ({v} : Set V))] :
    Fintype.card (G.cutEdgeSet ({v} : Set V)) = G.degree v := by
  -- Transport the finite boundary subtype to the neighbor subtype.
  classical
  let e : G.cutEdgeSet ({v} : Set V) ≃ G.neighborSet v :=
    (Equiv.setCongr (cutEdgeSet_singleton_eq_incidenceSet G v)).trans
      (G.incidenceSetEquivNeighborSet v)
  exact (Fintype.card_congr e).trans (G.card_neighborSet_eq_degree v)

#print axioms card_cutEdgeSet_singleton_eq_degree

end SimpleGraph

end
