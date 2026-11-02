import Mathlib

open scoped BigOperators

namespace SimpleGraph
namespace Subgraph

variable {V α : Type*} {G : SimpleGraph V}

section Weights

variable [Finite V] [AddCommMonoid α]
/-- The total weight of a subgraph, computed by summing the weights of its edges. -/
noncomputable def matchingWeight (w : Sym2 V → α) (M : G.Subgraph) : α :=
  letI : Fintype M.edgeSet := Fintype.ofFinite M.edgeSet
  ∑ e : M.edgeSet, w e

/-- Expands `matchingWeight` as the sum of the edge weights over the edge set of the subgraph. -/
theorem matchingWeight_eq_sum (w : Sym2 V → α) (M : G.Subgraph) :
    matchingWeight w M =
      letI : Fintype M.edgeSet := Fintype.ofFinite M.edgeSet
      ∑ e : M.edgeSet, w e := by
  rfl

variable [Preorder α]

/-- A matching has minimum weight among the matchings of cardinality `k` when it has cardinality
`k` and no competing matching of cardinality `k` has smaller total weight. -/
@[mk_iff]
structure IsMinimumWeightMatchingOfCardinality
    (w : Sym2 V → α) (k : ℕ) (M : G.Subgraph) : Prop where
  isMatching : M.IsMatching
  card : M.edgeSet.ncard = k
  minimum : ∀ M' : G.Subgraph,
    M'.IsMatching →
    M'.edgeSet.ncard = k →
    matchingWeight w M ≤ matchingWeight w M'

/-- Definition 4.4.3-extra-1 (1). A perfect matching in a bipartite graph is minimum-weight if its
total weight is at most the total weight of every other perfect matching; this is the assignment
problem. -/
@[mk_iff]
structure IsMinimumWeightPerfectMatching
    (w : Sym2 V → α) (M : G.Subgraph) : Prop where
  isPerfectMatching : M.IsPerfectMatching
  minimum : ∀ M' : G.Subgraph,
    M'.IsPerfectMatching →
    matchingWeight w M ≤ matchingWeight w M'

/-- Source-facing reformulation of minimum-weight perfect matchings in a bipartite graph. -/
theorem isBipartiteWith_and_isMinimumWeightPerfectMatching_iff
    {U W : Set V} (w : Sym2 V → α) (M : G.Subgraph) :
    G.IsBipartiteWith U W ∧ IsMinimumWeightPerfectMatching w M ↔
      G.IsBipartiteWith U W ∧
        M.IsPerfectMatching ∧
          ∀ M' : G.Subgraph, M'.IsPerfectMatching → matchingWeight w M ≤ matchingWeight w M' :=
  by rw [isMinimumWeightPerfectMatching_iff]

end Weights

end Subgraph

variable {V : Type*} {G : SimpleGraph V} {U W : Set V}

/-- Helper for Definition 4.4.3-extra-1: every edge of a matching in a bipartite graph has a unique
endpoint on the chosen side of the bipartition. -/
theorem existsUnique_side_vertex_of_edge {M : G.Subgraph}
    (hUW : G.IsBipartiteWith U W) (hM : M.IsMatching) (e : M.edgeSet) :
    ∃! u : ↥(U ∩ M.verts), hM.toEdge ⟨u.1, u.2.2⟩ = e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h v w =>
      have hvw : M.Adj v w := by
        simpa [Subgraph.mem_edgeSet] using he
      rcases hUW.mem_of_adj hvw.adj_sub with hleft | hright
      · refine ⟨⟨v, ⟨hleft.1, hvw.fst_mem⟩⟩, ?_, ?_⟩
        · -- The chosen left endpoint maps back to the original edge.
          exact hM.toEdge_eq_of_adj hvw
        · intro u hu
          apply Subtype.ext
          have hu_mem : u.1 ∈ ((⟨s(v, w), hvw⟩ : M.edgeSet) : Sym2 V) := by
            simpa [hu] using hM.mem_coe_toEdge u.2.2
          rcases Sym2.mem_iff.mp hu_mem with rfl | rfl
          · rfl
          · exfalso
            exact (Set.disjoint_left.mp hUW.disjoint u.2.1) hleft.2
      · refine ⟨⟨w, ⟨hright.2, hvw.snd_mem⟩⟩, ?_, ?_⟩
        · -- If the right endpoint lies in `U`, reverse the edge before using `toEdge_eq_of_adj`.
          simpa [Subgraph.mem_edgeSet, Sym2.eq_swap] using hM.toEdge_eq_of_adj hvw.symm
        · intro u hu
          apply Subtype.ext
          have hu_mem : u.1 ∈ ((⟨s(v, w), hvw⟩ : M.edgeSet) : Sym2 V) := by
            simpa [hu] using hM.mem_coe_toEdge u.2.2
          rcases Sym2.mem_iff.mp hu_mem with rfl | rfl
          · exfalso
            exact (Set.disjoint_left.mp hUW.disjoint u.2.1) hright.1
          · rfl

/-- Helper for Definition 4.4.3-extra-1: the matched vertices on one side of a bipartite matching
are sent bijectively to the edge set by the matching-edge map. -/
theorem matching_side_bijective {M : G.Subgraph}
    (hUW : G.IsBipartiteWith U W) (hM : M.IsMatching) :
    Function.Bijective (fun u : ↥(U ∩ M.verts) ↦ hM.toEdge ⟨u.1, u.2.2⟩) := by
  classical
  constructor
  · intro u u' huu'
    -- Uniqueness of the side-endpoint for a fixed edge gives injectivity.
    have hUnique := existsUnique_side_vertex_of_edge hUW hM (hM.toEdge ⟨u.1, u.2.2⟩)
    exact hUnique.unique rfl huu'.symm
  · intro e
    -- Surjectivity comes from choosing the unique side-endpoint of each edge.
    refine ⟨Classical.choose (existsUnique_side_vertex_of_edge hUW hM e), ?_⟩
    exact (Classical.choose_spec (existsUnique_side_vertex_of_edge hUW hM e)).1

/-- Definition 4.4.3-extra-1 (2). If a bipartite graph with sides `U` and `W` has a perfect
matching, then the two sides of the bipartition have the same cardinality. -/
theorem bipartition_encard_eq_of_exists_perfect_matching
    (hUW : G.IsBipartiteWith U W)
    (hex : ∃ M : G.Subgraph, M.IsPerfectMatching) :
    U.encard = W.encard := by
  obtain ⟨M, hM⟩ := hex
  -- Count each side by identifying it with the edge set of the perfect matching.
  have hLeft :
      U.encard = M.edgeSet.encard := by
    simpa [hM.2.verts_eq_univ, Set.inter_univ] using
      Set.encard_congr (Equiv.ofBijective _ (matching_side_bijective hUW hM.1))
  have hRight :
      W.encard = M.edgeSet.encard := by
    simpa [hM.2.verts_eq_univ, Set.inter_univ] using
      Set.encard_congr
        (Equiv.ofBijective _ (matching_side_bijective hUW.symm hM.1))
  exact hLeft.trans hRight.symm

namespace Subgraph

variable {M : G.Subgraph} {n : ℕ}

/-- Definition 4.4.3-extra-1 (3). If `U` and `W` are the two sides of a bipartition and both have
cardinality `n`, then a matching is perfect exactly when it has `n` edges. -/
theorem is_perfect_matching_iff_card_edge_set_eq
    [Finite V]
    (hUW : G.IsBipartiteWith U W) (hcover : U ∪ W = Set.univ)
    (hU : U.ncard = n) (hW : W.ncard = n) (hM : M.IsMatching) :
    M.IsPerfectMatching ↔ M.edgeSet.ncard = n := by
  constructor
  · intro hPerfect
    -- A perfect matching saturates all of `U`, so the side-edge bijection counts exactly `n` edges.
    calc
      M.edgeSet.ncard = (U ∩ M.verts).ncard := by
        simpa using
          (Nat.card_congr
            (Equiv.ofBijective _ (matching_side_bijective hUW hM))).symm
      _ = U.ncard := by simp [hPerfect.2.verts_eq_univ]
      _ = n := hU
  · intro hCard
    -- Equality of side counts forces every vertex on each side to be matched.
    have hLeftCount : (U ∩ M.verts).ncard = n := by
      calc
        (U ∩ M.verts).ncard = M.edgeSet.ncard := by
          simpa using
            Nat.card_congr
              (Equiv.ofBijective _ (matching_side_bijective hUW hM))
        _ = n := hCard
    have hRightCount : (W ∩ M.verts).ncard = n := by
      calc
        (W ∩ M.verts).ncard = M.edgeSet.ncard := by
          simpa using
            Nat.card_congr
              (Equiv.ofBijective _ (matching_side_bijective hUW.symm hM))
        _ = n := hCard
    have hUeq : U ∩ M.verts = U := by
      -- The matched vertices on `U` have the same cardinality as `U`, so no left vertex is missed.
      apply Set.eq_of_subset_of_ncard_le Set.inter_subset_left
      rw [hU, hLeftCount]
    have hWeq : W ∩ M.verts = W := by
      -- The same counting argument applies on the right side.
      apply Set.eq_of_subset_of_ncard_le Set.inter_subset_left
      rw [hW, hRightCount]
    have hUsubset : U ⊆ M.verts := by
      intro u hu
      have : u ∈ U ∩ M.verts := by
        rw [hUeq]
        exact hu
      exact this.2
    have hWsubset : W ⊆ M.verts := by
      intro w hw
      have : w ∈ W ∩ M.verts := by
        rw [hWeq]
        exact hw
      exact this.2
    refine ⟨hM, ?_⟩
    intro v
    have hv : v ∈ U ∪ W := by
      simp [hcover]
    rcases hv with hvU | hvW
    · exact hUsubset hvU
    · exact hWsubset hvW

end Subgraph
end SimpleGraph
