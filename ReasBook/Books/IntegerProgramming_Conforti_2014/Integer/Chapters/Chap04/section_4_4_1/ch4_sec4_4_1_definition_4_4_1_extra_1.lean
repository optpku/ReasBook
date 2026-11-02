import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped symmDiff

namespace SimpleGraph
namespace Walk

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- Auxiliary definition for Definition 4.4.1-extra-1 (1): An `M`-alternating path is a path whose
underlying graph
alternates with the matching `M` along consecutive edges. -/
structure IsMatchingAlternating (M : G.Subgraph) (p : G.Walk u v) : Prop where
  /-- The underlying walk is a path. -/
  isPath : p.IsPath
  /-- Along the path, every internal vertex is incident to one edge from `M` and one edge outside
  `M`, equivalently the path subgraph is alternating with respect to `M`. -/
  alternating : IsAlternating p.toSubgraph.spanningCoe M.spanningCoe

/-- Helper characterization of `IsMatchingAlternating`. -/
theorem isMatchingAlternating_iff {M : G.Subgraph} {p : G.Walk u v} :
    IsMatchingAlternating M p ↔
      p.IsPath ∧ IsAlternating p.toSubgraph.spanningCoe M.spanningCoe := by
  constructor
  · intro hp
    exact ⟨hp.isPath, hp.alternating⟩
  · rintro ⟨hisPath, halt⟩
    exact ⟨hisPath, halt⟩

/-- Auxiliary definition for Definition 4.4.1-extra-1 (2): An `M`-augmenting path is an
`M`-alternating path whose two
endpoints are not covered by the matching `M`, and which has at least one edge. -/
structure IsMatchingAugmenting (M : G.Subgraph) (p : G.Walk u v) : Prop
    extends IsMatchingAlternating M p where
  /-- An augmenting path is nontrivial: it contains at least one edge. -/
  not_nil : ¬ p.Nil
  /-- The initial vertex is not covered by any edge of `M`. -/
  start_uncovered : u ∉ M.support
  /-- The terminal vertex is not covered by any edge of `M`. -/
  end_uncovered : v ∉ M.support

/-- Helper characterization of `IsMatchingAugmenting`. -/
theorem isMatchingAugmenting_iff {M : G.Subgraph} {p : G.Walk u v} :
    IsMatchingAugmenting M p ↔
      IsMatchingAlternating M p ∧ ¬ p.Nil ∧ u ∉ M.support ∧ v ∉ M.support := by
  constructor
  · intro hp
    exact ⟨hp.toIsMatchingAlternating, hp.not_nil, hp.start_uncovered, hp.end_uncovered⟩
  · rintro ⟨halt, hnil, hu, hv⟩
    exact ⟨halt, hnil, hu, hv⟩

private def augment_matching_graph (M : G.Subgraph) (p : G.Walk u v) : SimpleGraph V :=
  M.spanningCoe ∆ p.toSubgraph.spanningCoe

private theorem augment_matching_graph_le (M : G.Subgraph) (p : G.Walk u v) :
    augment_matching_graph M p ≤ G := by
  dsimp [augment_matching_graph]
  exact symmDiff_le
    (show M.spanningCoe ≤ p.toSubgraph.spanningCoe ⊔ G from
      le_sup_of_le_right M.spanningCoe_le)
    (show p.toSubgraph.spanningCoe ≤ M.spanningCoe ⊔ G from
      le_sup_of_le_right p.toSubgraph.spanningCoe_le)

/-- Auxiliary definition for Definition 4.4.1-extra-1 (3): Augmenting a matching along a path
toggles exactly the path
edges, i.e. it takes the symmetric difference of `M` with the path subgraph. -/
def augment_matching (M : G.Subgraph) (p : G.Walk u v) : G.Subgraph :=
  { verts := (augment_matching_graph M p).support
    Adj := (augment_matching_graph M p).Adj
    adj_sub := fun h ↦ augment_matching_graph_le M p h
    edge_vert := fun h ↦ h.mem_support_left
    symm := (augment_matching_graph M p).symm }

/-- Helper expansion for `augment_matching`. -/
theorem augment_matching_def {M : G.Subgraph} {p : G.Walk u v} :
    (augment_matching M p).spanningCoe = M.spanningCoe ∆ p.toSubgraph.spanningCoe := by
  ext x y
  rfl

/-- Helper for Definition 4.4.1-extra-1: a path vertex distinct from the two endpoints occurs at
an internal index of the walk. -/
lemma existsInternalIndex_of_mem_support_ne_endpoints {x : V} {p : G.Walk u v} (_hp : p.IsPath)
    (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v) :
    ∃ i, 0 < i ∧ i < p.length ∧ x = p.getVert i := by
  obtain ⟨i, hxi, hi_le⟩ := mem_support_iff_exists_getVert.mp hx
  have hi0 : 0 < i := by
    have hi_ne_zero : i ≠ 0 := by
      intro hi_zero
      apply hxu
      calc
        x = p.getVert i := hxi.symm
        _ = p.getVert 0 := by simp [hi_zero]
        _ = u := p.getVert_zero
    exact Nat.pos_iff_ne_zero.mpr hi_ne_zero
  have hil : i < p.length := by
    have hi_ne_length : i ≠ p.length := by
      intro hi_length
      apply hxv
      calc
        x = p.getVert i := hxi.symm
        _ = p.getVert p.length := by simp [hi_length]
        _ = v := p.getVert_length
    exact lt_of_le_of_ne hi_le hi_ne_length
  exact ⟨i, hi0, hil, hxi.symm⟩

/-- Auxiliary theorem for Definition 4.4.1-extra-1 (4): Augmenting a matching along an augmenting
path produces a
matching. -/
theorem augment_matching_isMatching {M : G.Subgraph} {p : G.Walk u v}
    (hM : M.IsMatching) (hp : IsMatchingAugmenting M p) :
    (augment_matching M p).IsMatching := by
  classical
  let hpPath : p.IsPath := hp.toIsMatchingAlternating.isPath
  let hpAlt : IsAlternating p.toSubgraph.spanningCoe M.spanningCoe :=
    hp.toIsMatchingAlternating.alternating
  have hstart_uncovered : ∀ y, ¬ M.Adj u y := by
    intro y huy
    exact hp.start_uncovered (by simpa [hM.support_eq_verts] using huy.fst_mem)
  have hend_uncovered : ∀ y, ¬ M.Adj v y := by
    intro y hvy
    exact hp.end_uncovered (by simpa [hM.support_eq_verts] using hvy.fst_mem)
  intro x hx
  -- Route correction: prove uniqueness by separating off-path vertices from the three path cases.
  by_cases hxu : x = u
  · subst hxu
    use p.snd
    constructor
    · -- The first path edge is toggled into the augmented matching because
      -- `u` is uncovered in `M`.
      change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x p.snd
      have huPath : p.toSubgraph.Adj x p.snd := p.toSubgraph_adj_snd hp.not_nil
      exact Or.inr ⟨huPath, hstart_uncovered _⟩
    · intro y hy
      -- Any augmented neighbor of the start vertex must be the unique first path neighbor.
      change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x y at hy
      have hyPath : p.toSubgraph.Adj x y := by
        simpa [symmDiff_def, Subgraph.spanningCoe_adj, hstart_uncovered] using hy
      have hy_mem : y ∈ p.toSubgraph.neighborSet x := (p.toSubgraph.mem_neighborSet _ _).2 hyPath
      rw [hpPath.neighborSet_toSubgraph_startpoint hp.not_nil] at hy_mem
      simpa using hy_mem
  by_cases hxv : x = v
  · subst hxv
    use p.penultimate
    constructor
    · -- The endpoint case is symmetric: the last path edge is toggled into the new matching.
      change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x p.penultimate
      have hvPath : p.toSubgraph.Adj x p.penultimate := by
        exact (p.toSubgraph_adj_penultimate hp.not_nil).symm
      exact Or.inr ⟨hvPath, hend_uncovered _⟩
    · intro y hy
      -- Any augmented neighbor of the end vertex must be the unique last path neighbor.
      change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x y at hy
      have hyPath : p.toSubgraph.Adj x y := by
        simpa [symmDiff_def, Subgraph.spanningCoe_adj, hend_uncovered] using hy
      have hy_mem : y ∈ p.toSubgraph.neighborSet x := (p.toSubgraph.mem_neighborSet _ _).2 hyPath
      rw [hpPath.neighborSet_toSubgraph_endpoint hp.not_nil] at hy_mem
      simpa using hy_mem
  by_cases hx_path : x ∈ p.support
  · -- Internal path vertices lose their unique matched path edge and keep the opposite path edge.
    obtain ⟨i, hi0, hil, hxi⟩ :=
      existsInternalIndex_of_mem_support_ne_endpoints hpPath hx_path hxu hxv
    have hprev : p.toSubgraph.Adj x (p.getVert (i - 1)) := by
      have hmem : p.getVert (i - 1) ∈ p.toSubgraph.neighborSet x := by
        rw [hxi, hpPath.neighborSet_toSubgraph_internal (by omega) hil]
        simp
      exact (p.toSubgraph.mem_neighborSet _ _).1 hmem
    have hnext : p.toSubgraph.Adj x (p.getVert (i + 1)) := by
      have hmem : p.getVert (i + 1) ∈ p.toSubgraph.neighborSet x := by
        rw [hxi, hpPath.neighborSet_toSubgraph_internal (by omega) hil]
        simp
      exact (p.toSubgraph.mem_neighborSet _ _).1 hmem
    have hprev_ne_next : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
      intro hEq
      have := hpPath.getVert_injOn (by simp; omega) (by simp; omega) hEq
      omega
    have hAlt_local :
        M.Adj x (p.getVert (i - 1)) ↔ ¬ M.Adj x (p.getVert (i + 1)) := by
      simpa [Subgraph.spanningCoe_adj, hxi] using hpAlt hprev_ne_next hprev hnext
    by_cases hMatchedPrev : M.Adj x (p.getVert (i - 1))
    · use p.getVert (i + 1)
      constructor
      · -- The unmatched incident path edge survives the symmetric difference.
        change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x (p.getVert (i + 1))
        have hNotMatchedNext : ¬ M.Adj x (p.getVert (i + 1)) := hAlt_local.mp hMatchedPrev
        simp [symmDiff_def, Subgraph.spanningCoe_adj, hnext, hNotMatchedNext]
      · intro y hy
        -- Any candidate from the `M` side would have to be the deleted predecessor edge.
        change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x y at hy
        have hy' :
            M.Adj x y ∧ ¬ p.toSubgraph.Adj x y ∨
              p.toSubgraph.Adj x y ∧ ¬ M.Adj x y := by
          simpa [symmDiff_def, Subgraph.spanningCoe_adj] using hy
        rcases hy' with hyM | hyP
        · have : y = p.getVert (i - 1) :=
            (hM.eq_of_adj_left (u := x) (v := p.getVert (i - 1)) (w := y) hMatchedPrev hyM.1).symm
          subst this
          exact (hyM.2 hprev).elim
        · have hy_mem : y ∈ p.toSubgraph.neighborSet x := by
            exact (p.toSubgraph.mem_neighborSet _ _).2 hyP.1
          rw [hxi, hpPath.neighborSet_toSubgraph_internal (by omega) hil] at hy_mem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
          rcases hy_mem with rfl | rfl
          · exact (hyP.2 hMatchedPrev).elim
          · rfl
    · use p.getVert (i - 1)
      constructor
      · -- The predecessor survives exactly when the successor is the matched edge.
        change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x (p.getVert (i - 1))
        simp [symmDiff_def, Subgraph.spanningCoe_adj, hprev, hMatchedPrev]
      · intro y hy
        -- Any surviving augmented edge at an internal path vertex must be the predecessor now.
        change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x y at hy
        have hMatchedNext : M.Adj x (p.getVert (i + 1)) := by
          by_contra hNotMatchedNext
          exact hMatchedPrev (hAlt_local.mpr hNotMatchedNext)
        have hy' :
            M.Adj x y ∧ ¬ p.toSubgraph.Adj x y ∨
              p.toSubgraph.Adj x y ∧ ¬ M.Adj x y := by
          simpa [symmDiff_def, Subgraph.spanningCoe_adj] using hy
        rcases hy' with hyM | hyP
        · have : y = p.getVert (i + 1) :=
            (hM.eq_of_adj_left (u := x) (v := p.getVert (i + 1)) (w := y) hMatchedNext hyM.1).symm
          subst this
          exact (hyM.2 hnext).elim
        · have hy_mem : y ∈ p.toSubgraph.neighborSet x := by
            exact (p.toSubgraph.mem_neighborSet _ _).2 hyP.1
          rw [hxi, hpPath.neighborSet_toSubgraph_internal (by omega) hil] at hy_mem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
          rcases hy_mem with rfl | rfl
          · rfl
          · exact (hyP.2 hMatchedNext).elim
  · -- Away from the path, augmentation does not change the original matching edge.
    have hnotPath : ∀ y, ¬ p.toSubgraph.Adj x y := by
      intro y hxy
      exact hx_path (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hxy))
    have hx_support : x ∈ (M.spanningCoe ∆ p.toSubgraph.spanningCoe).support := by
      simpa [augment_matching, augment_matching_graph] using hx
    obtain ⟨y, hy⟩ := hx_support
    have hyM : M.Adj x y := by
      have hPy : ¬ p.toSubgraph.Adj x y := hnotPath y
      simpa [symmDiff_def, Subgraph.spanningCoe_adj, hPy] using hy
    obtain ⟨z, hz, huniq⟩ := hM hyM.fst_mem
    use z
    constructor
    · -- The unique original matching edge survives because no path edge touches `x`.
      change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x z
      have hPz : ¬ p.toSubgraph.Adj x z := hnotPath z
      simpa [symmDiff_def, Subgraph.spanningCoe_adj] using
        (Or.inl ⟨hz, hPz⟩ :
          (M.spanningCoe \ p.toSubgraph.spanningCoe ⊔
            p.toSubgraph.spanningCoe \ M.spanningCoe).Adj x z)
    · intro y hyAug
      -- Any augmented edge at an off-path vertex is just the original matching edge.
      change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x y at hyAug
      have hPy : ¬ p.toSubgraph.Adj x y := hnotPath y
      have hyM' : M.Adj x y := by
        simpa [symmDiff_def, Subgraph.spanningCoe_adj, hPy] using hyAug
      exact huniq y hyM'

/-- Helper for Definition 4.4.1-extra-1: a matching covers exactly twice as many vertices as it
has edges. -/
lemma matchingVertsNcard_eq_twoMulEdgeSetNcard [Finite V] {K : G.Subgraph}
    (hK : K.IsMatching) :
    K.verts.ncard = 2 * K.edgeSet.ncard := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  -- On a matching, covered vertices have degree `1` and uncovered vertices have degree `0`.
  have hdeg : ∀ x : V, K.spanningCoe.degree x = if x ∈ K.verts then 1 else 0 := by
    intro x
    by_cases hx : x ∈ K.verts
    · have hdegK : K.degree x = 1 :=
        (SimpleGraph.Subgraph.isMatching_iff_forall_degree (M := K)).mp hK x hx
      simp [hx, Subgraph.degree_spanningCoe, hdegK]
    · have hdegK : K.degree x = 0 := K.degree_of_notMem_verts hx
      simp [hx, Subgraph.degree_spanningCoe, hdegK]
  have hsum : Fintype.card K.verts = 2 * Fintype.card K.spanningCoe.edgeSet := by
    -- Summing degrees counts covered vertices, and the handshaking lemma counts edges.
    calc
      Fintype.card K.verts = ∑ x : V, K.spanningCoe.degree x := by
        rw [Fintype.card_subtype]
        rw [Finset.card_eq_sum_ones]
        simp [hdeg]
      _ = 2 * K.spanningCoe.edgeFinset.card := K.spanningCoe.sum_degrees_eq_twice_card_edges
      _ = 2 * Fintype.card K.spanningCoe.edgeSet := by
        simpa using congrArg (fun n : ℕ ↦ 2 * n) K.spanningCoe.edgeFinset_card
  have hsum' : Nat.card K.verts = 2 * Nat.card K.spanningCoe.edgeSet := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact hsum
  -- Convert the finite-cardinality identity back to `Set.ncard` and the original subgraph.
  calc
    K.verts.ncard = Nat.card K.verts := by rw [Nat.card_coe_set_eq]
    _ = 2 * Nat.card K.spanningCoe.edgeSet := hsum'
    _ = 2 * K.spanningCoe.edgeSet.ncard := by rw [Nat.card_coe_set_eq]
    _ = 2 * K.edgeSet.ncard := by rw [Subgraph.edgeSet_spanningCoe]

/-- Helper for Definition 4.4.1-extra-1: augmenting toggles exactly the path edges at the edge-set
level. -/
lemma augmentMatching_edgeSet_eq_symmDiff {M : G.Subgraph} {p : G.Walk u v} :
    (augment_matching M p).edgeSet = M.edgeSet ∆ p.edgeSet := by
  ext e
  refine Sym2.ind ?_ e
  intro x y
  -- Expand the augmented graph definition once and read it directly on edge sets.
  have hpath : p.toSubgraph.Adj x y ↔ s(x, y) ∈ p.edges := by
    calc
      p.toSubgraph.Adj x y ↔ s(x, y) ∈ p.toSubgraph.edgeSet := by
        rw [Subgraph.mem_edgeSet]
      _ ↔ s(x, y) ∈ p.edgeSet := by rw [Walk.edgeSet_toSubgraph]
      _ ↔ s(x, y) ∈ p.edges := by rw [Walk.mem_edgeSet]
  change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x y ↔
      M.Adj x y ∧ s(x, y) ∉ p.edges ∨ s(x, y) ∈ p.edges ∧ ¬ M.Adj x y
  simpa [hpath] using
    (show (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x y ↔
        M.Adj x y ∧ ¬ p.toSubgraph.Adj x y ∨ p.toSubgraph.Adj x y ∧ ¬ M.Adj x y from by
      simp [symmDiff_def, Subgraph.spanningCoe_adj])

/-- Helper for Definition 4.4.1-extra-1: on the path itself, augmentation keeps precisely the
previously unmatched path edges. -/
lemma augmentPathPiece_edgeSet_eq_pathDiff {M : G.Subgraph} {p : G.Walk u v} :
    ((augment_matching M p) ⊓ p.toSubgraph).edgeSet = p.edgeSet \ M.edgeSet := by
  ext e
  refine Sym2.ind ?_ e
  intro x y
  -- Restricting the symmetric difference to the path leaves the `path \ M` part.
  by_cases hxy : s(x, y) ∈ p.edgeSet
  · simp [hxy, augmentMatching_edgeSet_eq_symmDiff, symmDiff_def]
  · simp [hxy, augmentMatching_edgeSet_eq_symmDiff, symmDiff_def]

/-- Helper for Definition 4.4.1-extra-1: the old path piece is a matching, and its vertices are
exactly the internal path vertices. -/
lemma oldPathPiece_isMatching_and_verts {M : G.Subgraph} {p : G.Walk u v}
    (hM : M.IsMatching) (hp : IsMatchingAugmenting M p) :
    (M ⊓ p.toSubgraph).IsMatching ∧
      (M ⊓ p.toSubgraph).verts = p.toSubgraph.verts \ {u, v} := by
  classical
  let hpPath : p.IsPath := hp.toIsMatchingAlternating.isPath
  let hpAlt : IsAlternating p.toSubgraph.spanningCoe M.spanningCoe :=
    hp.toIsMatchingAlternating.alternating
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxInf : x ∈ M.verts ∩ p.toSubgraph.verts := by
      simpa [Subgraph.verts_inf] using hx
    have hxM : x ∈ M.support := by
      simpa [hM.support_eq_verts] using hxInf.1
    have hxu : x ≠ u := by
      intro hxu
      exact hp.start_uncovered (hxu ▸ hxM)
    have hxv : x ≠ v := by
      intro hxv
      exact hp.end_uncovered (hxv ▸ hxM)
    have hxSupport : x ∈ p.support := p.mem_verts_toSubgraph.mp hxInf.2
    obtain ⟨i, hi0, hil, hxi⟩ :=
      existsInternalIndex_of_mem_support_ne_endpoints hpPath hxSupport hxu hxv
    have hprev : p.toSubgraph.Adj x (p.getVert (i - 1)) := by
      have hmem : p.getVert (i - 1) ∈ p.toSubgraph.neighborSet x := by
        rw [hxi, hpPath.neighborSet_toSubgraph_internal (by omega) hil]
        simp
      exact (p.toSubgraph.mem_neighborSet _ _).1 hmem
    have hnext : p.toSubgraph.Adj x (p.getVert (i + 1)) := by
      have hmem : p.getVert (i + 1) ∈ p.toSubgraph.neighborSet x := by
        rw [hxi, hpPath.neighborSet_toSubgraph_internal (by omega) hil]
        simp
      exact (p.toSubgraph.mem_neighborSet _ _).1 hmem
    have hprev_ne_next : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
      intro hEq
      have := hpPath.getVert_injOn (by simp; omega) (by simp; omega) hEq
      omega
    have hAlt_local :
        M.Adj x (p.getVert (i - 1)) ↔ ¬ M.Adj x (p.getVert (i + 1)) := by
      simpa [Subgraph.spanningCoe_adj, hxi] using hpAlt hprev_ne_next hprev hnext
    by_cases hMatchedPrev : M.Adj x (p.getVert (i - 1))
    · refine ⟨p.getVert (i - 1), ?_, ?_⟩
      · exact ⟨hMatchedPrev, hprev⟩
      · intro w hw
        exact
          (hM.eq_of_adj_left (u := x) (v := p.getVert (i - 1)) (w := w) hMatchedPrev hw.1).symm
    · have hMatchedNext : M.Adj x (p.getVert (i + 1)) := by
        by_contra hNotMatchedNext
        exact hMatchedPrev (hAlt_local.mpr hNotMatchedNext)
      refine ⟨p.getVert (i + 1), ?_, ?_⟩
      · exact ⟨hMatchedNext, hnext⟩
      · intro w hw
        exact
          (hM.eq_of_adj_left (u := x) (v := p.getVert (i + 1)) (w := w) hMatchedNext hw.1).symm
  · ext x
    constructor
    · intro hx
      have hxInf : x ∈ M.verts ∩ p.toSubgraph.verts := by
        simpa [Subgraph.verts_inf] using hx
      have hxM : x ∈ M.support := by
        simpa [hM.support_eq_verts] using hxInf.1
      have hxu : x ≠ u := by
        intro hxu
        exact hp.start_uncovered (hxu ▸ hxM)
      have hxv : x ≠ v := by
        intro hxv
        exact hp.end_uncovered (hxv ▸ hxM)
      -- A matched path vertex cannot be one of the uncovered endpoints.
      exact ⟨hxInf.2, by simp [hxu, hxv]⟩
    · intro hx
      have hx' := hx
      simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx' with ⟨hxPath, hxNotEnds⟩
      have hxu : x ≠ u := by
        intro hxu
        exact hxNotEnds (by simp [hxu])
      have hxv : x ≠ v := by
        intro hxv
        exact hxNotEnds (by simp [hxv])
      have hxSupport : x ∈ p.support := p.mem_verts_toSubgraph.mp hxPath
      obtain ⟨i, hi0, hil, hxi⟩ :=
        existsInternalIndex_of_mem_support_ne_endpoints hpPath hxSupport hxu hxv
      have hprev : p.toSubgraph.Adj x (p.getVert (i - 1)) := by
        have hmem : p.getVert (i - 1) ∈ p.toSubgraph.neighborSet x := by
          rw [hxi, hpPath.neighborSet_toSubgraph_internal (by omega) hil]
          simp
        exact (p.toSubgraph.mem_neighborSet _ _).1 hmem
      have hnext : p.toSubgraph.Adj x (p.getVert (i + 1)) := by
        have hmem : p.getVert (i + 1) ∈ p.toSubgraph.neighborSet x := by
          rw [hxi, hpPath.neighborSet_toSubgraph_internal (by omega) hil]
          simp
        exact (p.toSubgraph.mem_neighborSet _ _).1 hmem
      have hprev_ne_next : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
        intro hEq
        have := hpPath.getVert_injOn (by simp; omega) (by simp; omega) hEq
        omega
      have hAlt_local :
          M.Adj x (p.getVert (i - 1)) ↔ ¬ M.Adj x (p.getVert (i + 1)) := by
        simpa [Subgraph.spanningCoe_adj, hxi] using hpAlt hprev_ne_next hprev hnext
      have hxM : x ∈ M.support := by
        by_cases hMatchedPrev : M.Adj x (p.getVert (i - 1))
        · exact (Subgraph.mem_support M).2 ⟨p.getVert (i - 1), hMatchedPrev⟩
        · have hMatchedNext : M.Adj x (p.getVert (i + 1)) := by
            by_contra hNotMatchedNext
            exact hMatchedPrev (hAlt_local.mpr hNotMatchedNext)
          exact (Subgraph.mem_support M).2 ⟨p.getVert (i + 1), hMatchedNext⟩
      have hxMVert : x ∈ M.verts := by
        simpa [hM.support_eq_verts] using hxM
      -- Every internal path vertex is matched by one of the two alternating path edges.
      simpa [Subgraph.verts_inf] using And.intro hxMVert hxPath

/-- Helper for Definition 4.4.1-extra-1: the new path piece is a matching, and after augmentation
every path vertex becomes covered by a path edge. -/
lemma newPathPiece_isMatching_and_verts {M : G.Subgraph} {p : G.Walk u v}
    (hM : M.IsMatching) (hp : IsMatchingAugmenting M p) :
    ((augment_matching M p) ⊓ p.toSubgraph).IsMatching ∧
      ((augment_matching M p) ⊓ p.toSubgraph).verts = p.toSubgraph.verts := by
  classical
  let hpPath : p.IsPath := hp.toIsMatchingAlternating.isPath
  let hpAlt : IsAlternating p.toSubgraph.spanningCoe M.spanningCoe :=
    hp.toIsMatchingAlternating.alternating
  let hAug : (augment_matching M p).IsMatching := augment_matching_isMatching hM hp
  have hstart_uncovered : ∀ y, ¬ M.Adj u y := by
    intro y huy
    exact hp.start_uncovered (by simpa [hM.support_eq_verts] using huy.fst_mem)
  have hend_uncovered : ∀ y, ¬ M.Adj v y := by
    intro y hvy
    exact hp.end_uncovered (by simpa [hM.support_eq_verts] using hvy.fst_mem)
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxInf : x ∈ (augment_matching M p).verts ∩ p.toSubgraph.verts := by
      simpa [Subgraph.verts_inf] using hx
    by_cases hxu : x = u
    · subst x
      have huPath : p.toSubgraph.Adj u p.snd := p.toSubgraph_adj_snd hp.not_nil
      have huAug : (augment_matching M p).Adj u p.snd := by
        change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj u p.snd
        exact Or.inr ⟨huPath, hstart_uncovered _⟩
      refine ⟨p.snd, ?_, ?_⟩
      · -- The first augmented edge lies on the path and is unique at the start vertex.
        exact ⟨huAug, huPath⟩
      · intro w hw
        exact (hAug.eq_of_adj_left (u := u) (v := p.snd) (w := w) huAug hw.1).symm
    by_cases hxv : x = v
    · subst x
      have hvPath : p.toSubgraph.Adj v p.penultimate :=
        (p.toSubgraph_adj_penultimate hp.not_nil).symm
      have hvAug : (augment_matching M p).Adj v p.penultimate := by
        change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj v p.penultimate
        exact Or.inr ⟨hvPath, hend_uncovered _⟩
      refine ⟨p.penultimate, ?_, ?_⟩
      · -- The last augmented edge lies on the path and is unique at the end vertex.
        exact ⟨hvAug, hvPath⟩
      · intro w hw
        exact (hAug.eq_of_adj_left (u := v) (v := p.penultimate) (w := w) hvAug hw.1).symm
    have hxSupport : x ∈ p.support := p.mem_verts_toSubgraph.mp hxInf.2
    obtain ⟨i, hi0, hil, hxi⟩ :=
      existsInternalIndex_of_mem_support_ne_endpoints hpPath hxSupport hxu hxv
    have hprev : p.toSubgraph.Adj x (p.getVert (i - 1)) := by
      have hmem : p.getVert (i - 1) ∈ p.toSubgraph.neighborSet x := by
        rw [hxi, hpPath.neighborSet_toSubgraph_internal (by omega) hil]
        simp
      exact (p.toSubgraph.mem_neighborSet _ _).1 hmem
    have hnext : p.toSubgraph.Adj x (p.getVert (i + 1)) := by
      have hmem : p.getVert (i + 1) ∈ p.toSubgraph.neighborSet x := by
        rw [hxi, hpPath.neighborSet_toSubgraph_internal (by omega) hil]
        simp
      exact (p.toSubgraph.mem_neighborSet _ _).1 hmem
    have hprev_ne_next : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
      intro hEq
      have := hpPath.getVert_injOn (by simp; omega) (by simp; omega) hEq
      omega
    have hAlt_local :
        M.Adj x (p.getVert (i - 1)) ↔ ¬ M.Adj x (p.getVert (i + 1)) := by
      simpa [Subgraph.spanningCoe_adj, hxi] using hpAlt hprev_ne_next hprev hnext
    by_cases hMatchedPrev : M.Adj x (p.getVert (i - 1))
    · have hNotMatchedNext : ¬ M.Adj x (p.getVert (i + 1)) := hAlt_local.mp hMatchedPrev
      have hAugNext : (augment_matching M p).Adj x (p.getVert (i + 1)) := by
        change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x (p.getVert (i + 1))
        simp [symmDiff_def, Subgraph.spanningCoe_adj, hnext, hNotMatchedNext]
      refine ⟨p.getVert (i + 1), ?_, ?_⟩
      · exact ⟨hAugNext, hnext⟩
      · intro w hw
        exact
          (hAug.eq_of_adj_left (u := x) (v := p.getVert (i + 1)) (w := w) hAugNext hw.1).symm
    · have hMatchedNext : M.Adj x (p.getVert (i + 1)) := by
        by_contra hNotMatchedNext
        exact hMatchedPrev (hAlt_local.mpr hNotMatchedNext)
      have hAugPrev : (augment_matching M p).Adj x (p.getVert (i - 1)) := by
        change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x (p.getVert (i - 1))
        simp [symmDiff_def, Subgraph.spanningCoe_adj, hprev, hMatchedPrev]
      refine ⟨p.getVert (i - 1), ?_, ?_⟩
      · exact ⟨hAugPrev, hprev⟩
      · intro w hw
        exact
          (hAug.eq_of_adj_left (u := x) (v := p.getVert (i - 1)) (w := w) hAugPrev hw.1).symm
  · ext x
    constructor
    · intro hx
      have hxInf : x ∈ (augment_matching M p).verts ∩ p.toSubgraph.verts := by
        simpa [Subgraph.verts_inf] using hx
      exact hxInf.2
    · intro hxPath
      by_cases hxu : x = u
      · subst x
        have huAug : (augment_matching M p).Adj u p.snd := by
          -- The first path edge is toggled in because the start vertex is uncovered in `M`.
          change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj u p.snd
          have huPath : p.toSubgraph.Adj u p.snd := p.toSubgraph_adj_snd hp.not_nil
          exact Or.inr ⟨huPath, hstart_uncovered _⟩
        have huAugVert : u ∈ (augment_matching M p).verts := by
          simpa [hAug.support_eq_verts] using
            (Subgraph.mem_support (augment_matching M p)).2 ⟨p.snd, huAug⟩
        -- The augmented matching now covers the start vertex by a path edge.
        simpa [Subgraph.verts_inf] using And.intro huAugVert p.start_mem_verts_toSubgraph
      by_cases hxv : x = v
      · subst x
        have hvAug : (augment_matching M p).Adj v p.penultimate := by
          -- The last path edge is toggled in because the endpoint is uncovered in `M`.
          change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj v p.penultimate
          have hvPath : p.toSubgraph.Adj v p.penultimate :=
            (p.toSubgraph_adj_penultimate hp.not_nil).symm
          exact Or.inr ⟨hvPath, hend_uncovered _⟩
        have hvAugVert : v ∈ (augment_matching M p).verts := by
          simpa [hAug.support_eq_verts] using
            (Subgraph.mem_support (augment_matching M p)).2 ⟨p.penultimate, hvAug⟩
        -- The augmented matching now covers the end vertex by a path edge.
        simpa [Subgraph.verts_inf] using And.intro hvAugVert p.end_mem_verts_toSubgraph
      have hxSupport : x ∈ p.support := p.mem_verts_toSubgraph.mp hxPath
      obtain ⟨i, hi0, hil, hxi⟩ :=
        existsInternalIndex_of_mem_support_ne_endpoints hpPath hxSupport hxu hxv
      have hprev : p.toSubgraph.Adj x (p.getVert (i - 1)) := by
        have hmem : p.getVert (i - 1) ∈ p.toSubgraph.neighborSet x := by
          rw [hxi, hpPath.neighborSet_toSubgraph_internal (by omega) hil]
          simp
        exact (p.toSubgraph.mem_neighborSet _ _).1 hmem
      have hnext : p.toSubgraph.Adj x (p.getVert (i + 1)) := by
        have hmem : p.getVert (i + 1) ∈ p.toSubgraph.neighborSet x := by
          rw [hxi, hpPath.neighborSet_toSubgraph_internal (by omega) hil]
          simp
        exact (p.toSubgraph.mem_neighborSet _ _).1 hmem
      have hprev_ne_next : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
        intro hEq
        have := hpPath.getVert_injOn (by simp; omega) (by simp; omega) hEq
        omega
      have hAlt_local :
          M.Adj x (p.getVert (i - 1)) ↔ ¬ M.Adj x (p.getVert (i + 1)) := by
        simpa [Subgraph.spanningCoe_adj, hxi] using hpAlt hprev_ne_next hprev hnext
      have hxAugSupport : x ∈ (augment_matching M p).support := by
        by_cases hMatchedPrev : M.Adj x (p.getVert (i - 1))
        · have hNotMatchedNext : ¬ M.Adj x (p.getVert (i + 1)) := hAlt_local.mp hMatchedPrev
          have hAugNext : (augment_matching M p).Adj x (p.getVert (i + 1)) := by
            change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x (p.getVert (i + 1))
            simp [symmDiff_def, Subgraph.spanningCoe_adj, hnext, hNotMatchedNext]
          exact (Subgraph.mem_support (augment_matching M p)).2 ⟨p.getVert (i + 1), hAugNext⟩
        · have hMatchedNext : M.Adj x (p.getVert (i + 1)) := by
            by_contra hNotMatchedNext
            exact hMatchedPrev (hAlt_local.mpr hNotMatchedNext)
          have hAugPrev : (augment_matching M p).Adj x (p.getVert (i - 1)) := by
            change (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj x (p.getVert (i - 1))
            simp [symmDiff_def, Subgraph.spanningCoe_adj, hprev, hMatchedPrev]
          exact (Subgraph.mem_support (augment_matching M p)).2 ⟨p.getVert (i - 1), hAugPrev⟩
      have hxAugVert : x ∈ (augment_matching M p).verts := by
        simpa [hAug.support_eq_verts] using hxAugSupport
      -- Each internal path vertex keeps exactly the opposite path edge after toggling.
      simpa [Subgraph.verts_inf] using And.intro hxAugVert hxPath

/-- Definition 4.4.1-extra-1 (5): Augmenting a matching along an augmenting path increases the
number of matched edges by exactly one. -/
theorem ncard_edgeSet_augment_matching {M : G.Subgraph} {p : G.Walk u v} [Finite V]
    (hM : M.IsMatching) (hp : IsMatchingAugmenting M p) :
    (augment_matching M p).edgeSet.ncard = M.edgeSet.ncard + 1 := by
  classical
  let Kold : G.Subgraph := M ⊓ p.toSubgraph
  let Knew : G.Subgraph := augment_matching M p ⊓ p.toSubgraph
  obtain ⟨hKoldMatch, hKoldVerts⟩ := oldPathPiece_isMatching_and_verts (M := M) (p := p) hM hp
  obtain ⟨hKnewMatch, hKnewVerts⟩ := newPathPiece_isMatching_and_verts (M := M) (p := p) hM hp
  have hKoldCount : Kold.verts.ncard = 2 * Kold.edgeSet.ncard := by
    simpa [Kold] using matchingVertsNcard_eq_twoMulEdgeSetNcard (K := Kold) hKoldMatch
  have hKnewCount : Knew.verts.ncard = 2 * Knew.edgeSet.ncard := by
    simpa [Knew] using matchingVertsNcard_eq_twoMulEdgeSetNcard (K := Knew) hKnewMatch
  let hpPath : p.IsPath := hp.toIsMatchingAlternating.isPath
  have huv : u ≠ v := by
    intro huvEq
    have hlen : 0 < p.length := Walk.not_nil_iff_lt_length.mp hp.not_nil
    have hidx : (0 : ℕ) = p.length := by
      apply hpPath.getVert_injOn
      · simp [Set.mem_setOf_eq]
      · simp [Set.mem_setOf_eq]
      · calc
          p.getVert 0 = u := p.getVert_zero
          _ = v := huvEq
          _ = p.getVert p.length := p.getVert_length.symm
    omega
  have hpair_subset : ({u, v} : Set V) ⊆ p.toSubgraph.verts := by
    intro x hx
    have hx' : x = u ∨ x = v := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    rcases hx' with rfl | rfl
    · exact p.start_mem_verts_toSubgraph
    · exact p.end_mem_verts_toSubgraph
  have hVertsJump : Kold.verts.ncard + 2 = Knew.verts.ncard := by
    -- The augmented path piece picks up exactly the two uncovered endpoints.
    calc
      Kold.verts.ncard + 2 = (p.toSubgraph.verts \ {u, v}).ncard + ({u, v} : Set V).ncard := by
        rw [hKoldVerts, Set.ncard_pair huv]
      _ = p.toSubgraph.verts.ncard := Set.ncard_diff_add_ncard_of_subset hpair_subset
      _ = Knew.verts.ncard := by rw [hKnewVerts]
  have hPathEdges : Knew.edgeSet.ncard = Kold.edgeSet.ncard + 1 := by
    -- Converting the vertex jump through the matching-count lemma yields one extra path edge.
    omega
  have hMdecomp : Kold.edgeSet.ncard + (M.edgeSet \ p.edgeSet).ncard = M.edgeSet.ncard := by
    -- Split the original matching into its on-path and off-path parts.
    simpa [Kold, Walk.edgeSet_toSubgraph] using
      (Set.ncard_inter_add_ncard_diff_eq_ncard M.edgeSet p.edgeSet)
  have hAugdecomp :
      Knew.edgeSet.ncard + ((augment_matching M p).edgeSet \ p.edgeSet).ncard =
        (augment_matching M p).edgeSet.ncard := by
    -- Split the augmented matching the same way and then compare the off-path part.
    simpa [Knew, Walk.edgeSet_toSubgraph] using
      (Set.ncard_inter_add_ncard_diff_eq_ncard (augment_matching M p).edgeSet p.edgeSet)
  have hOffPath :
      (augment_matching M p).edgeSet \ p.edgeSet = M.edgeSet \ p.edgeSet := by
    -- Route correction: compare the off-path edge sets directly after normalizing the symmetric
    -- difference on edge sets instead of chasing support facts through `spanningCoe`.
    ext e
    refine Sym2.ind ?_ e
    intro x y
    by_cases hxy : s(x, y) ∈ p.edgeSet
    · simp [hxy, augmentMatching_edgeSet_eq_symmDiff, symmDiff_def]
    · simp [hxy, augmentMatching_edgeSet_eq_symmDiff, symmDiff_def]
  have hAugdecomp' :
      (augment_matching M p).edgeSet.ncard =
        Knew.edgeSet.ncard + (M.edgeSet \ p.edgeSet).ncard := by
    rw [← hAugdecomp, hOffPath]
  have hMdecomp' : M.edgeSet.ncard = Kold.edgeSet.ncard + (M.edgeSet \ p.edgeSet).ncard := by
    exact hMdecomp.symm
  -- The path piece gains one edge and the off-path piece is unchanged.
  omega

end Walk
end SimpleGraph
