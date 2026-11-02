import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_1.ch4_sec4_4_1_definition_4_4_1_extra_1

namespace SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

open scoped symmDiff
open Walk (IsMatchingAugmenting)

namespace Subgraph

/-- Helper for Theorem 4.20: membership in the symmetric difference of two spanning subgraphs means
that exactly one of the two matchings contains the edge. -/
lemma mem_symmDiff_spanningCoe_iff {M N : Subgraph G} {v w : V} :
    s(v, w) ∈ M.spanningCoe.edgeSet ∆ N.spanningCoe.edgeSet ↔
      (M.Adj v w ∨ N.Adj v w) ∧ ¬ (M.Adj v w ∧ N.Adj v w) := by
  -- Expand the symmetric-difference edge predicate to the xor description used in the source proof.
  constructor
  · intro h
    simp [symmDiff_def, Subgraph.mem_edgeSet] at h
    rcases h with ⟨hMvw, hNvw⟩ | ⟨hNvw, hMvw⟩
    · exact ⟨Or.inl hMvw, fun hBoth ↦ hNvw hBoth.2⟩
    · exact ⟨Or.inr hNvw, fun hBoth ↦ hMvw hBoth.1⟩
  · intro h
    rcases h.1 with hMvw | hNvw
    · exact Or.inl ⟨hMvw, fun hNvw ↦ h.2 ⟨hMvw, hNvw⟩⟩
    · exact Or.inr ⟨hNvw, fun hMvw ↦ h.2 ⟨hMvw, hNvw⟩⟩

/-- Helper for Theorem 4.20: the symmetric difference of two matchings is alternating with
respect to the first matching. -/
lemma matching_symmDiff_is_alternating {M N : Subgraph G}
    (hM : M.IsMatching) (hN : N.IsMatching) :
    (M.spanningCoe ∆ N.spanningCoe).IsAlternating M.spanningCoe := by
  intro v w w' hww' hvw hvw'
  -- Two distinct symmetric-difference neighbors of one vertex cannot both come from the same
  -- matching, because matchings give each vertex a unique incident edge.
  have hxor : (M.Adj v w ∨ N.Adj v w) ∧ ¬ (M.Adj v w ∧ N.Adj v w) := by
    simpa [Subgraph.mem_edgeSet] using
      (mem_symmDiff_spanningCoe_iff (M := M) (N := N) (v := v) (w := w)).mp hvw
  have hxor' : (M.Adj v w' ∨ N.Adj v w') ∧ ¬ (M.Adj v w' ∧ N.Adj v w') := by
    simpa [Subgraph.mem_edgeSet] using
      (mem_symmDiff_spanningCoe_iff (M := M) (N := N) (v := v) (w := w')).mp hvw'
  have hM_iff : M.Adj v w ↔ ¬ M.Adj v w' := by
    constructor
    · intro hMv
      intro hMw'
      exact hww' (hM.eq_of_adj_left hMv hMw')
    · intro hnot
      rcases hxor.1 with hMv | hNv
      · exact hMv
      · exfalso
        have hNw' : ¬ N.Adj v w' := by
          intro hNw'
          exact hww' (hN.eq_of_adj_left hNv hNw')
        rcases hxor'.1 with hMw' | hNalt
        · exact hnot hMw'
        · exact hNw' hNalt
  simpa [Subgraph.spanningCoe_adj] using hM_iff

/-- Helper for Theorem 4.20: every vertex of the symmetric difference of two matchings has at most
two neighbors. -/
lemma matching_symmDiff_neighborSet_ncard_le_two [Finite V] {M N : Subgraph G}
    (hM : M.IsMatching) (hN : N.IsMatching) (v : V) :
    ((M.spanningCoe ∆ N.spanningCoe).neighborSet v).ncard ≤ 2 := by
  classical
  by_contra hgt
  have hthree : 2 < ((M.spanningCoe ∆ N.spanningCoe).neighborSet v).ncard := by
    exact lt_of_not_ge hgt
  obtain ⟨w, hw, w', hw', z, hz, hww', hwz, hw'z⟩ :=
    (Set.two_lt_ncard (s := (M.spanningCoe ∆ N.spanningCoe).neighborSet v)).mp hthree
  have halt := matching_symmDiff_is_alternating (M := M) (N := N) hM hN
  have hmww' : M.spanningCoe.Adj v w ↔ ¬ M.spanningCoe.Adj v w' := halt hww' hw hw'
  have hmwz : M.spanningCoe.Adj v w ↔ ¬ M.spanningCoe.Adj v z := halt hwz hw hz
  have hmw'z : M.spanningCoe.Adj v w' ↔ ¬ M.spanningCoe.Adj v z := halt hw'z hw' hz
  by_cases hMw : M.spanningCoe.Adj v w
  · have hMw' : ¬ M.spanningCoe.Adj v w' := (hmww'.mp hMw)
    have hMz : ¬ M.spanningCoe.Adj v z := (hmwz.mp hMw)
    have hMw'' : M.spanningCoe.Adj v w' := hmw'z.mpr hMz
    exact hMw' hMw''
  · have hMw' : M.spanningCoe.Adj v w' := by
      by_contra hMw''
      exact hMw (hmww'.mpr hMw'')
    have hMz : M.spanningCoe.Adj v z := by
      by_contra hMz'
      exact hMw (hmwz.mpr hMz')
    exact hw'z (hM.eq_of_adj_left hMw' hMz)

/-- Helper for Theorem 4.20: a matching covers exactly twice as many vertices as it has edges. -/
lemma matching_verts_ncard_eq_two_mul_edgeSet_ncard [Finite V] {K : Subgraph G}
    (hK : K.IsMatching) :
    K.verts.ncard = 2 * K.edgeSet.ncard := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  -- On a matching, each covered vertex has degree `1` and each uncovered vertex has degree `0`.
  have hdeg : ∀ v : V, K.spanningCoe.degree v = if v ∈ K.verts then 1 else 0 := by
    intro v
    by_cases hv : v ∈ K.verts
    · have hdegK : K.degree v = 1 :=
        (SimpleGraph.Subgraph.isMatching_iff_forall_degree (M := K)).mp hK v hv
      simp [hv, Subgraph.degree_spanningCoe, hdegK]
    · have hdegK : K.degree v = 0 := K.degree_of_notMem_verts hv
      simp [hv, Subgraph.degree_spanningCoe, hdegK]
  have hsum : Fintype.card K.verts = 2 * Fintype.card K.spanningCoe.edgeSet := by
    -- Summing the degree function counts exactly the covered vertices, then the handshaking lemma
    -- converts the total degree into twice the number of matching edges.
    calc
      Fintype.card K.verts = ∑ v : V, K.spanningCoe.degree v := by
        rw [Fintype.card_subtype]
        rw [Finset.card_eq_sum_ones]
        simpa [hdeg]
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

/-- Helper for Theorem 4.20: augmenting along an augmenting path yields a larger matching of `G`. -/
lemma exists_larger_matching_of_augmenting_path [Finite V] {M : Subgraph G} (hM : M.IsMatching)
    {u v : V} {p : G.Walk u v} (hp : IsMatchingAugmenting M p) :
    ∃ N : Subgraph G, N.IsMatching ∧ M.edgeSet.ncard < N.edgeSet.ncard := by
  let N := Walk.augment_matching M p
  have hN : N.IsMatching := Walk.augment_matching_isMatching hM hp
  have hcard : N.edgeSet.ncard = M.edgeSet.ncard + 1 := by
    simpa [N] using Walk.ncard_edgeSet_augment_matching (M := M) (p := p) hM hp
  refine ⟨N, hN, ?_⟩
  -- The augmented matching has exactly one more edge, hence in particular strictly more edges.
  omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_4_1/ch4_sec4_4_1_theorem_4_20.lean: a strict
cardinality imbalance is witnessed inside one connected component of a finite graph. -/
lemma existsComponentWithNcardImbalance [Finite V] (H : SimpleGraph V) {A B : Set V}
    (hBA : B.ncard < A.ncard) :
    ∃ c : H.ConnectedComponent, (B ∩ c.supp).ncard < (A ∩ c.supp).ncard := by
  classical
  -- Local instance justification (finite enumeration): the component-cardinality decomposition
  -- is expressed as a finite sum over all connected components.
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  have hpair (S : Set V) :
      Pairwise fun c d : H.ConnectedComponent ↦ Disjoint (S ∩ c.supp) (S ∩ d.supp) := by
    intro c d hcd
    exact (H.pairwise_disjoint_supp_connectedComponent hcd).mono
      Set.inter_subset_right Set.inter_subset_right
  have hunion (S : Set V) : ⋃ c : H.ConnectedComponent, S ∩ c.supp = S := by
    -- Intersecting the component partition with `S` partitions `S` itself.
    rw [← Set.inter_iUnion, H.iUnion_connectedComponentSupp, Set.inter_univ]
  have hncard (S : Set V) : S.ncard = ∑ c : H.ConnectedComponent, (S ∩ c.supp).ncard := by
    -- Pairwise disjointness turns the component partition into an exact cardinality sum.
    rw [← finsum_eq_sum_of_fintype, ← Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _)
      (hpair S), hunion]
  rw [hncard B, hncard A] at hBA
  obtain ⟨c, -, hc⟩ := Finset.exists_lt_of_sum_lt hBA
  exact ⟨c, hc⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_4_1/ch4_sec4_4_1_theorem_4_20.lean: at an
internal vertex of a path, a degree-two upper bound makes the ambient and path neighbor sets
equal. -/
lemma neighborSetEqToSubgraphOfInternalVertex [Finite V] {H : SimpleGraph V}
    (hdeg : ∀ x : V, (H.neighborSet x).ncard ≤ 2) {u v x : V} {p : H.Walk u v}
    (hp : p.IsPath) (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v) :
    H.neighborSet x = p.toSubgraph.neighborSet x := by
  obtain ⟨i, hi0, hil, hxi⟩ :=
    Walk.existsInternalIndex_of_mem_support_ne_endpoints hp hx hxu hxv
  have hpathCard : (p.toSubgraph.neighborSet x).ncard = 2 := by
    rw [hxi, hp.ncard_neighborSet_toSubgraph_internal_eq_two (by omega) hil]
  -- The two path neighbors already exhaust the ambient degree bound.
  exact (Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset x)
    (by simpa [hpathCard] using hdeg x)).symm

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_4_1/ch4_sec4_4_1_theorem_4_20.lean: in a finite
graph of maximum degree two, a path maximal from a leaf spans that leaf's component and ends at
another leaf. -/
lemma existsSpanningPathFromSingletonNeighbor [Finite V] {H : SimpleGraph V}
    (hdeg : ∀ x : V, (H.neighborSet x).ncard ≤ 2) {u w : V}
    (huw : H.neighborSet u = {w}) :
    ∃ (v : V) (p : H.Walk u v), p.IsPath ∧ ¬ p.Nil ∧
      p.toSubgraph.verts = (H.connectedComponentMk u).supp ∧
      H.neighborSet v = {p.penultimate} := by
  classical
  let lengths : Set ℕ :=
    {n | ∃ (v : V) (p : H.Walk u v), p.IsPath ∧ p.length = n}
  have hlengthsFinite : lengths.Finite :=
    Set.Finite.subset (Set.finite_le_nat H.edgeFinset.card) fun n ⟨v, p, hp, hn⟩ ↦ by
      rw [← hn]
      exact hp.isTrail.length_le_card_edgeFinset
  obtain ⟨maxLength, ⟨⟨v, p, hp, hpLength⟩, hmax⟩⟩ :=
    hlengthsFinite.exists_maximal ⟨0, u, .nil, by simp⟩
  have hmaxPath {v' : V} (p' : H.Walk u v') (hp' : p'.IsPath) :
      p'.length ≤ p.length := by
    rw [hpLength]
    by_contra hle
    have hlt : maxLength < p'.length := Nat.lt_of_not_ge hle
    exact (Nat.not_le_of_gt hlt) (hmax ⟨v', p', hp', rfl⟩ hlt.le)
  have huwAdj : H.Adj u w := by
    have : w ∈ H.neighborSet u := by rw [huw]; simp
    exact this
  have hpNotNil : ¬ p.Nil := by
    intro hpNil
    have hshort := hmaxPath huwAdj.toWalk (Walk.IsPath.of_adj huwAdj)
    have hone : 1 ≤ p.length := by simpa using hshort
    have hpLengthZero : p.length = 0 := hpNil.length_eq_zero
    omega
  have hpSnd : p.snd = w := by
    have hsnd : p.snd ∈ H.neighborSet u := p.adj_snd hpNotNil
    rw [huw] at hsnd
    simpa using hsnd
  have hclosed : ∀ x ∈ p.support, ∀ y, H.Adj x y → y ∈ p.support := by
    intro x hx y hxy
    by_cases hxu : x = u
    · subst x
      have hy : y ∈ H.neighborSet u := hxy
      rw [huw] at hy
      have hyw : y = w := by simpa using hy
      rw [hyw, ← hpSnd]
      exact p.getVert_mem_support 1
    by_cases hxv : x = v
    · subst x
      by_contra hy
      have hlong := hmaxPath (p.concat hxy) (hp.concat hy hxy)
      rw [p.length_concat] at hlong
      omega
    · have hneighbors := neighborSetEqToSubgraphOfInternalVertex hdeg hp hx hxu hxv
      have hyPath : y ∈ p.toSubgraph.neighborSet x := by
        rw [← hneighbors]
        exact hxy
      exact p.mem_verts_toSubgraph.mp (p.toSubgraph.neighborSet_subset_verts x hyPath)
  have hverts : p.toSubgraph.verts = (H.connectedComponentMk u).supp := by
    ext x
    constructor
    · intro hx
      have hxSupport : x ∈ p.support := p.mem_verts_toSubgraph.mp hx
      have hreach : H.Reachable u x := (p.takeUntil x hxSupport).reachable
      exact ConnectedComponent.sound hreach |>.symm
    · intro hx
      have hreach : H.Reachable u x :=
        (H.connectedComponentMk u).reachable_of_mem_supp
          ConnectedComponent.connectedComponentMk_mem hx
      let P : H.Subgraph := (⊤ : H.Subgraph).induce {x | x ∈ p.support}
      have huP : u ∈ P.verts := by simp [P, p.start_mem_support]
      have hclosure : ∀ z ∈ P.verts, ∀ y, H.Adj z y → P.Adj z y := by
        intro z hz y hzy
        have hzSupport : z ∈ p.support := by simpa [P] using hz
        exact ⟨hzSupport, hclosed z hzSupport y hzy, hzy⟩
      have hxP : x ∈ P.verts := hreach.mem_subgraphVerts hclosure huP
      exact p.mem_verts_toSubgraph.mpr (by simpa [P] using hxP)
  have hendNeighbors : H.neighborSet v = {p.penultimate} := by
    ext x
    constructor
    · intro hx
      have hxAdj : H.Adj v x := hx
      have hxSupport : x ∈ p.support := hclosed v p.end_mem_support x hxAdj
      by_cases hxu : x = u
      · subst x
        have hvSnd : v = p.snd := by
          have hv : v ∈ H.neighborSet u := hxAdj.symm
          rw [huw] at hv
          have hvw : v = w := by simpa using hv
          exact hvw.trans hpSnd.symm
        have hvPath : p.toSubgraph.Adj v u := by
          simpa only [hvSnd] using (p.toSubgraph_adj_snd hpNotNil).symm
        have hvPathReverse : p.reverse.toSubgraph.Adj v u := by
          rw [Walk.toSubgraph_reverse]
          exact hvPath
        have hpen : p.penultimate = u := by
          simpa [Walk.snd_reverse] using hp.reverse.snd_of_toSubgraph_adj hvPathReverse
        simpa [hpen]
      · have hxv : x ≠ v := by
          intro hxv
          subst x
          exact H.loopless.irrefl v hxAdj
        have hneighbors :=
          neighborSetEqToSubgraphOfInternalVertex hdeg hp hxSupport hxu hxv
        have hxPath : p.toSubgraph.Adj v x := by
          have : v ∈ H.neighborSet x := hxAdj.symm
          rw [hneighbors] at this
          exact this.symm
        have hxPathReverse : p.reverse.toSubgraph.Adj v x := by
          rw [Walk.toSubgraph_reverse]
          exact hxPath
        have hpen : p.penultimate = x := by
          simpa [Walk.snd_reverse] using hp.reverse.snd_of_toSubgraph_adj hxPathReverse
        simpa [hpen]
    · intro hx
      have hpen : x = p.penultimate := by simpa using hx
      subst x
      exact (p.toSubgraph_adj_penultimate hpNotNil).symm.adj_sub
  exact ⟨v, p, hp, hpNotNil, hverts, hendNeighbors⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_4_1/ch4_sec4_4_1_theorem_4_20.lean: every
internal vertex of a path in the symmetric difference of two matchings is covered by both
matchings. -/
lemma memBothVertsOfInternalSymmDiffPath {M N : Subgraph G} (hM : M.IsMatching)
    (hN : N.IsMatching) {u v x : V}
    {p : (M.spanningCoe ∆ N.spanningCoe).Walk u v} (hp : p.IsPath)
    (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v) :
    x ∈ M.verts ∧ x ∈ N.verts := by
  obtain ⟨i, hi0, hil, hxi⟩ :=
    Walk.existsInternalIndex_of_mem_support_ne_endpoints hp hx hxu hxv
  have hprev : (M.spanningCoe ∆ N.spanningCoe).Adj x (p.getVert (i - 1)) := by
    have hmem : p.getVert (i - 1) ∈ p.toSubgraph.neighborSet x := by
      rw [hxi, hp.neighborSet_toSubgraph_internal (by omega) hil]
      simp
    exact (p.toSubgraph.mem_neighborSet _ _).mp hmem |>.adj_sub
  have hnext : (M.spanningCoe ∆ N.spanningCoe).Adj x (p.getVert (i + 1)) := by
    have hmem : p.getVert (i + 1) ∈ p.toSubgraph.neighborSet x := by
      rw [hxi, hp.neighborSet_toSubgraph_internal (by omega) hil]
      simp
    exact (p.toSubgraph.mem_neighborSet _ _).mp hmem |>.adj_sub
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro heq
    have hi := hp.getVert_injOn (by simp; omega) (by simp; omega) heq
    omega
  have halt := matching_symmDiff_is_alternating (M := M) (N := N) hM hN hne hprev hnext
  have hprevXor := (mem_symmDiff_spanningCoe_iff (M := M) (N := N)).mp
    (by simpa [Subgraph.mem_edgeSet] using hprev)
  have hnextXor := (mem_symmDiff_spanningCoe_iff (M := M) (N := N)).mp
    (by simpa [Subgraph.mem_edgeSet] using hnext)
  -- Alternation selects the `M`-edge; the xor descriptions put the other edge in `N`.
  by_cases hMprev : M.Adj x (p.getVert (i - 1))
  · have hMnext : ¬ M.Adj x (p.getVert (i + 1)) := halt.mp hMprev
    have hNnext : N.Adj x (p.getVert (i + 1)) := by
      rcases hnextXor.1 with hMnext' | hNnext
      · exact (hMnext hMnext').elim
      · exact hNnext
    exact ⟨M.edge_vert hMprev, N.edge_vert hNnext⟩
  · have hMnext : M.Adj x (p.getVert (i + 1)) := by
      by_contra hMnext
      exact hMprev (halt.mpr hMnext)
    have hNprev : N.Adj x (p.getVert (i - 1)) := by
      rcases hprevXor.1 with hMprev' | hNprev
      · exact (hMprev hMprev').elim
      · exact hNprev
    exact ⟨M.edge_vert hMnext, N.edge_vert hNprev⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_4_1/ch4_sec4_4_1_theorem_4_20.lean: a vertex
with a singleton neighborhood in the symmetric difference of two matchings is covered by exactly
one matching. -/
lemma endpointMemDiffOfSingletonSymmDiffNeighbor {M N : Subgraph G} (hM : M.IsMatching)
    (hN : N.IsMatching) {x y : V}
    (hneighbors : (M.spanningCoe ∆ N.spanningCoe).neighborSet x = {y}) :
    x ∈ M.verts \ N.verts ∨ x ∈ N.verts \ M.verts := by
  have hxy : (M.spanningCoe ∆ N.spanningCoe).Adj x y := by
    have : y ∈ (M.spanningCoe ∆ N.spanningCoe).neighborSet x := by
      rw [hneighbors]
      simp
    exact this
  have hxor := (mem_symmDiff_spanningCoe_iff (M := M) (N := N)).mp
    (by simpa [Subgraph.mem_edgeSet] using hxy)
  rcases hxor.1 with hMxy | hNxy
  · refine Or.inl ⟨M.edge_vert hMxy, ?_⟩
    intro hxN
    obtain ⟨z, hNxz, -⟩ := hN hxN
    have hzy : z = y := by
      by_cases hMxz : M.Adj x z
      · exact hM.eq_of_adj_left hMxz hMxy
      · have hHz : (M.spanningCoe ∆ N.spanningCoe).Adj x z := by
          simp [symmDiff_def, Subgraph.spanningCoe_adj, hNxz, hMxz]
        have hz : z ∈ ({y} : Set V) := by
          rw [← hneighbors]
          exact hHz
        simpa using hz
    subst z
    exact hxor.2 ⟨hMxy, hNxz⟩
  · refine Or.inr ⟨N.edge_vert hNxy, ?_⟩
    intro hxM
    obtain ⟨z, hMxz, -⟩ := hM hxM
    have hzy : z = y := by
      by_cases hNxz : N.Adj x z
      · exact hN.eq_of_adj_left hNxz hNxy
      · have hHz : (M.spanningCoe ∆ N.spanningCoe).Adj x z := by
          simp [symmDiff_def, Subgraph.spanningCoe_adj, hMxz, hNxz]
        have hz : z ∈ ({y} : Set V) := by
          rw [← hneighbors]
          exact hHz
        simpa using hz
    subst z
    exact hxor.2 ⟨hMxz, hNxy⟩

/-- Helper for Theorem 4.20: a strictly larger matching should yield an augmenting path via the
textbook symmetric-difference decomposition into paths and cycles. -/
lemma exists_augmenting_path_of_exists_larger_matching [Finite V] {M N : Subgraph G}
    (hM : M.IsMatching) (hN : N.IsMatching) (hMN : M.edgeSet.ncard < N.edgeSet.ncard) :
    ∃ (u v : V) (p : G.Walk u v), IsMatchingAugmenting M p := by
  classical
  -- Follow the source decomposition in the single normal form
  -- `H := M.spanningCoe ∆ N.spanningCoe`.
  let H : SimpleGraph V := M.spanningCoe ∆ N.spanningCoe
  have hHalt : H.IsAlternating M.spanningCoe := by
    simpa [H] using matching_symmDiff_is_alternating (M := M) (N := N) hM hN
  have hHdeg : ∀ v : V, (H.neighborSet v).ncard ≤ 2 := by
    intro v
    simpa [H] using matching_symmDiff_neighborSet_ncard_le_two (M := M) (N := N) hM hN v
  have hMverts : M.verts.ncard = 2 * M.edgeSet.ncard :=
    matching_verts_ncard_eq_two_mul_edgeSet_ncard (K := M) hM
  have hNverts : N.verts.ncard = 2 * N.edgeSet.ncard :=
    matching_verts_ncard_eq_two_mul_edgeSet_ncard (K := N) hN
  have hVertsLt : M.verts.ncard < N.verts.ncard := by
    omega
  have hDiffLt :
      (M.verts \ N.verts).ncard < (N.verts \ M.verts).ncard :=
    (Set.ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff).mp hVertsLt
  obtain ⟨c, hc⟩ := existsComponentWithNcardImbalance H hDiffLt
  have hNOnlyPos : 0 < ((N.verts \ M.verts) ∩ c.supp).ncard :=
    lt_of_le_of_lt (Nat.zero_le _) hc
  obtain ⟨u, hu⟩ := (Set.ncard_pos).mp hNOnlyPos
  obtain ⟨w, hNuw, -⟩ := hN hu.1.1
  have hMnone : ∀ z, ¬ M.Adj u z := by
    intro z hMuz
    exact hu.1.2 (M.edge_vert hMuz)
  have huNeighbors : H.neighborSet u = {w} := by
    ext z
    constructor
    · intro hHz
      have hxor := (mem_symmDiff_spanningCoe_iff (M := M) (N := N)).mp
        (by simpa [H, Subgraph.mem_edgeSet] using hHz)
      rcases hxor.1 with hMuz | hNuz
      · exact (hMnone z hMuz).elim
      · simpa using hN.eq_of_adj_left hNuz hNuw
    · intro hzw
      have hEq : z = w := by simpa using hzw
      subst z
      have hmem := (mem_symmDiff_spanningCoe_iff (M := M) (N := N)).mpr
        ⟨Or.inr hNuw, fun hBoth ↦ hMnone w hBoth.1⟩
      simpa [H, Subgraph.mem_edgeSet] using hmem
  -- The selected `N`-surplus component contains the leaf `u`; a maximal path from it spans the
  -- component and exposes the only other possible exceptional vertex at its far endpoint.
  obtain ⟨v, p, hp, hpNotNil, hpVerts, hvNeighbors⟩ :=
    existsSpanningPathFromSingletonNeighbor hHdeg huNeighbors
  have hcomponent : H.connectedComponentMk u = c := hu.2
  rw [hcomponent] at hpVerts
  have hvExclusive : v ∈ M.verts \ N.verts ∨ v ∈ N.verts \ M.verts := by
    apply endpointMemDiffOfSingletonSymmDiffNeighbor hM hN
    simpa [H] using hvNeighbors
  have hvNOnly : v ∈ N.verts \ M.verts := by
    rcases hvExclusive with hvMOnly | hvNOnly
    · exfalso
      have hNOnlyEq : (N.verts \ M.verts) ∩ c.supp = {u} := by
        apply Set.Subset.antisymm
        · intro x hx
          have hxSupport : x ∈ p.support := by
            apply p.mem_verts_toSubgraph.mp
            rw [hpVerts]
            exact hx.2
          by_cases hxu : x = u
          · simpa [hxu]
          by_cases hxv : x = v
          · subst x
            exact (hvMOnly.2 hx.1.1).elim
          have hBoth : x ∈ M.verts ∧ x ∈ N.verts := by
            apply memBothVertsOfInternalSymmDiffPath hM hN hp hxSupport hxu hxv
          exact (hx.1.2 hBoth.1).elim
        · intro x hx
          have hxu : x = u := by simpa using hx
          subst x
          exact hu
      have hvComponent : v ∈ c.supp := by
        rw [← hpVerts]
        exact p.mem_verts_toSubgraph.mpr p.end_mem_support
      have hMOnlyPos : 0 < ((M.verts \ N.verts) ∩ c.supp).ncard :=
        (Set.ncard_pos).mpr ⟨v, hvMOnly, hvComponent⟩
      rw [hNOnlyEq] at hc
      simp only [Set.ncard_singleton] at hc
      omega
    · exact hvNOnly
  have hHG : H ≤ G := by
    dsimp [H]
    exact symmDiff_le
      (show M.spanningCoe ≤ N.spanningCoe ⊔ G from le_sup_of_le_right M.spanningCoe_le)
      (show N.spanningCoe ≤ M.spanningCoe ⊔ G from le_sup_of_le_right N.spanningCoe_le)
  let q : G.Walk u v := p.mapLe hHG
  have hqPath : q.IsPath := by
    simpa [q] using hp.mapLe hHG
  have hqAlt : q.toSubgraph.spanningCoe.IsAlternating M.spanningCoe := by
    apply hHalt.mono
    intro x y hxy
    have hqxy : q.toSubgraph.Adj x y := by
      simpa [Subgraph.spanningCoe_adj] using hxy
    have hpxy : p.toSubgraph.Adj x y := by
      simpa [q] using (Walk.adj_toSubgraph_mapLe hHG).mp hqxy
    exact hpxy.adj_sub
  have hqMatchingAlt : Walk.IsMatchingAlternating M q := ⟨hqPath, hqAlt⟩
  have hqNotNil : ¬ q.Nil := by
    dsimp [q, Walk.mapLe]
    intro hqNil
    exact hpNotNil (Iff.mp (Walk.nil_map_iff (f := SimpleGraph.Hom.ofLE hHG)) hqNil)
  have huUncovered : u ∉ M.support := by
    simpa [hM.support_eq_verts] using hu.1.2
  have hvUncovered : v ∉ M.support := by
    simpa [hM.support_eq_verts] using hvNOnly.2
  -- Mapping along `H ≤ G` preserves the path and its support, so the endpoint and alternation
  -- facts assemble directly into the required augmenting path.
  exact ⟨u, v, q, hqMatchingAlt, hqNotNil, huUncovered, hvUncovered⟩

/-- A matching of `G` has maximum cardinality when no other matching of `G` uses more edges. -/
@[mk_iff]
structure IsMaximumCardinalityMatching [Finite V] (M : Subgraph G) : Prop where
  isMatching : M.IsMatching
  maximum (N : Subgraph G) (_ : N.IsMatching) : N.edgeSet.ncard ≤ M.edgeSet.ncard

/-- A finite graph admits a maximum-cardinality matching. -/
theorem exists_isMaximumCardinalityMatching [Finite V] :
    ∃ M : G.Subgraph, M.IsMaximumCardinalityMatching := by
  classical
  letI : Fintype G.Subgraph := Fintype.ofFinite _
  have hbot : (⊥ : G.Subgraph).IsMatching := by
    intro v hv
    simp at hv
  let admissible : Finset G.Subgraph :=
    (Finset.univ : Finset G.Subgraph).filter fun M ↦ M.IsMatching
  have hadmissible : admissible.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp [admissible, hbot]
  obtain ⟨M, hMmem, hMmax⟩ :=
    admissible.exists_max_image (fun M ↦ M.edgeSet.ncard) hadmissible
  refine ⟨M, ?_⟩
  refine ⟨(Finset.mem_filter.mp hMmem).2, ?_⟩
  intro N hN
  have hNmem : N ∈ admissible := by
    simp [admissible, hN]
  exact hMmax N hNmem

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_4_1/ch4_sec4_4_1_theorem_4_20.lean

Theorem 4.20. A matching `M` has maximum cardinality if and only if there is no
`M`-augmenting path. -/
theorem matching_has_maximum_cardinality_iff_no_augmenting_path [Finite V] {M : Subgraph G}
    (hM : M.IsMatching) :
    M.IsMaximumCardinalityMatching ↔
      ¬ ∃ (u v : V) (p : G.Walk u v), IsMatchingAugmenting M p := by
  constructor
  · intro hmax hAug
    rcases hAug with ⟨u, v, p, hp⟩
    -- An augmenting path produces a larger matching, contradicting maximality.
    rcases exists_larger_matching_of_augmenting_path hM hp with ⟨N, hN, hlt⟩
    exact Nat.not_lt_of_ge (hmax.maximum N hN) hlt
  · intro hNoAug
    refine ⟨hM, ?_⟩
    intro N hN
    by_contra hle
    have hlt : M.edgeSet.ncard < N.edgeSet.ncard := lt_of_not_ge hle
    -- The source-proof converse extracts an augmenting path from any strictly larger matching.
    exact hNoAug (exists_augmenting_path_of_exists_larger_matching hM hN hlt)

end Subgraph

end SimpleGraph

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_468cd09da0ad5a47a1f3"
#print axioms _root_.SimpleGraph.Subgraph.matching_has_maximum_cardinality_iff_no_augmenting_path
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_468cd09da0ad5a47a1f3"
