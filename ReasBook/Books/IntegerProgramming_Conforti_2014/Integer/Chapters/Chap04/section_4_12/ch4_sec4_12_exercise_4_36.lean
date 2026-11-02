import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_definition_4_10_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10_1.ch4_sec4_10_1_definition_4_10_1_extra_1

noncomputable section

attribute [local instance] Classical.propDecidable

open SimpleGraph
open scoped BigOperators Matrix

private abbrev completeGraph (n : ℕ) : SimpleGraph (Fin n) := ⊤

namespace SimpleGraph

/-- Helper for Exercise 4.36: the `0,1` incidence vector of a subgraph in the ambient edge
coordinates of `G`. -/
private def subgraphIncidenceVector {V : Type*} {G : SimpleGraph V}
    (R : Type*) [Zero R] [One R] (M : G.Subgraph) : G.edgeSet → R :=
  fun e ↦ if e.1 ∈ M.edgeSet then 1 else 0

/-- Helper for Exercise 4.36: the cut-edge finset `δ[G] S` in the edge coordinates of `G`. -/
private def cutEdgeFinset {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] (S : Set V) :
    Finset G.edgeSet :=
  Finset.univ.filter fun e ↦ ∃ u ∈ S, ∃ v ∉ S, s(u, v) = (e : Sym2 V)

/-- Helper for Exercise 4.36: membership in `δ[G] S` means one endpoint lies in `S` and the other
lies outside `S`. -/
private theorem mem_cutEdgeFinset_iff {V : Type*} {G : SimpleGraph V} [Fintype G.edgeSet]
    {S : Set V} {e : G.edgeSet} :
    e ∈ cutEdgeFinset G S ↔ ∃ u ∈ S, ∃ v ∉ S, s(u, v) = (e : Sym2 V) := by
  simp [cutEdgeFinset]

end SimpleGraph

notation "δ[" G "] " S:arg => SimpleGraph.cutEdgeFinset G S

private abbrev perfectMatchingVertex (n : ℕ) :=
  {M : (completeGraph n).Subgraph // M.IsPerfectMatching}

private abbrev oddCutFacet (n : ℕ) :=
  {S : Set (Fin n) // Odd S.ncard ∧ 1 < S.ncard ∧ S.ncard < n - 1}

private abbrev perfectMatchingFacetRow (n : ℕ) :=
  (completeGraph n).edgeSet ⊕ oddCutFacet n

private abbrev rowEquiv (n : ℕ) := Fintype.equivFin (perfectMatchingFacetRow n)
private abbrev colEquiv (n : ℕ) := Fintype.equivFin (perfectMatchingVertex n)
private abbrev edgeEquiv (n : ℕ) := Fintype.equivFin ((completeGraph n).edgeSet)

private def perfectMatchingFacetMatrix (n : ℕ) :
    Matrix (Fin (Fintype.card (perfectMatchingFacetRow n)))
      (Fin (Fintype.card ((completeGraph n).edgeSet))) ℝ :=
  fun i j ↦
    match (rowEquiv n).symm i with
    | .inl e => if (edgeEquiv n).symm j = e then -1 else 0
    | .inr S => if (edgeEquiv n).symm j ∈ δ[completeGraph n] S.1 then -1 else 0

private def perfectMatchingFacetBounds (n : ℕ) :
    Fin (Fintype.card (perfectMatchingFacetRow n)) → ℝ :=
  fun i ↦
    match (rowEquiv n).symm i with
    | .inl _ => 0
    | .inr _ => -1

private def perfectMatchingFacetVertices (n : ℕ) :
    Fin (Fintype.card (perfectMatchingVertex n)) →
      Fin (Fintype.card ((completeGraph n).edgeSet)) → ℝ :=
  fun j i ↦
    (completeGraph n).subgraphIncidenceVector ℝ ((colEquiv n).symm j).1 ((edgeEquiv n).symm i)

/-- A bridge/view of the perfect-matching slack matrix for the complete graph on `Fin n`: rows are
the nonnegativity rows and odd-cut rows from the Chapter 4 perfect-matching constraint system,
columns are perfect-matchings of `⊤`, and the matrix itself is expressed through the canonical
owner `slack_matrix`. -/
def completeGraphPerfectMatchingSlackMatrix (n : ℕ) :
    Matrix (Fin (Fintype.card (perfectMatchingFacetRow n)))
      (Fin (Fintype.card (perfectMatchingVertex n))) ℝ :=
  slack_matrix (perfectMatchingFacetMatrix n) (perfectMatchingFacetBounds n)
    (perfectMatchingFacetVertices n)

private def oddCutSlack {n : ℕ} (S : oddCutFacet n) (M : perfectMatchingVertex n) : ℝ :=
  (((δ[completeGraph n] S.1).filter fun e ↦ (e : Sym2 (Fin n)) ∈ M.1.edgeSet).card : ℝ) - 1

private def displayedSlackMatrix (n : ℕ) :
    Matrix (perfectMatchingFacetRow n) (perfectMatchingVertex n) ℝ
  | .inl e, M => if (e : Sym2 (Fin n)) ∈ M.1.edgeSet then 1 else 0
  | .inr S, M => oddCutSlack S M

private lemma cutSum_eq_card {n : ℕ} (S : Set (Fin n)) (M : perfectMatchingVertex n) :
    (δ[completeGraph n] S).sum ((completeGraph n).subgraphIncidenceVector ℝ M.1) =
      (((δ[completeGraph n] S).filter fun e ↦ (e : Sym2 (Fin n)) ∈ M.1.edgeSet).card : ℝ) := by
  let cut :
      Finset (completeGraph n).edgeSet :=
    (δ[completeGraph n] S).filter fun e ↦ (e : Sym2 (Fin n)) ∈ M.1.edgeSet
  let edgeEmbedding : (completeGraph n).edgeSet ↪ Sym2 (Fin n) :=
    ⟨fun e ↦ e, fun _ _ h ↦ Subtype.ext h⟩
  -- Rewrite the cut sum as a `0,1` indicator sum over the same cut-edge finset.
  calc
    (δ[completeGraph n] S).sum ((completeGraph n).subgraphIncidenceVector ℝ M.1) =
        (δ[completeGraph n] S).sum
          (fun e ↦ if (e : Sym2 (Fin n)) ∈ M.1.edgeSet then 1 else 0) := by
      simp [SimpleGraph.subgraphIncidenceVector]
    -- A boolean indicator sum is exactly the cardinality of the filtered cut edges.
    _ = (cut.card : ℝ) := by
      rw [Finset.sum_boole (R := ℝ)
        (p := fun e : (completeGraph n).edgeSet ↦ (e : Sym2 (Fin n)) ∈ M.1.edgeSet)
        (s := δ[completeGraph n] S)]
    -- Map the filtered cut through the canonical edge-to-`Sym2` embedding to match the
    -- normalized odd-cut slack presentation.
    _ = ((cut.map edgeEmbedding).card : ℝ) := by
      rw [Finset.card_map]
    _ = (((δ[completeGraph n] S).filter fun e ↦ (e : Sym2 (Fin n)) ∈ M.1.edgeSet).card : ℝ) := by
      have hmap :
          cut.map edgeEmbedding =
            (do
              let a ← δ[completeGraph n] S
              pure (a : Sym2 (Fin n))).filter fun e ↦ e ∈ M.1.edgeSet := by
        ext e
        simp [cut, edgeEmbedding]
      simpa using congrArg (fun s : Finset (Sym2 (Fin n)) ↦ (s.card : ℝ)) hmap

private lemma one_le_cutCard {n : ℕ} (S : oddCutFacet n) (M : perfectMatchingVertex n) :
    1 ≤ ((δ[completeGraph n] S.1).filter fun e ↦ (e : Sym2 (Fin n)) ∈ M.1.edgeSet).card := by
  by_contra hlt
  have hcard_zero :
      ((δ[completeGraph n] S.1).filter fun e ↦ (e : Sym2 (Fin n)) ∈ M.1.edgeSet).card = 0 := by
    omega
  have hfilter_empty :
      ((SimpleGraph.cutEdgeFinset (completeGraph n) S.1).filter fun e ↦ e.1 ∈ M.1.edgeSet) = ∅ := by
    simpa using Finset.card_eq_zero.mp hcard_zero
  have hno_cut :
      ∀ {e : (completeGraph n).edgeSet},
        e.1 ∈ M.1.edgeSet →
          e ∉ SimpleGraph.cutEdgeFinset (completeGraph n) S.1 := by
    intro e he hedge
    have hmem :
        e ∈
          ((SimpleGraph.cutEdgeFinset (completeGraph n) S.1).filter
            fun e' ↦ e'.1 ∈ M.1.edgeSet) := by
      exact Finset.mem_filter.mpr ⟨hedge, he⟩
    simp [hfilter_empty] at hmem
  have hinduced_match : (M.1.induce S.1).IsMatching := by
    intro v hv
    obtain ⟨w, hvw, huniq⟩ := (Subgraph.isPerfectMatching_iff.mp M.2) v
    have hw_in : w ∈ S.1 := by
      by_contra hw_notin
      let e : (completeGraph n).edgeSet := ⟨s(v, w), M.1.adj_sub hvw⟩
      have hedge : e ∈ SimpleGraph.cutEdgeFinset (completeGraph n) S.1 := by
        rw [SimpleGraph.mem_cutEdgeFinset_iff]
        exact ⟨v, hv, w, hw_notin, rfl⟩
      exact hno_cut (show e.1 ∈ M.1.edgeSet by
          change s(v, w) ∈ M.1.edgeSet
          exact Subgraph.mem_edgeSet.2 hvw) hedge
    refine ⟨w, ?_, ?_⟩
    · exact ⟨hv, hw_in, hvw⟩
    · intro x hx
      exact huniq x hx.2.2
  haveI : Fintype ↑(M.1.induce S.1).verts := Fintype.ofFinite _
  have hEven : Even S.1.ncard := by
    simpa [Subgraph.induce_verts, Set.ncard_eq_toFinset_card'] using hinduced_match.even_card
  exact (Nat.not_even_iff_odd.mpr S.2.1) hEven

private lemma reindexedSlackMatrix_nonnegativity_apply {n : ℕ}
    (e : (completeGraph n).edgeSet) (M : perfectMatchingVertex n) :
    Matrix.reindex (rowEquiv n).symm (colEquiv n).symm
        (completeGraphPerfectMatchingSlackMatrix n) (.inl e) M =
      if (e : Sym2 (Fin n)) ∈ M.1.edgeSet then 1 else 0 := by
  -- Expand the reindexed slack entry and collapse the dot product to the unique edge column.
  calc
    Matrix.reindex (rowEquiv n).symm (colEquiv n).symm
        (completeGraphPerfectMatchingSlackMatrix n) (.inl e) M
      = 0 - (((perfectMatchingFacetMatrix n) *ᵥ
          (perfectMatchingFacetVertices n ((colEquiv n) M))) ((rowEquiv n) (.inl e))) := by
          simp [Matrix.reindex, completeGraphPerfectMatchingSlackMatrix, slack_matrix,
            perfectMatchingFacetBounds]
    _ = if (e : Sym2 (Fin n)) ∈ M.1.edgeSet then 1 else 0 := by
          rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_single (edgeEquiv n e)]
          · by_cases hmem : (e : Sym2 (Fin n)) ∈ M.1.edgeSet
            · simp [perfectMatchingFacetMatrix, perfectMatchingFacetVertices,
                SimpleGraph.subgraphIncidenceVector, hmem]
            · simp [perfectMatchingFacetMatrix, perfectMatchingFacetVertices,
                SimpleGraph.subgraphIncidenceVector, hmem]
          · intro j hj
            have hneq : (edgeEquiv n).symm j ≠ e := by
              intro hje
              apply hj
              simpa using congrArg (edgeEquiv n) hje
            simp [perfectMatchingFacetMatrix, perfectMatchingFacetVertices, hneq]

private lemma reindexedSlackMatrix_oddCut_apply {n : ℕ}
    (S : oddCutFacet n) (M : perfectMatchingVertex n) :
    Matrix.reindex (rowEquiv n).symm (colEquiv n).symm
        (completeGraphPerfectMatchingSlackMatrix n) (.inr S) M =
      oddCutSlack S M := by
  have hmul :
      ((perfectMatchingFacetMatrix n) *ᵥ (perfectMatchingFacetVertices n ((colEquiv n) M)))
          ((rowEquiv n) (.inr S)) =
        -((δ[completeGraph n] S.1).sum ((completeGraph n).subgraphIncidenceVector ℝ M.1)) := by
    -- Reindex the finite sum from `Fin` back to the complete-graph edge coordinates.
    calc
      ((perfectMatchingFacetMatrix n) *ᵥ (perfectMatchingFacetVertices n ((colEquiv n) M)))
          ((rowEquiv n) (.inr S))
        = ∑ j,
            (if (edgeEquiv n).symm j ∈ δ[completeGraph n] S.1 then (-1 : ℝ) else 0) *
              (completeGraph n).subgraphIncidenceVector ℝ M.1 ((edgeEquiv n).symm j) := by
            simp [Matrix.mulVec, dotProduct, perfectMatchingFacetMatrix,
              perfectMatchingFacetVertices]
      _ =
          ∑ j,
            if (edgeEquiv n).symm j ∈ δ[completeGraph n] S.1 then
              -((completeGraph n).subgraphIncidenceVector ℝ M.1 ((edgeEquiv n).symm j))
            else 0 := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hmem : (edgeEquiv n).symm j ∈ δ[completeGraph n] S.1
            · simp [hmem]
            · simp [hmem]
      _ = ∑ e : (completeGraph n).edgeSet,
            if e ∈ δ[completeGraph n] S.1 then
              -((completeGraph n).subgraphIncidenceVector ℝ M.1 e)
            else 0 := by
            exact (Fintype.sum_equiv (edgeEquiv n)
              (fun e : (completeGraph n).edgeSet ↦
                if e ∈ δ[completeGraph n] S.1 then
                  -((completeGraph n).subgraphIncidenceVector ℝ M.1 e)
                else 0)
              (fun j : Fin (Fintype.card ((completeGraph n).edgeSet)) ↦
                if (edgeEquiv n).symm j ∈ δ[completeGraph n] S.1 then
                  -((completeGraph n).subgraphIncidenceVector ℝ M.1 ((edgeEquiv n).symm j))
                else 0)
              (fun e ↦ by simp [edgeEquiv])).symm
      _ = (δ[completeGraph n] S.1).sum
            (fun e ↦ -((completeGraph n).subgraphIncidenceVector ℝ M.1 e)) := by
            simp [Finset.sum_ite_mem]
      _ = -((δ[completeGraph n] S.1).sum ((completeGraph n).subgraphIncidenceVector ℝ M.1)) := by
            rw [Finset.sum_neg_distrib]
  -- Rewrite the odd-cut slack through the cut-sum cardinality identity.
  calc
    Matrix.reindex (rowEquiv n).symm (colEquiv n).symm
        (completeGraphPerfectMatchingSlackMatrix n) (.inr S) M
      = -1 - (((perfectMatchingFacetMatrix n) *ᵥ
          (perfectMatchingFacetVertices n ((colEquiv n) M))) ((rowEquiv n) (.inr S))) := by
          simp [Matrix.reindex, completeGraphPerfectMatchingSlackMatrix, slack_matrix,
            perfectMatchingFacetBounds]
    _ =
        -1 - (-((δ[completeGraph n] S.1).sum
          ((completeGraph n).subgraphIncidenceVector ℝ M.1))) := by
          rw [hmul]
    _ = oddCutSlack S M := by
          rw [oddCutSlack, cutSum_eq_card]
          ring

private theorem displayedSlackMatrix_eq_reindex (n : ℕ) :
    displayedSlackMatrix n =
      Matrix.reindex (rowEquiv n).symm (colEquiv n).symm
        (completeGraphPerfectMatchingSlackMatrix n) := by
  -- Check the two row types separately and use the explicit row formulas above.
  ext row col
  cases row with
  | inl e =>
      exact (reindexedSlackMatrix_nonnegativity_apply e col).symm
  | inr S =>
      exact (reindexedSlackMatrix_oddCut_apply S col).symm

private lemma exists_two_cut_edges_of_oddCutSlack_ne_zero {n : ℕ}
    (S : oddCutFacet n) (M : perfectMatchingVertex n) (hslack : oddCutSlack S M ≠ 0) :
    ∃ e₁ e₂ : (completeGraph n).edgeSet,
      e₁ ≠ e₂ ∧
        (e₁ : Sym2 (Fin n)) ∈ M.1.edgeSet ∧
        (e₂ : Sym2 (Fin n)) ∈ M.1.edgeSet ∧
        e₁ ∈ δ[completeGraph n] S.1 ∧
        e₂ ∈ δ[completeGraph n] S.1 := by
  let cut :
      Finset (Sym2 (Fin n)) :=
    (do
      let a ← δ[completeGraph n] S.1
      pure (a : Sym2 (Fin n))).filter fun e ↦ e ∈ M.1.edgeSet
  have hcut_ge : 1 ≤ cut.card := by
    -- The odd-cut inequalities force at least one matching edge across every odd cut.
    simpa [cut] using one_le_cutCard S M
  have hcut_ne_one : cut.card ≠ 1 := by
    -- A nonzero slack means the filtered cut cardinality is not exactly `1`.
    intro hcard
    apply hslack
    have : (cut.card : ℝ) = 1 := by
      exact_mod_cast hcard
    have hzero : ((cut.card : ℝ) - 1) = 0 := by
      linarith
    simpa [oddCutSlack, cut] using hzero
  have hcut_gt : 1 < cut.card := lt_of_le_of_ne hcut_ge (Ne.symm hcut_ne_one)
  obtain ⟨f₁, hf₁, f₂, hf₂, hne⟩ := Finset.one_lt_card.mp hcut_gt
  have hf₁' :
      f₁ ∈
          (do
            let a ← δ[completeGraph n] S.1
            pure (a : Sym2 (Fin n))) ∧
        f₁ ∈ M.1.edgeSet := by
    simpa [cut] using hf₁
  have hf₂' :
      f₂ ∈
          (do
            let a ← δ[completeGraph n] S.1
            pure (a : Sym2 (Fin n))) ∧
        f₂ ∈ M.1.edgeSet := by
    simpa [cut] using hf₂
  have hf₁'' :
      ∃ e₁ : (completeGraph n).edgeSet,
        e₁ ∈ δ[completeGraph n] S.1 ∧ (e₁ : Sym2 (Fin n)) = f₁ := by
    simpa using hf₁'.1
  have hf₂'' :
      ∃ e₂ : (completeGraph n).edgeSet,
        e₂ ∈ δ[completeGraph n] S.1 ∧ (e₂ : Sym2 (Fin n)) = f₂ := by
    simpa using hf₂'.1
  rcases hf₁'' with ⟨e₁, he₁cut, rfl⟩
  rcases hf₂'' with ⟨e₂, he₂cut, he₂eq⟩
  have hne' : e₁ ≠ e₂ := by
    intro h
    apply hne
    simpa [he₂eq] using congrArg (fun e : (completeGraph n).edgeSet ↦ (e : Sym2 (Fin n))) h
  exact ⟨e₁, e₂, hne', hf₁'.2, by simpa [he₂eq] using hf₂'.2, he₁cut, he₂cut⟩

private lemma oddCutSlack_ne_zero_of_two_cut_edges {n : ℕ}
    (S : oddCutFacet n) (M : perfectMatchingVertex n) {e₁ e₂ : (completeGraph n).edgeSet}
    (hne : e₁ ≠ e₂) (he₁ : (e₁ : Sym2 (Fin n)) ∈ M.1.edgeSet)
    (he₂ : (e₂ : Sym2 (Fin n)) ∈ M.1.edgeSet)
    (hcut₁ : e₁ ∈ δ[completeGraph n] S.1) (hcut₂ : e₂ ∈ δ[completeGraph n] S.1) :
    oddCutSlack S M ≠ 0 := by
  let cut :
      Finset (Sym2 (Fin n)) :=
    (do
      let a ← δ[completeGraph n] S.1
      pure (a : Sym2 (Fin n))).filter fun e ↦ e ∈ M.1.edgeSet
  have hnotdiag₁ : ¬ (e₁ : Sym2 (Fin n)).IsDiag := by
    simpa [SimpleGraph.mem_edgeSet] using e₁.2
  have hnotdiag₂ : ¬ (e₂ : Sym2 (Fin n)).IsDiag := by
    simpa [SimpleGraph.mem_edgeSet] using e₂.2
  have he₁cut : (e₁ : Sym2 (Fin n)) ∈ cut := by
    simp [cut, hcut₁, he₁, hnotdiag₁]
  have he₂cut : (e₂ : Sym2 (Fin n)) ∈ cut := by
    simp [cut, hcut₂, he₂, hnotdiag₂]
  have hcut_gt : 1 < cut.card := by
    refine Finset.one_lt_card.mpr ?_
    refine ⟨(e₁ : Sym2 (Fin n)), he₁cut, (e₂ : Sym2 (Fin n)), he₂cut, ?_⟩
    intro h
    apply hne
    exact Subtype.ext h
  intro hzero
  have hcut_eq_one : cut.card = 1 := by
    have hzero' : ((cut.card : ℝ) - 1) = 0 := by
      simpa [oddCutSlack, cut] using hzero
    have : (cut.card : ℝ) = 1 := by
      linarith [hzero']
    exact_mod_cast this
  omega

private def quadrupleRectangleRowSet (n : ℕ) :
    Fin n × Fin n × Fin n × Fin n → Set (perfectMatchingFacetRow n)
  | (u, v, x, y) =>
      {row | match row with
        | .inl e => (e : Sym2 (Fin n)) = s(u, v) ∨ (e : Sym2 (Fin n)) = s(x, y)
        | .inr S =>
            s(u, v) ≠ s(x, y) ∧
              (∃ e : (completeGraph n).edgeSet,
                (e : Sym2 (Fin n)) = s(u, v) ∧ e ∈ δ[completeGraph n] S.1) ∧
              (∃ e : (completeGraph n).edgeSet,
                (e : Sym2 (Fin n)) = s(x, y) ∧ e ∈ δ[completeGraph n] S.1)}

private def quadrupleRectangleColSet (n : ℕ) :
    Fin n × Fin n × Fin n × Fin n → Set (perfectMatchingVertex n)
  | (u, v, x, y) => {M | s(u, v) ∈ M.1.edgeSet ∧ s(x, y) ∈ M.1.edgeSet}

private lemma quadrupleRectangleEntry_ne_zero {n : ℕ} {q : Fin n × Fin n × Fin n × Fin n}
    {row : perfectMatchingFacetRow n} {col : perfectMatchingVertex n}
    (hrow : row ∈ quadrupleRectangleRowSet n q) (hcol : col ∈ quadrupleRectangleColSet n q) :
    displayedSlackMatrix n row col ≠ 0 := by
  rcases q with ⟨u, v, x, y⟩
  have hcol' : s(u, v) ∈ col.1.edgeSet ∧ s(x, y) ∈ col.1.edgeSet := by
    simpa [quadrupleRectangleColSet] using hcol
  cases row with
  | inl e =>
      have hrow' : (e : Sym2 (Fin n)) = s(u, v) ∨ (e : Sym2 (Fin n)) = s(x, y) := by
        simpa [quadrupleRectangleRowSet] using hrow
      rcases hrow' with hrow_uv | hrow_xy
      · have hedge : (e : Sym2 (Fin n)) ∈ col.1.edgeSet := by
          simpa [hrow_uv] using hcol'.1
        simp [displayedSlackMatrix, hedge]
      · have hedge : (e : Sym2 (Fin n)) ∈ col.1.edgeSet := by
          simpa [hrow_xy] using hcol'.2
        simp [displayedSlackMatrix, hedge]
  | inr S =>
      have hrow' :
          s(u, v) ≠ s(x, y) ∧
            (∃ e : (completeGraph n).edgeSet,
              (e : Sym2 (Fin n)) = s(u, v) ∧ e ∈ δ[completeGraph n] S.1) ∧
            (∃ e : (completeGraph n).edgeSet,
              (e : Sym2 (Fin n)) = s(x, y) ∧ e ∈ δ[completeGraph n] S.1) := by
        simpa [quadrupleRectangleRowSet] using hrow
      rcases hrow' with ⟨hneq, ⟨e₁, he₁, hcut₁⟩, ⟨e₂, he₂, hcut₂⟩⟩
      have hne : e₁ ≠ e₂ := by
        intro h
        apply hneq
        simpa [he₁, he₂] using congrArg (fun e : (completeGraph n).edgeSet ↦ (e : Sym2 (Fin n))) h
      have he₁M : (e₁ : Sym2 (Fin n)) ∈ col.1.edgeSet := by
        simpa [he₁] using hcol'.1
      have he₂M : (e₂ : Sym2 (Fin n)) ∈ col.1.edgeSet := by
        simpa [he₂] using hcol'.2
      simpa [displayedSlackMatrix] using
        oddCutSlack_ne_zero_of_two_cut_edges S col hne he₁M he₂M hcut₁ hcut₂

private lemma exists_quadrupleCover_of_positive_slack (n : ℕ) :
    ∀ row col, displayedSlackMatrix n row col ≠ 0 →
      ∃ q, row ∈ quadrupleRectangleRowSet n q ∧ col ∈ quadrupleRectangleColSet n q := by
  intro row col hslack
  cases row with
  | inl e =>
      have hedge : (e : Sym2 (Fin n)) ∈ col.1.edgeSet := by
        by_contra hedge
        exact hslack (by simp [displayedSlackMatrix, hedge])
      refine ⟨(e.1.out.1, e.1.out.2, e.1.out.1, e.1.out.2), ?_, ?_⟩
      · -- A nonnegativity row is covered by the rectangle indexed by the repeated edge quadruple.
        change (e : Sym2 (Fin n)) = s(e.1.out.1, e.1.out.2) ∨
            (e : Sym2 (Fin n)) = s(e.1.out.1, e.1.out.2)
        exact Or.inl e.1.out_eq.symm
      · -- Positive slack on a nonnegativity row means the corresponding edge lies in the matching.
        simpa [quadrupleRectangleColSet, e.1.out_eq] using And.intro hedge hedge
  | inr S =>
      obtain ⟨e₁, e₂, hne, he₁M, he₂M, hcut₁, hcut₂⟩ :=
        exists_two_cut_edges_of_oddCutSlack_ne_zero S col hslack
      have hsym_ne : s(e₁.1.out.1, e₁.1.out.2) ≠ s(e₂.1.out.1, e₂.1.out.2) := by
        intro hs
        apply hne
        apply Subtype.ext
        exact e₁.1.out_eq.symm.trans (hs.trans e₂.1.out_eq)
      refine ⟨(e₁.1.out.1, e₁.1.out.2, e₂.1.out.1, e₂.1.out.2), ?_, ?_⟩
      · -- The odd-cut row is covered by the rectangle indexed by the two cut edges from the hint.
        change s(e₁.1.out.1, e₁.1.out.2) ≠ s(e₂.1.out.1, e₂.1.out.2) ∧
            (∃ e : (completeGraph n).edgeSet,
              (e : Sym2 (Fin n)) = s(e₁.1.out.1, e₁.1.out.2) ∧ e ∈ δ[completeGraph n] S.1) ∧
            (∃ e : (completeGraph n).edgeSet,
              (e : Sym2 (Fin n)) = s(e₂.1.out.1, e₂.1.out.2) ∧ e ∈ δ[completeGraph n] S.1)
        exact ⟨hsym_ne, ⟨e₁, e₁.1.out_eq.symm, hcut₁⟩, ⟨e₂, e₂.1.out_eq.symm, hcut₂⟩⟩
      · -- Both chosen cut edges belong to the matching, so the column lies in the same rectangle.
        simpa [quadrupleRectangleColSet, e₁.1.out_eq, e₂.1.out_eq] using And.intro he₁M he₂M

private abbrev activeQuadruple (n : ℕ) :=
  {q : Fin n × Fin n × Fin n × Fin n //
      (quadrupleRectangleRowSet n q).Nonempty ∧ (quadrupleRectangleColSet n q).Nonempty}

private def quadrupleRectangleMatrix (n : ℕ) (q : activeQuadruple n) :
    Matrix (perfectMatchingFacetRow n) (perfectMatchingVertex n) ℝ :=
  rectangle_indicator (quadrupleRectangleRowSet n q.1) (quadrupleRectangleColSet n q.1)

private lemma quadrupleRectangleMatrix_is_rectangleMatrix (n : ℕ) (q : activeQuadruple n) :
    is_rectangle_matrix (quadrupleRectangleMatrix n q) := by
  exact rectangle_indicator_is_rectangle_matrix q.2.1 q.2.2

private lemma quadrupleRectangleCover (n : ℕ) :
    ∃ R : Fin (Fintype.card (activeQuadruple n)) →
      Matrix (perfectMatchingFacetRow n) (perfectMatchingVertex n) ℝ,
      is_rectangle_cover (displayedSlackMatrix n) R := by
  let e : Fin (Fintype.card (activeQuadruple n)) ≃ activeQuadruple n :=
    (Fintype.equivFin (activeQuadruple n)).symm
  refine ⟨fun t ↦ quadrupleRectangleMatrix n (e t), ?_⟩
  refine (is_rectangle_cover_iff).mpr ?_
  refine ⟨fun t ↦ quadrupleRectangleMatrix_is_rectangleMatrix n (e t), ?_⟩
  ext p
  rcases p with ⟨row, col⟩
  constructor
  · intro hp
    obtain ⟨q, hrow, hcol⟩ := exists_quadrupleCover_of_positive_slack n row col hp
    let aq : activeQuadruple n := ⟨q, ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩⟩
    refine Set.mem_iUnion.2 ⟨Fintype.equivFin (activeQuadruple n) aq, ?_⟩
    simpa [e, aq, quadrupleRectangleMatrix] using And.intro hrow hcol
  · intro hp
    rcases Set.mem_iUnion.1 hp with ⟨t, ht⟩
    have hmem :
        row ∈ quadrupleRectangleRowSet n (e t).1 ∧
          col ∈ quadrupleRectangleColSet n (e t).1 := by
      simpa [e, quadrupleRectangleMatrix] using ht
    exact quadrupleRectangleEntry_ne_zero hmem.1 hmem.2

/-- Exercise 4.36. The rectangle covering number of the complete-graph perfect-matching slack
matrix is at most `n ^ 4`. -/
theorem completeGraphPerfectMatchingSlackMatrix_rectangleCoveringNumber_le (n : ℕ) :
    rectangle_covering_number (completeGraphPerfectMatchingSlackMatrix n) ≤ n ^ 4 := by
  obtain ⟨R, hR⟩ := quadrupleRectangleCover n
  have hR' :
      is_rectangle_cover (completeGraphPerfectMatchingSlackMatrix n)
        (fun t ↦ Matrix.reindex (rowEquiv n) (colEquiv n) (R t)) := by
    -- Transport the displayed cover back through the canonical row and column equivalences.
    simpa [displayedSlackMatrix_eq_reindex] using
      hR.reindex (rowEquiv n) (colEquiv n)
  refine (rectangle_covering_number_le hR').trans ?_
  calc
    Fintype.card (activeQuadruple n) ≤
        Fintype.card (Fin n × Fin n × Fin n × Fin n) := by
          exact Fintype.card_subtype_le _
    _ = n ^ 4 := by
          calc
            Fintype.card (Fin n × Fin n × Fin n × Fin n) = n * (n * (n * n)) := by
              simp [Fintype.card_prod]
            _ = n ^ 4 := by
              simp [pow_succ, Nat.mul_assoc]
