/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_corollary_4_8

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search note: `tool_search` exposed no deferred Lean semantic search tool such as
-- `lean_leansearch`, so this file reuses mathlib's canonical `SimpleGraph.incMatrix`,
-- `SimpleGraph.IsBipartite`, and `Matrix.IsTotallyUnimodular` owners, with the chapter's
-- edge-indexed matrix `A_G` exposed as a thin bridge.

open scoped BigOperators
open SimpleGraph

universe u

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-- The edge-indexed incidence matrix `A_G`, obtained from `G.incMatrix R` by restricting the
columns to the actual edges of `G`. -/
abbrev edgeIncMatrix (R : Type*) [Zero R] [One R] [DecidableEq V] [DecidableRel G.Adj] :
    Matrix V G.edgeSet R :=
  (G.incMatrix R).submatrix id Subtype.val

end SimpleGraph

section Theorem_4_18

variable {V : Type u} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Helper for Theorem 4.18: every entry of the edge-indexed incidence matrix is `0` or `1`. -/
lemma edge_incidence_matrix_hasZeroOneNegOneEntries :
    HasZeroOneNegOneEntries (G.edgeIncMatrix ℤ) := by
  -- The edge-indexed incidence matrix is a row/column restriction of the `0/1` incidence matrix.
  rw [hasZeroOneNegOneEntries_iff]
  intro v e
  rw [SimpleGraph.edgeIncMatrix, Matrix.submatrix_apply]
  by_cases h : (e : Sym2 V) ∈ G.incidenceSet v
  · right
    left
    exact G.incMatrix_of_mem_incidenceSet (R := ℤ) h
  · left
    exact G.incMatrix_of_notMem_incidenceSet (R := ℤ) h

/-- Helper for Theorem 4.18: a row-submatrix entry is nonzero exactly when the chosen row vertex is
incident to the chosen edge. -/
lemma edge_incidence_submatrix_entry_ne_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : ι ↪ V) {i : ι} {e : G.edgeSet} :
    ((G.edgeIncMatrix ℤ).submatrix row id) i e ≠ 0 ↔ (e : Sym2 V) ∈ G.incidenceSet (row i) := by
  -- Unfold the restricted incidence entry and rewrite `≠ 0` via the incidence-set criterion.
  rw [SimpleGraph.edgeIncMatrix, Matrix.submatrix_apply, Matrix.submatrix_apply]
  constructor
  · intro h
    by_contra hmem
    exact h ((G.incMatrix_apply_eq_zero_iff (R := ℤ) (a := row i) (e := (e : Sym2 V))).2 hmem)
  · intro h
    exact fun hzero ↦ ((G.incMatrix_apply_eq_zero_iff (R := ℤ) (a := row i) (e := (e : Sym2 V))).1 hzero) h

/-- Helper for Theorem 4.18: a nonzero entry in a row-restricted edge-incidence matrix is
necessarily equal to `1`. -/
lemma edge_incidence_submatrix_entry_eq_one_of_nonzero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : ι ↪ V) {i : ι} {e : G.edgeSet}
    (h : ((G.edgeIncMatrix ℤ).submatrix row id) i e ≠ 0) :
    ((G.edgeIncMatrix ℤ).submatrix row id) i e = 1 := by
  -- Incidence matrix entries are `1` exactly at incident vertices.
  rw [SimpleGraph.edgeIncMatrix, Matrix.submatrix_apply, Matrix.submatrix_apply]
  exact
    G.incMatrix_of_mem_incidenceSet (R := ℤ)
      ((edge_incidence_submatrix_entry_ne_zero_iff (G := G) row).1 h)

/-- Helper for Theorem 4.18: a nonzero row-submatrix entry forces the row vertex to be one of the
two endpoints of the edge indexing that column. -/
lemma edge_incidence_submatrix_mem_edge_of_nonzero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : ι ↪ V) {i : ι} {e : G.edgeSet}
    (h : ((G.edgeIncMatrix ℤ).submatrix row id) i e ≠ 0) :
    row i ∈ (e : Sym2 V) := by
  -- Convert the nonzero entry to incidence-set membership, then read that as endpoint membership.
  exact
    (G.edge_mem_incidenceSet_iff (a := row i) (e := e)).1
      ((edge_incidence_submatrix_entry_ne_zero_iff (G := G) row).1 h)

/-- Helper for Theorem 4.18: each column of a row-restricted edge-incidence matrix has support of
size at most two. -/
lemma edge_incidence_submatrix_hasAtMostTwoNonzeroEntriesPerColumn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : ι ↪ V) :
    HasAtMostTwoNonzeroEntriesPerColumn ((G.edgeIncMatrix ℤ).submatrix row id) := by
  classical
  intro e
  let s : Finset ι :=
    Finset.univ.filter fun i ↦ ((G.edgeIncMatrix ℤ).submatrix row id) i e ≠ 0
  have hs : s.image row ⊆ (e : Sym2 V).toFinset := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    simpa using
      edge_incidence_submatrix_mem_edge_of_nonzero (G := G) row (i := i) (e := e)
        ((Finset.mem_filter.mp hi).2)
  -- The restricted column support injects into the two endpoints of the underlying edge.
  calc
    (Finset.univ.filter fun i ↦ ((G.edgeIncMatrix ℤ).submatrix row id) i e ≠ 0).card = s.card := by
      simp [s]
    _ = (s.image row).card := by
      symm
      exact Finset.card_image_of_injective s row.injective
    _ ≤ ((e : Sym2 V).toFinset).card := Finset.card_le_card hs
    _ = 2 := by
      exact Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet e.prop)
    _ ≤ 2 := le_rfl

/-- Helper for Theorem 4.18: the row indexed by one endpoint of an edge contributes `1` in the
corresponding edge column. -/
lemma edge_incidence_submatrix_entry_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : ι ↪ V) {i j : ι} (hij : G.Adj (row i) (row j)) :
    ((G.edgeIncMatrix ℤ).submatrix row id) i ⟨s(row i, row j), hij⟩ = 1 := by
  -- The edge column is incident to its left endpoint by definition.
  rw [SimpleGraph.edgeIncMatrix, Matrix.submatrix_apply, Matrix.submatrix_apply]
  exact
    G.incMatrix_of_mem_incidenceSet (R := ℤ)
      ((G.mk'_mem_incidenceSet_left_iff (a := row i) (b := row j)).2 hij)

/-- Helper for Theorem 4.18: the row indexed by the other endpoint of an edge also contributes `1`
in the corresponding edge column. -/
lemma edge_incidence_submatrix_entry_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : ι ↪ V) {i j : ι} (hij : G.Adj (row i) (row j)) :
    ((G.edgeIncMatrix ℤ).submatrix row id) j ⟨s(row i, row j), hij⟩ = 1 := by
  -- The same edge column is incident to its right endpoint as well.
  rw [SimpleGraph.edgeIncMatrix, Matrix.submatrix_apply, Matrix.submatrix_apply]
  exact
    G.incMatrix_of_mem_incidenceSet (R := ℤ)
      ((G.mk'_mem_incidenceSet_right_iff (a := row i) (b := row j)).2 hij)

/-- Helper for Theorem 4.18: rows other than the two endpoints of an edge contribute `0` in that
edge column. -/
lemma edge_incidence_submatrix_entry_eq_zero_of_ne_endpoints
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : ι ↪ V) {i j k : ι} (hij : G.Adj (row i) (row j))
    (hki : k ≠ i) (hkj : k ≠ j) :
    ((G.edgeIncMatrix ℤ).submatrix row id) k ⟨s(row i, row j), hij⟩ = 0 := by
  -- A different row vertex is not incident to the edge joining `row i` and `row j`.
  rw [SimpleGraph.edgeIncMatrix, Matrix.submatrix_apply, Matrix.submatrix_apply]
  refine G.incMatrix_of_notMem_incidenceSet (R := ℤ) ?_
  simpa using
    (show s(row i, row j) ∉ G.incidenceSet (row k) from by
      rw [G.mk'_mem_incidenceSet_iff]
      simp [hij, row.injective.ne hki, row.injective.ne hkj])

/-- Helper for Theorem 4.18: a Boolean coloring of the vertices induces an equitable row-bicoloring
on every finite row restriction of the edge-incidence matrix. -/
lemma edge_incidence_submatrix_is_equitable_row_bicoloring_of_coloring
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : ι ↪ V) (c : G.Coloring Bool) :
    ∃ red blue : Finset ι,
      is_equitable_row_bicoloring ((G.edgeIncMatrix ℤ).submatrix row id) red blue := by
  classical
  let B : Matrix ι G.edgeSet ℤ := (G.edgeIncMatrix ℤ).submatrix row id
  let red : Finset ι := Finset.univ.filter fun i ↦ c (row i) = true
  let blue : Finset ι := Finset.univ.filter fun i ↦ c (row i) = false
  refine ⟨red, blue, ?_⟩
  rw [is_equitable_row_bicoloring_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- The red and blue rows are disjoint because a Boolean color cannot be both values.
    rw [Finset.disjoint_left]
    intro i hiRed hiBlue
    have hRed : c (row i) = true := (Finset.mem_filter.mp hiRed).2
    have hBlue : c (row i) = false := (Finset.mem_filter.mp hiBlue).2
    simp [hRed] at hBlue
  · -- Every selected row gets one of the two Boolean colors.
    ext i
    by_cases hi : c (row i) = true
    · simp [red, blue, hi]
    · have hi' : c (row i) = false := by
        cases hci : c (row i) <;> simp_all
      simp [red, blue, hi, hi']
  · intro e
    let support : Finset ι := Finset.univ.filter fun i ↦ B i e ≠ 0
    have hsupportCard : support.card ≤ 2 := by
      simpa [B, support] using
        edge_incidence_submatrix_hasAtMostTwoNonzeroEntriesPerColumn (G := G) row e
    have hcases : support.card = 0 ∨ support.card = 1 ∨ support.card = 2 := by
      omega
    rcases hcases with hzero | hone | htwo
    · have hsupport : support = ∅ := Finset.card_eq_zero.mp hzero
      have hsZero : ∀ i : ι, B i e = 0 := by
        intro i
        by_contra hne
        have hi : i ∈ support := by
          simp [support, hne]
        simp [hsupport] at hi
      -- No selected row is incident to this edge, so the column difference is `0`.
      have hredSum : red.sum (fun i ↦ B i e) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        exact hsZero i
      have hblueSum : blue.sum (fun i ↦ B i e) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        exact hsZero i
      left
      rw [row_bicoloring_difference_apply, hredSum, hblueSum]
      norm_num
    · obtain ⟨i, hsupport⟩ := Finset.card_eq_one.mp hone
      have hiSupport : i ∈ support := by
        simp [hsupport]
      have hnonzero : B i e ≠ 0 := (Finset.mem_filter.mp hiSupport).2
      have hentry : B i e = 1 := by
        exact edge_incidence_submatrix_entry_eq_one_of_nonzero (G := G) row hnonzero
      have hsZero : ∀ i' : ι, i' ≠ i → B i' e = 0 := by
        intro i' hi'
        by_contra hne
        have hi'Support : i' ∈ support := by
          simp [support, hne]
        have : i' = i := by
          simpa [hsupport] using hi'Support
        exact hi' this
      by_cases hci : c (row i) = true
      · have hiRed : i ∈ red := by simp [red, hci]
        have hnotBlue : i ∉ blue := by simp [blue, hci]
        have hredSum : red.sum (fun i' ↦ B i' e) = 1 := by
          -- With a unique nonzero row colored red, the red sum is exactly that entry.
          calc
            red.sum (fun i' ↦ B i' e) = B i e := by
              simpa [B, red, hci] using
                sum_eq_if_mem_of_eq_zero_off_singleton red (fun i' ↦ B i' e) i
                  (fun i' _ hi' ↦ hsZero i' hi')
            _ = 1 := hentry
        have hblueSum : blue.sum (fun i' ↦ B i' e) = 0 := by
          -- No blue row contributes at the unique nonzero position.
          calc
            blue.sum (fun i' ↦ B i' e) = if i ∈ blue then B i e else 0 := by
              exact
                sum_eq_if_mem_of_eq_zero_off_singleton blue (fun i' ↦ B i' e) i
                  (fun i' _ hi' ↦ hsZero i' hi')
            _ = 0 := by simp [hnotBlue]
        right
        left
        rw [row_bicoloring_difference_apply, hredSum, hblueSum]
        norm_num
      · have hci' : c (row i) = false := by
          cases hcol : c (row i) <;> simp_all
        have hiBlue : i ∈ blue := by simp [blue, hci']
        have hnotRed : i ∉ red := by simp [red, hci]
        have hredSum : red.sum (fun i' ↦ B i' e) = 0 := by
          -- No red row contributes at the unique nonzero position.
          calc
            red.sum (fun i' ↦ B i' e) = if i ∈ red then B i e else 0 := by
              exact
                sum_eq_if_mem_of_eq_zero_off_singleton red (fun i' ↦ B i' e) i
                  (fun i' _ hi' ↦ hsZero i' hi')
            _ = 0 := by simp [hnotRed]
        have hblueSum : blue.sum (fun i' ↦ B i' e) = 1 := by
          -- The unique nonzero row now lies in the blue class.
          calc
            blue.sum (fun i' ↦ B i' e) = B i e := by
              simpa [B, blue, hci'] using
                sum_eq_if_mem_of_eq_zero_off_singleton blue (fun i' ↦ B i' e) i
                  (fun i' _ hi' ↦ hsZero i' hi')
            _ = 1 := hentry
        right
        right
        rw [row_bicoloring_difference_apply, hredSum, hblueSum]
        norm_num
    · obtain ⟨i, j, hij, hsupport⟩ := Finset.card_eq_two.mp htwo
      have hiSupport : i ∈ support := by simp [hsupport]
      have hjSupport : j ∈ support := by simp [hsupport, hij]
      have hnonzeroI : B i e ≠ 0 := (Finset.mem_filter.mp hiSupport).2
      have hnonzeroJ : B j e ≠ 0 := (Finset.mem_filter.mp hjSupport).2
      have hentryI : B i e = 1 := by
        exact edge_incidence_submatrix_entry_eq_one_of_nonzero (G := G) row hnonzeroI
      have hentryJ : B j e = 1 := by
        exact edge_incidence_submatrix_entry_eq_one_of_nonzero (G := G) row hnonzeroJ
      have hsZero : ∀ k : ι, k ≠ i → k ≠ j → B k e = 0 := by
        intro k hki hkj
        by_contra hne
        have hkSupport : k ∈ support := by
          simp [support, hne]
        have : k = i ∨ k = j := by
          simpa [hsupport] using hkSupport
        cases this with
        | inl hk => exact hki hk
        | inr hk => exact hkj hk
      have hIncI : (e : Sym2 V) ∈ G.incidenceSet (row i) := by
        exact (edge_incidence_submatrix_entry_ne_zero_iff (G := G) row).1 hnonzeroI
      have hIncJ : (e : Sym2 V) ∈ G.incidenceSet (row j) := by
        exact (edge_incidence_submatrix_entry_ne_zero_iff (G := G) row).1 hnonzeroJ
      have hAdj : G.Adj (row i) (row j) := by
        exact G.adj_of_mem_incidenceSet (row.injective.ne hij) hIncI hIncJ
      have hColorNe : c (row i) ≠ c (row j) := c.valid hAdj
      by_cases hci : c (row i) = true
      · have hcj : c (row j) = false := by
          cases hcj' : c (row j) with
          | false => simp [hcj']
          | true =>
              exfalso
              exact hColorNe (by simp [hci, hcj'])
        have hiRed : i ∈ red := by simp [red, hci]
        have hjBlue : j ∈ blue := by simp [blue, hcj]
        have hnotBlueI : i ∉ blue := by simp [blue, hci]
        have hnotRedJ : j ∉ red := by simp [red, hcj]
        have hredZero :
            ∀ k ∈ red, k ≠ i → B k e = 0 := by
          intro k hk hki
          by_cases hkj : k = j
          · exact False.elim (hnotRedJ (hkj ▸ hk))
          · exact hsZero k hki hkj
        have hblueZero :
            ∀ k ∈ blue, k ≠ j → B k e = 0 := by
          intro k hk hkj
          by_cases hki : k = i
          · exact False.elim (hnotBlueI (hki ▸ hk))
          · exact hsZero k hki hkj
        have hredSum : red.sum (fun k ↦ B k e) = 1 := by
          -- Exactly one red endpoint survives in this column.
          calc
            red.sum (fun k ↦ B k e) = B i e := by
              simpa [B, red, hci] using
                sum_eq_if_mem_of_eq_zero_off_singleton red (fun k ↦ B k e) i
                  (fun k hk hki ↦ hredZero k hk hki)
            _ = 1 := hentryI
        have hblueSum : blue.sum (fun k ↦ B k e) = 1 := by
          -- Exactly one blue endpoint survives in this column.
          calc
            blue.sum (fun k ↦ B k e) = B j e := by
              simpa [B, blue, hcj] using
                sum_eq_if_mem_of_eq_zero_off_singleton blue (fun k ↦ B k e) j
                  (fun k hk hkj ↦ hblueZero k hk hkj)
            _ = 1 := hentryJ
        left
        rw [row_bicoloring_difference_apply, hredSum, hblueSum]
        norm_num
      · have hci' : c (row i) = false := by
          cases hcol : c (row i) <;> simp_all
        have hcj : c (row j) = true := by
          cases hcj' : c (row j) with
          | false =>
              exfalso
              exact hColorNe (by simp [hci', hcj'])
          | true => simp [hcj']
        have hiBlue : i ∈ blue := by simp [blue, hci']
        have hjRed : j ∈ red := by simp [red, hcj]
        have hnotRedI : i ∉ red := by simp [red, hci']
        have hnotBlueJ : j ∉ blue := by simp [blue, hcj]
        have hredZero :
            ∀ k ∈ red, k ≠ j → B k e = 0 := by
          intro k hk hkj
          by_cases hki : k = i
          · exact False.elim (hnotRedI (hki ▸ hk))
          · exact hsZero k hki hkj
        have hblueZero :
            ∀ k ∈ blue, k ≠ i → B k e = 0 := by
          intro k hk hki
          by_cases hkj : k = j
          · exact False.elim (hnotBlueJ (hkj ▸ hk))
          · exact hsZero k hki hkj
        have hredSum : red.sum (fun k ↦ B k e) = 1 := by
          -- The red endpoint is `j`, so the red sum is still `1`.
          calc
            red.sum (fun k ↦ B k e) = B j e := by
              simpa [B, red, hcj] using
                sum_eq_if_mem_of_eq_zero_off_singleton red (fun k ↦ B k e) j
                  (fun k hk hkj ↦ hredZero k hk hkj)
            _ = 1 := hentryJ
        have hblueSum : blue.sum (fun k ↦ B k e) = 1 := by
          -- The blue endpoint is `i`, so the blue sum is also `1`.
          calc
            blue.sum (fun k ↦ B k e) = B i e := by
              simpa [B, blue, hci'] using
                sum_eq_if_mem_of_eq_zero_off_singleton blue (fun k ↦ B k e) i
                  (fun k hk hki ↦ hblueZero k hk hki)
            _ = 1 := hentryI
        left
        rw [row_bicoloring_difference_apply, hredSum, hblueSum]
        norm_num

/-- Helper for Theorem 4.18: a bipartition yields equitable row-bicolorings on every finite row
restriction of the edge-incidence matrix. -/
lemma edge_incidence_submatrix_is_equitable_row_bicoloring_of_isBipartiteWith
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : ι ↪ V) {U W : Set V} (hUW : G.IsBipartiteWith U W) :
    ∃ red blue : Finset ι,
      is_equitable_row_bicoloring ((G.edgeIncMatrix ℤ).submatrix row id) red blue := by
  -- Convert the bipartition witness into a Boolean coloring, then use the coloring helper.
  obtain ⟨cFin⟩ := hUW.isBipartite
  let c : G.Coloring Bool := recolorOfEquiv G finTwoEquiv cFin
  exact edge_incidence_submatrix_is_equitable_row_bicoloring_of_coloring (G := G) row c

/-- Helper for Theorem 4.18: in an equitable row-bicoloring of a row-restricted edge-incidence
matrix, the two endpoints of any represented edge lie in opposite color classes. -/
lemma equitable_row_bicoloring_adj_endpoints_opposite_on_row_submatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : ι ↪ V) {red blue : Finset ι}
    (hColor : is_equitable_row_bicoloring ((G.edgeIncMatrix ℤ).submatrix row id) red blue) :
    ∀ {i j : ι}, G.Adj (row i) (row j) → (i ∈ red ∧ j ∈ blue) ∨ (i ∈ blue ∧ j ∈ red) := by
  classical
  rcases (is_equitable_row_bicoloring_iff.1 hColor) with ⟨hDisj, _hCover, hBalance⟩
  intro i j hij
  have hij' : i ≠ j := by
    intro hEq
    exact G.ne_of_adj hij (congrArg row hEq)
  have hiColor := is_equitable_row_bicoloring.mem_red_or_mem_blue hColor i
  have hjColor := is_equitable_row_bicoloring.mem_red_or_mem_blue hColor j
  rcases hiColor with hiRed | hiBlue
  · rcases hjColor with hjRed | hjBlue
    · exfalso
      let B : Matrix ι G.edgeSet ℤ := (G.edgeIncMatrix ℤ).submatrix row id
      let e : G.edgeSet := ⟨s(row i, row j), hij⟩
      let f : ι → ℤ := fun k ↦ B k e
      have hBi : B i e = 1 := by
        unfold B e
        simpa using edge_incidence_submatrix_entry_left (G := G) row hij
      have hBj : B j e = 1 := by
        unfold B e
        simpa using edge_incidence_submatrix_entry_right (G := G) row hij
      have hPairSubset : ({i, j} : Finset ι) ⊆ red := by
        simp [Finset.insert_subset_iff, hiRed, hjRed]
      have hredSum : red.sum f = 2 := by
        -- If both endpoints are red, the red rows contribute exactly the two endpoint ones.
        rw [← Finset.sum_subset (s₁ := ({i, j} : Finset ι)) (s₂ := red) hPairSubset]
        · rw [Finset.sum_pair hij', hBi, hBj]
          norm_num
        · intro k hkRed hkPair
          have hki : k ≠ i := by
            intro hki
            exact hkPair (by simp [hki])
          have hkj : k ≠ j := by
            intro hkj
            exact hkPair (by simp [hkj])
          exact edge_incidence_submatrix_entry_eq_zero_of_ne_endpoints (G := G) row hij hki hkj
      have hnotBlueI : i ∉ blue := by
        exact Finset.disjoint_left.mp hDisj hiRed
      have hnotBlueJ : j ∉ blue := by
        exact Finset.disjoint_left.mp hDisj hjRed
      have hblueSum : blue.sum f = 0 := by
        -- No blue row can contribute, since the only nonzero rows are the two red endpoints.
        rw [← Finset.sum_subset (s₁ := (∅ : Finset ι)) (s₂ := blue) (by simp)]
        · simp
        · intro k hkBlue _hk
          by_cases hki : k = i
          · exact False.elim (hnotBlueI (hki ▸ hkBlue))
          · by_cases hkj : k = j
            · exact False.elim (hnotBlueJ (hkj ▸ hkBlue))
            · exact edge_incidence_submatrix_entry_eq_zero_of_ne_endpoints (G := G) row hij hki hkj
      have hDiff :
          row_bicoloring_difference ((G.edgeIncMatrix ℤ).submatrix row id) red blue e = 2 := by
        rw [row_bicoloring_difference_apply, hredSum, hblueSum]
        norm_num
      have hBad := hBalance e
      rw [hDiff] at hBad
      norm_num at hBad
    · exact Or.inl ⟨hiRed, hjBlue⟩
  · rcases hjColor with hjRed | hjBlue
    · exact Or.inr ⟨hiBlue, hjRed⟩
    · exfalso
      let B : Matrix ι G.edgeSet ℤ := (G.edgeIncMatrix ℤ).submatrix row id
      let e : G.edgeSet := ⟨s(row i, row j), hij⟩
      let f : ι → ℤ := fun k ↦ B k e
      have hBi : B i e = 1 := by
        unfold B e
        simpa using edge_incidence_submatrix_entry_left (G := G) row hij
      have hBj : B j e = 1 := by
        unfold B e
        simpa using edge_incidence_submatrix_entry_right (G := G) row hij
      have hnotRedI : i ∉ red := by
        exact fun hiRed ↦ Finset.disjoint_left.mp hDisj hiRed hiBlue
      have hnotRedJ : j ∉ red := by
        exact fun hjRed ↦ Finset.disjoint_left.mp hDisj hjRed hjBlue
      have hPairSubset : ({i, j} : Finset ι) ⊆ blue := by
        simp [Finset.insert_subset_iff, hiBlue, hjBlue]
      have hredSum : red.sum f = 0 := by
        -- No red row can contribute when both endpoints are blue.
        rw [← Finset.sum_subset (s₁ := (∅ : Finset ι)) (s₂ := red) (by simp)]
        · simp
        · intro k hkRed _hk
          by_cases hki : k = i
          · exact False.elim (hnotRedI (hki ▸ hkRed))
          · by_cases hkj : k = j
            · exact False.elim (hnotRedJ (hkj ▸ hkRed))
            · exact edge_incidence_submatrix_entry_eq_zero_of_ne_endpoints (G := G) row hij hki hkj
      have hblueSum : blue.sum f = 2 := by
        -- Both endpoint ones now appear in the blue sum.
        rw [← Finset.sum_subset (s₁ := ({i, j} : Finset ι)) (s₂ := blue) hPairSubset]
        · rw [Finset.sum_pair hij', hBi, hBj]
          norm_num
        · intro k hkBlue hkPair
          have hki : k ≠ i := by
            intro hki
            exact hkPair (by simp [hki])
          have hkj : k ≠ j := by
            intro hkj
            exact hkPair (by simp [hkj])
          exact edge_incidence_submatrix_entry_eq_zero_of_ne_endpoints (G := G) row hij hki hkj
      have hDiff :
          row_bicoloring_difference ((G.edgeIncMatrix ℤ).submatrix row id) red blue e = -2 := by
        rw [row_bicoloring_difference_apply, hredSum, hblueSum]
        norm_num
      have hBad := hBalance e
      rw [hDiff] at hBad
      norm_num at hBad

/-- Helper for Theorem 4.18: total unimodularity of the edge-incidence matrix forces every closed
walk to have even length. -/
lemma even_length_of_closed_walk_of_edge_incidence_matrix_isTotallyUnimodular
    (hTU : (G.edgeIncMatrix ℤ).IsTotallyUnimodular) :
    ∀ {u : V} (p : G.Walk u u), Even p.length := by
  intro u p
  classical
  let row : (↑p.support.toFinset) ↪ V := Function.Embedding.subtype fun v : V ↦ v ∈ p.support.toFinset
  let B : Matrix (↑p.support.toFinset) G.edgeSet ℤ := (G.edgeIncMatrix ℤ).submatrix row id
  have hBTU : B.IsTotallyUnimodular := by
    exact hTU.submatrix row id
  have hB01 : HasZeroOneNegOneEntries B := by
    exact (edge_incidence_matrix_hasZeroOneNegOneEntries (G := G)).submatrix row id
  have hBcol : HasAtMostTwoNonzeroEntriesPerColumn B := by
    simpa [B] using edge_incidence_submatrix_hasAtMostTwoNonzeroEntriesPerColumn (G := G) row
  obtain ⟨red, blue, hColor⟩ :=
    (totally_unimodular_iff_admits_equitable_row_bicoloring_of_column_support_card_le_two
      B hB01 hBcol).1 hBTU
  let s : Set V := (↑p.support.toFinset : Set V)
  let c : (G.induce s).Coloring Bool :=
    Coloring.mk (fun v ↦ decide (v ∈ red)) <| by
      have hDisj : Disjoint red blue := (is_equitable_row_bicoloring_iff.1 hColor).1
      intro v w hvw
      rcases
          equitable_row_bicoloring_adj_endpoints_opposite_on_row_submatrix
            (G := G) row hColor (i := v) (j := w) (by simpa using (SimpleGraph.induce_adj.1 hvw))
        with h | h
      · have hwNotRed : w ∉ red := Finset.disjoint_right.mp hDisj h.2
        simp [h.1, hwNotRed]
      · have hvNotRed : v ∉ red := Finset.disjoint_right.mp hDisj h.1
        simp [h.2, hvNotRed]
  have hs : ∀ x ∈ p.support, x ∈ s := by
    intro x hx
    simpa [s] using hx
  -- Induce the walk onto its finite support and read parity from the induced two-coloring.
  have hEvenInduced : Even ((p.induce s hs).length) := by
    exact (c.even_length_iff_congr (p.induce s hs)).2 (by simp)
  have hLength : (p.induce s hs).length = p.length := by
    rw [← SimpleGraph.Walk.length_map (f := (Embedding.induce s).toHom) (p := p.induce s hs)]
    simpa [s] using
      congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.map_induce (w := p) (s := s) hs)
  rwa [hLength] at hEvenInduced

/-- Theorem 4.18. Let `A_G` be the incidence matrix of a graph `G`. Then `A_G` is totally
unimodular if and only if `G` is bipartite. -/
theorem edge_incidence_matrix_isTotallyUnimodular_iff_isBipartite :
    (G.edgeIncMatrix ℤ).IsTotallyUnimodular ↔ G.IsBipartite := by
  constructor
  · intro hTU
    -- Localize TU to the support of each closed walk and deduce even cycle parity.
    exact
      (SimpleGraph.two_colorable_iff_forall_loop_even (G := G)).2
        (fun u p ↦
          even_length_of_closed_walk_of_edge_incidence_matrix_isTotallyUnimodular
            (G := G) hTU p)
  · intro hBip
    rcases hBip.exists_isBipartiteWith with ⟨U, W, hUW⟩
    -- Apply Corollary 4.7 by coloring each finite row restriction through the bipartition.
    exact
      (totally_unimodular_iff_every_row_submatrix_admits_equitable_row_bicoloring.{u, u, u}
        (G.edgeIncMatrix ℤ)).2 <| by
          intro ι _ _ row
          exact
            edge_incidence_submatrix_is_equitable_row_bicoloring_of_isBipartiteWith
              (G := G) row hUW

end Theorem_4_18
