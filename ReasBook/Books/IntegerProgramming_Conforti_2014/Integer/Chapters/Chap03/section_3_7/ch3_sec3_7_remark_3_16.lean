import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_definition_3_7_extra_1

open scoped Matrix

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Remark 3.16: evaluating a row of the averaged witness family reduces to the
corresponding average of row values. -/
lemma mulVec_finset_average_apply
    {m n : ℕ}
    {ι : Type*}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (s : Finset ι)
    (y : ι → Fin n → ℝ)
    (k : Fin m) :
    (A *ᵥ (((s.card : ℝ)⁻¹) • ∑ j ∈ s, y j)) k =
      (s.card : ℝ)⁻¹ * ∑ j ∈ s, (A *ᵥ y j) k := by
  -- Expand the matrix action using linearity, then evaluate the resulting function at `k`.
  rw [Matrix.mulVec_smul, Matrix.mulVec_sum]
  simp [Pi.smul_apply]

/-- Helper for Remark 3.16: the average of finitely many feasible points is still feasible for the
polyhedron `{x | A *ᵥ x ≤ b}`. -/
lemma average_of_feasible_family_mem_polyhedron
    {m n : ℕ}
    {ι : Type*}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (s : Finset ι)
    (hs : s.Nonempty)
    (y : ι → Fin n → ℝ)
    (hy : ∀ j ∈ s, A *ᵥ y j ≤ b) :
    ((s.card : ℝ)⁻¹) • ∑ j ∈ s, y j ∈ polyhedron_le_set A b := by
  -- Prove feasibility rowwise after rewriting each row as an average of feasible row values.
  change A *ᵥ (((s.card : ℝ)⁻¹) • ∑ j ∈ s, y j) ≤ b
  intro k
  have hcard_pos : 0 < (s.card : ℝ) := by
    exact_mod_cast hs.card_pos
  have hcard_ne : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  have hinv_nonneg : 0 ≤ (s.card : ℝ)⁻¹ := by
    exact inv_nonneg.mpr hcard_pos.le
  have hsum_le : ∑ j ∈ s, (A *ᵥ y j) k ≤ s.card • b k := by
    refine Finset.sum_le_card_nsmul s (fun j ↦ (A *ᵥ y j) k) (b k) ?_
    intro j hj
    exact hy j hj k
  rw [mulVec_finset_average_apply]
  calc
    (s.card : ℝ)⁻¹ * ∑ j ∈ s, (A *ᵥ y j) k
        ≤ (s.card : ℝ)⁻¹ * (s.card • b k) := by
          exact mul_le_mul_of_nonneg_left hsum_le hinv_nonneg
    _ = (s.card : ℝ)⁻¹ * ((s.card : ℝ) * b k) := by
          rw [nsmul_eq_mul]
    _ = ((s.card : ℝ)⁻¹ * (s.card : ℝ)) * b k := by
          ring
    _ = b k := by
          simp [hcard_ne]

/-- Helper for Remark 3.16: if one witness is strict in row `i` and all witnesses are feasible,
then their average is still strict in row `i`. -/
lemma strict_row_of_average_of_rowwise_witnesses
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (s : Finset (Fin m))
    (hs : s.Nonempty)
    (y : Fin m → Fin n → ℝ)
    (i : Fin m)
    (hi : i ∈ s)
    (hy : ∀ j ∈ s, A *ᵥ y j ≤ b)
    (hstrict : (A *ᵥ y i) i < b i) :
    (A *ᵥ (((s.card : ℝ)⁻¹) • ∑ j ∈ s, y j)) i < b i := by
  -- Sum the row inequalities and keep the witness row strictly below `b i`.
  have hcard_pos : 0 < (s.card : ℝ) := by
    exact_mod_cast hs.card_pos
  have hcard_ne : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  have hinv_pos : 0 < (s.card : ℝ)⁻¹ := by
    exact inv_pos.mpr hcard_pos
  have hsum_lt : ∑ j ∈ s, (A *ᵥ y j) i < ∑ _j ∈ s, b i := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro j hj
      exact hy j hj i
    · exact ⟨i, hi, hstrict⟩
  rw [mulVec_finset_average_apply]
  calc
    (s.card : ℝ)⁻¹ * ∑ j ∈ s, (A *ᵥ y j) i
        < (s.card : ℝ)⁻¹ * ∑ _j ∈ s, b i := by
          exact mul_lt_mul_of_pos_left hsum_lt hinv_pos
    _ = (s.card : ℝ)⁻¹ * (s.card • b i) := by
          rw [Finset.sum_const]
    _ = (s.card : ℝ)⁻¹ * ((s.card : ℝ) * b i) := by
          rw [nsmul_eq_mul]
    _ = ((s.card : ℝ)⁻¹ * (s.card : ℝ)) * b i := by
          ring
    _ = b i := by
          simp [hcard_ne]

/-- Helper for Remark 3.16: if each row in a finite subset `I_lt` is strict at some point of the
polyhedron `polyhedron_le_set A b`, then one point of that polyhedron makes all rows in `I_lt`
strict simultaneously. -/
theorem exists_mem_polyhedron_le_set_strict_on_finset
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I_lt : Finset (Fin m))
    (h_nonempty : Set.Nonempty (polyhedron_le_set A b))
    (h_strict :
      ∀ i ∈ I_lt,
        ∃ x ∈ polyhedron_le_set A b, (A *ᵥ x) i < b i) :
    ∃ x ∈ polyhedron_le_set A b, ∀ i ∈ I_lt, (A *ᵥ x) i < b i := by
  classical
  obtain ⟨x₀, hx₀_mem⟩ := h_nonempty
  by_cases hI : I_lt.Nonempty
  · let xSel : Fin m → Fin n → ℝ := fun i ↦
      if hi : i ∈ I_lt then Classical.choose (h_strict i hi) else x₀
    let xbar : Fin n → ℝ := ((I_lt.card : ℝ)⁻¹) • ∑ j ∈ I_lt, xSel j
    have hxSel_mem : ∀ i ∈ I_lt, A *ᵥ xSel i ≤ b := by
      -- On rows from `I_lt`, `xSel` is the chosen feasible witness.
      intro i hi
      simpa [xSel, hi] using (Classical.choose_spec (h_strict i hi)).1
    have hxSel_strict : ∀ i ∈ I_lt, (A *ᵥ xSel i) i < b i := by
      -- The chosen witness for row `i` is strict exactly in that row.
      intro i hi
      simpa [xSel, hi] using (Classical.choose_spec (h_strict i hi)).2
    have hxbar_mem : xbar ∈ polyhedron_le_set A b := by
      -- Averaging feasible witnesses preserves feasibility.
      unfold xbar
      exact average_of_feasible_family_mem_polyhedron A b I_lt hI xSel hxSel_mem
    have hxbar_strict : ∀ i ∈ I_lt, (A *ᵥ xbar) i < b i := by
      -- In each strict row, its own strict witness keeps the average strictly below `b`.
      intro i hi
      unfold xbar
      exact strict_row_of_average_of_rowwise_witnesses A b I_lt hI xSel i hi hxSel_mem
        (hxSel_strict i hi)
    exact ⟨xbar, hxbar_mem, hxbar_strict⟩
  · have hI_empty : I_lt = ∅ := by
      exact Finset.not_nonempty_iff_eq_empty.mp hI
    refine ⟨x₀, hx₀_mem, ?_⟩
    -- When `I_lt` is empty, the strict-row condition is vacuous.
    intro i hi
    rw [hI_empty] at hi
    exact False.elim (Finset.notMem_empty i hi)

/-- Remark 3.16. If the polyhedron `polyhedron_le_set A b` is nonempty, then it contains a point
that is strict on every remaining inequality simultaneously. In the Section 3.7 owner language,
this means there exists `x̄ ∈ polyhedron_le_set A b` such that `(A *ᵥ x̄) i < b i` for every
`i ∈ remaining_inequality_indices A b`. -/
theorem exists_mem_polyhedron_le_set_strict_on_remaining_inequality_indices
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : Set.Nonempty (polyhedron_le_set A b)) :
    ∃ x ∈ polyhedron_le_set A b,
      ∀ i ∈ remaining_inequality_indices A b, (A *ᵥ x) i < b i := by
  classical
  let I_lt : Finset (Fin m) := Finset.univ.filter (fun i ↦ i ∈ remaining_inequality_indices A b)
  have h_strict :
      ∀ i ∈ I_lt, ∃ x ∈ polyhedron_le_set A b, (A *ᵥ x) i < b i := by
    intro i hi
    have hi' : i ∈ remaining_inequality_indices A b := by
      simpa [I_lt] using hi
    exact exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices A b i hi'
  rcases
      exists_mem_polyhedron_le_set_strict_on_finset A b I_lt h_nonempty h_strict with
    ⟨x, hx, hx_strict⟩
  refine ⟨x, hx, ?_⟩
  intro i hi
  have hi' : i ∈ I_lt := by
    simpa [I_lt] using hi
  exact hx_strict i hi'
