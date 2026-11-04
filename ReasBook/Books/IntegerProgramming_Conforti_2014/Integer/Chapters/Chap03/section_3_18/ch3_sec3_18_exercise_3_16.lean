/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_definition_3_7_extra_1

open scoped Matrix

-- This exercise uses the Chapter 3 owner `polyhedron_le_set`; deleting rows is treated as
-- keeping the complementary subsystem via the canonical row-restriction view.

/-- Keeping the complementary rows via
`A.submatrix (Subtype.val : {i // i ∈ Iᶜ} → Fin m) id` and
`b ∘ (Subtype.val : {i // i ∈ Iᶜ} → Fin m)` is exactly the deleted-row subsystem of
`A *ᵥ x ≤ b`. -/
theorem mem_compl_rows_mulVec_le_iff
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin m))
    (x : Fin n → ℝ) :
    A.submatrix (Subtype.val : {i // i ∈ Iᶜ} → Fin m) id *ᵥ x ≤
        b ∘ (Subtype.val : {i // i ∈ Iᶜ} → Fin m) ↔
      ∀ j : Fin m, j ∉ I → (A *ᵥ x) j ≤ b j :=
by
  constructor
  · intro hx j hj
    simpa using hx ⟨j, hj⟩
  · intro hx j
    simpa using hx j.1 j.2

/-- A concrete four-row system in `ℝ²` exhibiting the phenomenon from Exercise 3.16. -/
def exercise_3_16_counterexample_matrix : Matrix (Fin 4) (Fin 2) ℝ :=
  !![(1 : ℝ), 0;
    0, 1;
    1, -1;
    -1, 1]

/-- The right-hand side vector for the counterexample system in Exercise 3.16. -/
def exercise_3_16_counterexample_rhs : Fin 4 → ℝ :=
  ![(0 : ℝ), 0, 0, 0]

/-- Helper for Exercise 3.16: the first row of the counterexample system evaluates to `x 0`. -/
lemma counterexample_row_zero_eval (x : Fin 2 → ℝ) :
    (exercise_3_16_counterexample_matrix *ᵥ x) 0 = x 0 := by
  -- Expand the concrete first row and simplify the finite dot product.
  simp [exercise_3_16_counterexample_matrix, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 3.16: the second row of the counterexample system evaluates to `x 1`. -/
lemma counterexample_row_one_eval (x : Fin 2 → ℝ) :
    (exercise_3_16_counterexample_matrix *ᵥ x) 1 = x 1 := by
  -- Expand the concrete second row and simplify the finite dot product.
  simp [exercise_3_16_counterexample_matrix, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 3.16: the third row of the counterexample system
evaluates to `x 0 - x 1`. -/
lemma counterexample_row_two_eval (x : Fin 2 → ℝ) :
    (exercise_3_16_counterexample_matrix *ᵥ x) 2 = x 0 - x 1 := by
  -- Expand the third row and normalize the resulting linear expression.
  ring_nf
  simp [exercise_3_16_counterexample_matrix, Matrix.mulVec, dotProduct, sub_eq_add_neg]

/-- Helper for Exercise 3.16: the fourth row of the counterexample system
evaluates to `-x 0 + x 1`. -/
lemma counterexample_row_three_eval (x : Fin 2 → ℝ) :
    (exercise_3_16_counterexample_matrix *ᵥ x) 3 = -x 0 + x 1 := by
  -- Expand the fourth row and simplify to the intended difference form.
  simp [exercise_3_16_counterexample_matrix, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 3.16: the last two rows force the two coordinates to be equal. -/
lemma counterexample_rows_two_three_force_equal (x : Fin 2 → ℝ)
    (h₂ : (exercise_3_16_counterexample_matrix *ᵥ x) 2 ≤ exercise_3_16_counterexample_rhs 2)
    (h₃ : (exercise_3_16_counterexample_matrix *ᵥ x) 3 ≤ exercise_3_16_counterexample_rhs 3) :
    x 0 = x 1 := by
  -- Rewrite the two comparison rows into scalar inequalities on the coordinates.
  rw [counterexample_row_two_eval] at h₂
  rw [counterexample_row_three_eval] at h₃
  simp [exercise_3_16_counterexample_rhs] at h₂ h₃
  linarith

/-- Exercise 3.16 (1). In the counterexample system, the first inequality `x ≤ 0` is redundant
for the full system because it follows from `y ≤ 0` and the equality rows `x ≤ y` and `y ≤ x`. -/
theorem counterexample_first_inequality_redundant :
    {x : Fin 2 → ℝ |
      exercise_3_16_counterexample_matrix.submatrix
          (Subtype.val : {i // i ∈ ({0} : Set (Fin 4))ᶜ} → Fin 4) id *ᵥ x ≤
        exercise_3_16_counterexample_rhs ∘
          (Subtype.val : {i // i ∈ ({0} : Set (Fin 4))ᶜ} → Fin 4)} ⊆
      {x : Fin 2 → ℝ |
        (exercise_3_16_counterexample_matrix *ᵥ x) 0 ≤ exercise_3_16_counterexample_rhs 0} := by
  intro x hx
  have hx' :=
    (mem_compl_rows_mulVec_le_iff
      exercise_3_16_counterexample_matrix exercise_3_16_counterexample_rhs ({0} : Set (Fin 4))
      x).1 hx
  have h₁ := hx' 1 (by simp)
  have h₂ := hx' 2 (by simp)
  have h₃ := hx' 3 (by simp)
  -- The equality rows identify the two coordinates, so `y ≤ 0` forces `x ≤ 0`.
  have hxy : x 0 = x 1 := counterexample_rows_two_three_force_equal x h₂ h₃
  rw [counterexample_row_one_eval] at h₁
  have h₁' : x 1 ≤ 0 := by
    simpa [exercise_3_16_counterexample_rhs] using h₁
  simpa [counterexample_row_zero_eval, exercise_3_16_counterexample_rhs, hxy] using h₁'

/-- Exercise 3.16 (2). In the same counterexample system, the second inequality `y ≤ 0` is also
redundant for the full system. -/
theorem counterexample_second_inequality_redundant :
    {x : Fin 2 → ℝ |
      exercise_3_16_counterexample_matrix.submatrix
          (Subtype.val : {i // i ∈ ({1} : Set (Fin 4))ᶜ} → Fin 4) id *ᵥ x ≤
        exercise_3_16_counterexample_rhs ∘
          (Subtype.val : {i // i ∈ ({1} : Set (Fin 4))ᶜ} → Fin 4)} ⊆
      {x : Fin 2 → ℝ |
        (exercise_3_16_counterexample_matrix *ᵥ x) 1 ≤ exercise_3_16_counterexample_rhs 1} := by
  intro x hx
  have hx' :=
    (mem_compl_rows_mulVec_le_iff
      exercise_3_16_counterexample_matrix exercise_3_16_counterexample_rhs ({1} : Set (Fin 4))
      x).1 hx
  have h₀ := hx' 0 (by simp)
  have h₂ := hx' 2 (by simp)
  have h₃ := hx' 3 (by simp)
  -- The same equality rows now transfer `x ≤ 0` to the conclusion `y ≤ 0`.
  have hxy : x 0 = x 1 := counterexample_rows_two_three_force_equal x h₂ h₃
  rw [counterexample_row_zero_eval] at h₀
  have h₀' : x 0 ≤ 0 := by
    simpa [exercise_3_16_counterexample_rhs] using h₀
  simpa [counterexample_row_one_eval, exercise_3_16_counterexample_rhs, hxy] using h₀'

/-- Exercise 3.16 (3). Removing the second inequality destroys the redundancy of the first one,
so a redundant inequality need not remain redundant after another redundant inequality is
removed. -/
theorem first_inequality_not_redundant_after_removing_second :
    ¬ {x : Fin 2 → ℝ |
        exercise_3_16_counterexample_matrix.submatrix
            (Subtype.val : {i // i ∈ ({0, 1} : Set (Fin 4))ᶜ} → Fin 4) id *ᵥ x ≤
          exercise_3_16_counterexample_rhs ∘
            (Subtype.val : {i // i ∈ ({0, 1} : Set (Fin 4))ᶜ} → Fin 4)} ⊆
      {x : Fin 2 → ℝ |
        (exercise_3_16_counterexample_matrix *ᵥ x) 0 ≤ exercise_3_16_counterexample_rhs 0} := by
  intro h_redundant
  let x : Fin 2 → ℝ := ![1, 1]
  have h_row_two :
      (exercise_3_16_counterexample_matrix *ᵥ x) 2 ≤ exercise_3_16_counterexample_rhs 2 := by
    -- The witness lies on the row `x - y ≤ 0`.
    rw [counterexample_row_two_eval]
    simp [x, exercise_3_16_counterexample_rhs]
  have h_row_three :
      (exercise_3_16_counterexample_matrix *ᵥ x) 3 ≤ exercise_3_16_counterexample_rhs 3 := by
    -- The witness also lies on the row `-x + y ≤ 0`.
    rw [counterexample_row_three_eval]
    simp [x, exercise_3_16_counterexample_rhs]
  have h_rows :
      x ∈ {x : Fin 2 → ℝ |
        exercise_3_16_counterexample_matrix.submatrix
            (Subtype.val : {i // i ∈ ({0, 1} : Set (Fin 4))ᶜ} → Fin 4) id *ᵥ x ≤
          exercise_3_16_counterexample_rhs ∘
            (Subtype.val : {i // i ∈ ({0, 1} : Set (Fin 4))ᶜ} → Fin 4)} := by
    exact
      (mem_compl_rows_mulVec_le_iff
        exercise_3_16_counterexample_matrix
        exercise_3_16_counterexample_rhs
        ({0, 1} : Set (Fin 4))
        x).2
        (by
          intro j hj
          fin_cases j
          · exact False.elim (hj (by simp))
          · exact False.elim (hj (by simp))
          · simpa using h_row_two
          · simpa using h_row_three)
  have h_row_zero :
      (exercise_3_16_counterexample_matrix *ᵥ x) 0 ≤ exercise_3_16_counterexample_rhs 0 := by
    simpa using h_redundant h_rows
  -- Evaluating the deleted-row witness at row `0` yields the contradiction `1 ≤ 0`.
  rw [counterexample_row_zero_eval] at h_row_zero
  have h_false : (1 : ℝ) ≤ 0 := by
    simpa [x, exercise_3_16_counterexample_rhs] using h_row_zero
  norm_num at h_false
