/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped Matrix

section Exercise53

/-- The matrix `A` for the description `P = {v ∈ ℝ^3 | A v ≤ b}` used in Exercise 5.3. -/
def exercise_5_3_matrix : Matrix (Fin 4) (Fin 3) ℝ :=
  ![![-1, 0, 1], ![0, -1, 1], ![1, 1, 2], ![0, 0, -1]]

/-- The right-hand side vector `b` for the matrix description of Exercise 5.3. -/
def exercise_5_3_rhs : Fin 4 → ℝ :=
  ![0, 0, 2, 0]

/-- The integer-variable index set `I = {x₁, x₂}` from Exercise 5.3. -/
def exercise_5_3_integer_indices : Finset (Fin 3) :=
  {0, 1}

/-- The polyhedron `P` from Exercise 5.3 in the coordinate order `(x₁, x₂, y)`. -/
def exercise_5_3_polyhedron : Set (Fin 3 → ℝ) :=
  polyhedron_le_set exercise_5_3_matrix exercise_5_3_rhs

/-- Membership in `exercise_5_3_polyhedron` is exactly the displayed system
`x₁ ≥ y`, `x₂ ≥ y`, `x₁ + x₂ + 2 y ≤ 2`, and `y ≥ 0`. -/
theorem mem_exercise_5_3_polyhedron_iff
    {v : Fin 3 → ℝ} :
    v ∈ exercise_5_3_polyhedron ↔
      v 2 ≤ v 0 ∧
        v 2 ≤ v 1 ∧
          v 0 + v 1 + 2 * v 2 ≤ 2 ∧
            0 ≤ v 2 := by
  rw [exercise_5_3_polyhedron, mem_polyhedron_le_set_iff]
  constructor
  · intro hv
    -- Rewrite the matrix inequalities into the four scalar constraints from the exercise.
    have hyx1 : v 2 ≤ v 0 := by
      simpa [exercise_5_3_matrix, exercise_5_3_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using hv 0
    have hyx2 : v 2 ≤ v 1 := by
      simpa [exercise_5_3_matrix, exercise_5_3_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using hv 1
    have hsum : v 0 + v 1 + 2 * v 2 ≤ 2 := by
      simpa [exercise_5_3_matrix, exercise_5_3_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using hv 2
    have hy : 0 ≤ v 2 := by
      have hnegY : -v 2 ≤ 0 := by
        simpa [exercise_5_3_matrix, exercise_5_3_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
          using hv 3
      linarith
    exact ⟨hyx1, hyx2, hsum, hy⟩
  · rintro ⟨hyx1, hyx2, hsum, hy⟩ i
    -- Each matrix row is one of the displayed inequalities.
    fin_cases i
    · simpa [exercise_5_3_matrix, exercise_5_3_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using hyx1
    · simpa [exercise_5_3_matrix, exercise_5_3_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using hyx2
    · simpa [exercise_5_3_matrix, exercise_5_3_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using hsum
    · have hnegY : -v 2 ≤ 0 := by
        linarith
      simpa [exercise_5_3_matrix, exercise_5_3_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using hnegY

/-- The mixed-integer set `S = P ∩ (ℤ^2 × ℝ)` from Exercise 5.3. -/
def exercise_5_3_mixed_integer_set : Set (Fin 3 → ℝ) :=
  mixed_integer_feasible_set
    exercise_5_3_matrix
    exercise_5_3_rhs
    exercise_5_3_integer_indices

/-- Membership in `exercise_5_3_mixed_integer_set` means belonging to `P` with `x₁` and `x₂`
integral. -/
theorem mem_exercise_5_3_mixed_integer_set_iff
    {v : Fin 3 → ℝ} :
    v ∈ exercise_5_3_mixed_integer_set ↔
      v ∈ exercise_5_3_polyhedron ∧
        (∃ z : ℤ, v 0 = (z : ℝ)) ∧
          ∃ z : ℤ, v 1 = (z : ℝ) := by
  rw [exercise_5_3_mixed_integer_set, mem_mixed_integer_feasible_set_iff]
  constructor
  · rintro ⟨hv, hint⟩
    -- Specialize the integrality condition to the two integer coordinates.
    have hvPoly : v ∈ exercise_5_3_polyhedron := by
      have hv' : v ∈ polyhedron_le_set exercise_5_3_matrix exercise_5_3_rhs := by
        exact (mem_polyhedron_le_set_iff).2 hv
      simpa [exercise_5_3_polyhedron] using hv'
    refine ⟨hvPoly, ?_, ?_⟩
    · exact hint 0 (by simp [exercise_5_3_integer_indices])
    · exact hint 1 (by simp [exercise_5_3_integer_indices])
  · rintro ⟨hv, hz0, hz1⟩
    -- Repackage the two displayed witnesses into the owner predicate over the index set.
    refine ⟨?_, ?_⟩
    · have hv' : v ∈ polyhedron_le_set exercise_5_3_matrix exercise_5_3_rhs := by
        simpa [exercise_5_3_polyhedron] using hv
      exact (mem_polyhedron_le_set_iff).1 hv'
    · intro j hj
      fin_cases j
      · simpa [exercise_5_3_integer_indices] using hz0
      · simpa [exercise_5_3_integer_indices] using hz1
      · simp [exercise_5_3_integer_indices] at hj

/-- The coefficient vector encoding the inequality `x₁ ≥ 3 y` as `α x ≤ 0`. -/
def exercise_5_3_x1_ge_three_y_coeffs : Fin 3 → ℝ :=
  ![-1, 0, 3]

/-- The coefficient vector encoding the inequality `x₂ ≥ 3 y` as `α x ≤ 0`. -/
def exercise_5_3_x2_ge_three_y_coeffs : Fin 3 → ℝ :=
  ![0, -1, 3]

/-- The split `x₁ ≤ 0 ∨ x₁ ≥ 1` over the integer variables `{x₁, x₂}` used to derive
`x₁ ≥ 3 y`. -/
def exercise_5_3_x1_split : Split exercise_5_3_integer_indices where
  π := ![(1 : ℤ), 0, 0]
  π0 := 0
  nonzero := by
    intro hπ
    have h0 := congrFun hπ 0
    norm_num at h0
  zero_on_continuous := by
    intro j hj
    fin_cases j <;> simp [exercise_5_3_integer_indices] at hj ⊢

/-- The split `x₂ ≤ 0 ∨ x₂ ≥ 1` over the integer variables `{x₁, x₂}` used to derive
`x₂ ≥ 3 y`. -/
def exercise_5_3_x2_split : Split exercise_5_3_integer_indices where
  π := ![0, (1 : ℤ), 0]
  π0 := 0
  nonzero := by
    intro hπ
    have h1 := congrFun hπ 1
    norm_num at h1
  zero_on_continuous := by
    intro j hj
    fin_cases j <;> simp [exercise_5_3_integer_indices] at hj ⊢

/-- Helper for Exercise 5.3: both branches of the `x₁`-coordinate split satisfy the inequality
`x₁ ≥ 3 y`. -/
lemma exercise_5_3_x1_split_branches_valid :
    is_valid_inequality
      (split_branch_lower
          exercise_5_3_polyhedron
          exercise_5_3_x1_split
          exercise_5_3_x1_split.π0
        ∪
        split_branch_upper
          exercise_5_3_polyhedron
          exercise_5_3_x1_split
          exercise_5_3_x1_split.π0)
      exercise_5_3_x1_ge_three_y_coeffs
      0 := by
  rw [is_valid_inequality_iff]
  intro v hv
  rcases hv with hv | hv
  · -- On the lower branch, `x₁ ≤ 0` together with `0 ≤ y ≤ x₁` forces `y = 0`.
    rcases (mem_split_branch_lower_iff).1 hv with ⟨hvP, hvSplit⟩
    rcases (mem_exercise_5_3_polyhedron_iff).1 hvP with ⟨hyx1, hyx2, hsum, hy⟩
    have hx1le : v 0 ≤ 0 := by
      simpa [exercise_5_3_x1_split, split_dot_eq_sum, Fin.sum_univ_three] using hvSplit
    have hyEq : v 2 = 0 := by
      linarith
    have hthree : 3 * v 2 ≤ v 0 := by
      nlinarith [hyx1, hyEq]
    have hdot : -v 0 + 3 * v 2 ≤ 0 := by
      linarith
    simpa [exercise_5_3_x1_ge_three_y_coeffs, dotProduct, Fin.sum_univ_three] using hdot
  · -- On the upper branch, `x₁ ≥ 1` and the polyhedron inequalities imply `3y ≤ 1 ≤ x₁`.
    rcases (mem_split_branch_upper_iff).1 hv with ⟨hvP, hvSplit⟩
    rcases (mem_exercise_5_3_polyhedron_iff).1 hvP with ⟨hyx1, hyx2, hsum, hy⟩
    have hx1ge : 1 ≤ v 0 := by
      simpa [exercise_5_3_x1_split, split_dot_eq_sum, Fin.sum_univ_three] using hvSplit
    have hthreeToOne : 3 * v 2 ≤ 1 := by
      linarith
    have hthree : 3 * v 2 ≤ v 0 := by
      linarith
    have hdot : -v 0 + 3 * v 2 ≤ 0 := by
      linarith
    simpa [exercise_5_3_x1_ge_three_y_coeffs, dotProduct, Fin.sum_univ_three] using hdot

/-- Helper for Exercise 5.3: both branches of the `x₂`-coordinate split satisfy the inequality
`x₂ ≥ 3 y`. -/
lemma exercise_5_3_x2_split_branches_valid :
    is_valid_inequality
      (split_branch_lower
          exercise_5_3_polyhedron
          exercise_5_3_x2_split
          exercise_5_3_x2_split.π0
        ∪
        split_branch_upper
          exercise_5_3_polyhedron
          exercise_5_3_x2_split
          exercise_5_3_x2_split.π0)
      exercise_5_3_x2_ge_three_y_coeffs
      0 := by
  rw [is_valid_inequality_iff]
  intro v hv
  rcases hv with hv | hv
  · -- On the lower branch, `x₂ ≤ 0` together with `0 ≤ y ≤ x₂` again forces `y = 0`.
    rcases (mem_split_branch_lower_iff).1 hv with ⟨hvP, hvSplit⟩
    rcases (mem_exercise_5_3_polyhedron_iff).1 hvP with ⟨hyx1, hyx2, hsum, hy⟩
    have hx2le : v 1 ≤ 0 := by
      simpa [exercise_5_3_x2_split, split_dot_eq_sum, Fin.sum_univ_three] using hvSplit
    have hyEq : v 2 = 0 := by
      linarith
    have hthree : 3 * v 2 ≤ v 1 := by
      nlinarith [hyx2, hyEq]
    have hdot : -v 1 + 3 * v 2 ≤ 0 := by
      linarith
    simpa [exercise_5_3_x2_ge_three_y_coeffs, dotProduct, Fin.sum_univ_three] using hdot
  · -- On the upper branch, `x₂ ≥ 1` and the polyhedron inequalities imply `3y ≤ 1 ≤ x₂`.
    rcases (mem_split_branch_upper_iff).1 hv with ⟨hvP, hvSplit⟩
    rcases (mem_exercise_5_3_polyhedron_iff).1 hvP with ⟨hyx1, hyx2, hsum, hy⟩
    have hx2ge : 1 ≤ v 1 := by
      simpa [exercise_5_3_x2_split, split_dot_eq_sum, Fin.sum_univ_three] using hvSplit
    have hthreeToOne : 3 * v 2 ≤ 1 := by
      linarith
    have hthree : 3 * v 2 ≤ v 1 := by
      linarith
    have hdot : -v 1 + 3 * v 2 ≤ 0 := by
      linarith
    simpa [exercise_5_3_x2_ge_three_y_coeffs, dotProduct, Fin.sum_univ_three] using hdot

/-- The inequality `x₁ ≥ 3 y` is valid on the split polyhedron of `exercise_5_3_x1_split`. -/
theorem exercise_5_3_x1_ge_three_y_valid_on_split_polyhedron
    {v : Fin 3 → ℝ}
    (hv : v ∈ split_polyhedron exercise_5_3_matrix exercise_5_3_rhs exercise_5_3_x1_split) :
    exercise_5_3_x1_ge_three_y_coeffs ⬝ᵥ v ≤ 0 := by
  -- Validity on the two split branches extends unchanged to their convex hull.
  have hvalid :
      is_valid_inequality
        (split_polyhedron exercise_5_3_matrix exercise_5_3_rhs exercise_5_3_x1_split)
        exercise_5_3_x1_ge_three_y_coeffs
        0 := by
    simpa [split_polyhedron, split_hull, exercise_5_3_polyhedron] using
      (is_valid_inequality_convexHull_iff
        (S :=
          split_branch_lower
              exercise_5_3_polyhedron
              exercise_5_3_x1_split
              exercise_5_3_x1_split.π0
            ∪
            split_branch_upper
              exercise_5_3_polyhedron
              exercise_5_3_x1_split
              exercise_5_3_x1_split.π0)
        (α := exercise_5_3_x1_ge_three_y_coeffs)
        (β := 0)).2 exercise_5_3_x1_split_branches_valid
  exact hvalid hv

/-- The inequality `x₂ ≥ 3 y` is valid on the split polyhedron of `exercise_5_3_x2_split`. -/
theorem exercise_5_3_x2_ge_three_y_valid_on_split_polyhedron
    {v : Fin 3 → ℝ}
    (hv : v ∈ split_polyhedron exercise_5_3_matrix exercise_5_3_rhs exercise_5_3_x2_split) :
    exercise_5_3_x2_ge_three_y_coeffs ⬝ᵥ v ≤ 0 := by
  -- The symmetric `x₂` branch argument also transfers from the union to the split hull.
  have hvalid :
      is_valid_inequality
        (split_polyhedron exercise_5_3_matrix exercise_5_3_rhs exercise_5_3_x2_split)
        exercise_5_3_x2_ge_three_y_coeffs
        0 := by
    simpa [split_polyhedron, split_hull, exercise_5_3_polyhedron] using
      (is_valid_inequality_convexHull_iff
        (S :=
          split_branch_lower
              exercise_5_3_polyhedron
              exercise_5_3_x2_split
              exercise_5_3_x2_split.π0
            ∪
            split_branch_upper
              exercise_5_3_polyhedron
              exercise_5_3_x2_split
              exercise_5_3_x2_split.π0)
        (α := exercise_5_3_x2_ge_three_y_coeffs)
        (β := 0)).2 exercise_5_3_x2_split_branches_valid
  exact hvalid hv

/-- First split certificate for Exercise 5.3: the inequality `x₁ ≥ 3 y` is a split
inequality for the mixed-integer set associated to `exercise_5_3_matrix`,
`exercise_5_3_rhs`, and `exercise_5_3_integer_indices`. -/
theorem exercise_5_3_x1_ge_three_y_is_split_inequality :
    IsSplitInequality exercise_5_3_matrix exercise_5_3_rhs
      exercise_5_3_integer_indices exercise_5_3_x1_ge_three_y_coeffs 0 := by
  rw [isSplitInequality_iff_valid_on_split_polyhedron]
  -- Package the explicit `x₁` split witness with the split-polyhedron validity theorem.
  refine ⟨exercise_5_3_x1_split, ?_⟩
  rw [is_valid_inequality_iff]
  intro v hv
  exact exercise_5_3_x1_ge_three_y_valid_on_split_polyhedron hv

/-- Second split certificate for Exercise 5.3: the inequality `x₂ ≥ 3 y` is a split
inequality for the mixed-integer set associated to `exercise_5_3_matrix`,
`exercise_5_3_rhs`, and `exercise_5_3_integer_indices`. -/
theorem exercise_5_3_x2_ge_three_y_is_split_inequality :
    IsSplitInequality exercise_5_3_matrix exercise_5_3_rhs
      exercise_5_3_integer_indices exercise_5_3_x2_ge_three_y_coeffs 0 := by
  rw [isSplitInequality_iff_valid_on_split_polyhedron]
  -- Package the explicit `x₂` split witness with the symmetric validity theorem.
  refine ⟨exercise_5_3_x2_split, ?_⟩
  rw [is_valid_inequality_iff]
  intro v hv
  exact exercise_5_3_x2_ge_three_y_valid_on_split_polyhedron hv

/-- Exercise 5.3. Both coordinate inequalities `x₁ ≥ 3 y` and `x₂ ≥ 3 y`
are split
inequalities for the mixed-integer set associated to `exercise_5_3_matrix`,
`exercise_5_3_rhs`, and `exercise_5_3_integer_indices`. -/
theorem exercise_5_3_split_inequalities :
    IsSplitInequality exercise_5_3_matrix exercise_5_3_rhs
      exercise_5_3_integer_indices exercise_5_3_x1_ge_three_y_coeffs 0 ∧
      IsSplitInequality exercise_5_3_matrix exercise_5_3_rhs
        exercise_5_3_integer_indices exercise_5_3_x2_ge_three_y_coeffs 0 := by
  -- The two coordinate-specific split certificates established above are exactly the claim.
  constructor
  · exact exercise_5_3_x1_ge_three_y_is_split_inequality
  · exact exercise_5_3_x2_ge_three_y_is_split_inequality

end Exercise53
