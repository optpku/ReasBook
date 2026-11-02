import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_definition_3_14_extra_1

open scoped Matrix

-- Source-facing layer: the exercise keeps its concrete `Fin 7 → ℝ` coordinate presentation.
-- Core/canonical layer: the LP relaxation is presented through the Chapter 3 owner
-- `standard_equality_form`.
--
-- Coordinate order: `(x₁, x₂, x₃, y₁, y₂, y₃, y₄)`.

section Exercise515

/-- The standard equality-form matrix for Exercise 5.15 in the coordinate order
`(x₁, x₂, x₃, y₁, y₂, y₃, y₄)`. -/
def exercise_5_15_matrix : Matrix (Fin 3) (Fin 7) ℝ :=
  ![![1, 3, 0, 4, 1, 0, 0],
    ![5, 1, 3, 0, 0, 1, 0],
    ![0, 0, 2, 2, 0, 0, -1]]

/-- The right-hand side vector for the standard equality-form presentation of Exercise 5.15. -/
def exercise_5_15_rhs : Fin 3 → ℝ :=
  ![11, 12, 3]

/-- The integer-variable index set `{x₁, x₂, x₃}` from Exercise 5.15. -/
def exercise_5_15_integer_indices : Finset (Fin 7) :=
  {0, 1, 2}

/-- The LP relaxation of Exercise 5.15 in the coordinate order
`(x₁, x₂, x₃, y₁, y₂, y₃, y₄)`. -/
def exercise_5_15_relaxation : Set (Fin 7 → ℝ) :=
  standard_equality_form exercise_5_15_matrix exercise_5_15_rhs

/-- Membership in `exercise_5_15_relaxation` means satisfying the three displayed equations and
coordinatewise nonnegativity. -/
theorem mem_exercise_5_15_relaxation_iff
    {v : Fin 7 → ℝ} :
    v ∈ exercise_5_15_relaxation ↔
      0 ≤ v ∧
        v 0 + 3 * v 1 + 4 * v 3 + v 4 = 11 ∧
          5 * v 0 + v 1 + 3 * v 2 + v 5 = 12 ∧
            2 * v 2 + 2 * v 3 - v 6 = 3 := by
  rw [exercise_5_15_relaxation, mem_standard_equality_form_iff]
  constructor
  · rintro ⟨hAx, hnonneg⟩
    -- Read the three displayed equations by projecting the matrix equality row by row.
    have hrow1 := congrFun hAx 0
    have hrow2 := congrFun hAx 1
    have hrow3 := congrFun hAx 2
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hrow1 hrow2 hrow3
    norm_num [exercise_5_15_matrix, exercise_5_15_rhs] at hrow1 hrow2 hrow3
    refine ⟨hnonneg, ?_, ?_, ?_⟩
    · simpa [add_assoc, sub_eq_add_neg] using hrow1
    · simpa [add_assoc, sub_eq_add_neg] using hrow2
    · simpa [add_assoc, sub_eq_add_neg] using hrow3
  · rintro ⟨hnonneg, hrow1, hrow2, hrow3⟩
    -- Reassemble the owner-side matrix equation from the three scalar rows.
    refine ⟨?_, hnonneg⟩
    ext i
    fin_cases i
    · norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, exercise_5_15_matrix,
        exercise_5_15_rhs]
      simpa [add_assoc, sub_eq_add_neg] using hrow1
    · norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, exercise_5_15_matrix,
        exercise_5_15_rhs]
      simpa [add_assoc, sub_eq_add_neg] using hrow2
    · norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, exercise_5_15_matrix,
        exercise_5_15_rhs]
      simpa [add_assoc, sub_eq_add_neg] using hrow3

/-- The mixed-integer feasible set of Exercise 5.15, where `x₁`, `x₂`, and `x₃` are integral
and all variables are nonnegative. This is the source-facing specialization of the Chapter 3
standard equality-form owner with integrality imposed on `exercise_5_15_integer_indices`. -/
def exercise_5_15_mixed_integer_feasible_set : Set (Fin 7 → ℝ) :=
  exercise_5_15_relaxation ∩
    {v : Fin 7 → ℝ |
      ∀ j ∈ exercise_5_15_integer_indices, ∃ z : ℤ, v j = (z : ℝ)}

/-- Membership in `exercise_5_15_mixed_integer_feasible_set` means LP feasibility together with
integrality of `x₁`, `x₂`, and `x₃`. -/
theorem mem_exercise_5_15_mixed_integer_feasible_set_iff
    {v : Fin 7 → ℝ} :
    v ∈ exercise_5_15_mixed_integer_feasible_set ↔
      v ∈ exercise_5_15_relaxation ∧
        (∃ z : ℤ, v 0 = (z : ℝ)) ∧
          (∃ z : ℤ, v 1 = (z : ℝ)) ∧
            ∃ z : ℤ, v 2 = (z : ℝ) := by
  constructor
  · rintro ⟨hv, hint⟩
    refine ⟨hv, ?_, ?_, ?_⟩
    · exact hint 0 (by simp [exercise_5_15_integer_indices])
    · exact hint 1 (by simp [exercise_5_15_integer_indices])
    · exact hint 2 (by simp [exercise_5_15_integer_indices])
  · rintro ⟨hv, hz0, hz1, hz2⟩
    refine ⟨hv, ?_⟩
    intro j hj
    fin_cases j
    · simpa [exercise_5_15_integer_indices] using hz0
    · simpa [exercise_5_15_integer_indices] using hz1
    · simpa [exercise_5_15_integer_indices] using hz2
    · simp [exercise_5_15_integer_indices] at hj
    · simp [exercise_5_15_integer_indices] at hj
    · simp [exercise_5_15_integer_indices] at hj
    · simp [exercise_5_15_integer_indices] at hj

/-- The fractional LP optimum of Exercise 5.15, written with the exact rational values matching
the displayed decimals `2.214`, `0.929`, and `1.5`. -/
noncomputable def exercise_5_15_fractional_solution : Fin 7 → ℝ :=
  ![(31 : ℝ) / 14, (13 : ℝ) / 14, 0, (3 : ℝ) / 2, 0, 0, 0]

/-- A mixed-integer feasible point where both Gomory mixed integer cuts are tight. -/
noncomputable def exercise_5_15_boundary_point : Fin 7 → ℝ :=
  ![(2 : ℝ), (1 : ℝ), 0, (3 : ℝ) / 2, 0, (1 : ℝ), 0]

/-- The Gomory mixed integer inequality `11 ≤ 3 x₃ + y₂ + 11 y₃ + 2 y₄` obtained from the
displayed `x₁`-basic tableau row. -/
def exercise_5_15_first_cut : Set (Fin 7 → ℝ) :=
  {v : Fin 7 → ℝ | 11 ≤ 3 * v 2 + v 4 + 11 * v 5 + 2 * v 6}

/-- Membership in `exercise_5_15_first_cut` is exactly the inequality
`11 ≤ 3 x₃ + y₂ + 11 y₃ + 2 y₄`. -/
theorem mem_exercise_5_15_first_cut_iff
    {v : Fin 7 → ℝ} :
    v ∈ exercise_5_15_first_cut ↔
      11 ≤ 3 * v 2 + v 4 + 11 * v 5 + 2 * v 6 :=
  Iff.rfl

/-- The Gomory mixed integer inequality `13 ≤ x₃ + 5 y₂ + 13 y₃ + 10 y₄` obtained from the
displayed `x₂`-basic tableau row. -/
def exercise_5_15_second_cut : Set (Fin 7 → ℝ) :=
  {v : Fin 7 → ℝ | 13 ≤ v 2 + 5 * v 4 + 13 * v 5 + 10 * v 6}

/-- Membership in `exercise_5_15_second_cut` is exactly the inequality
`13 ≤ x₃ + 5 y₂ + 13 y₃ + 10 y₄`. -/
theorem mem_exercise_5_15_second_cut_iff
    {v : Fin 7 → ℝ} :
    v ∈ exercise_5_15_second_cut ↔
      13 ≤ v 2 + 5 * v 4 + 13 * v 5 + 10 * v 6 :=
  Iff.rfl

/-- Helper for Exercise 5.15: eliminating `y₂`, `y₃`, and `y₄` from the first rounded cut turns
its left-hand side into an affine expression in `x₁`, `x₂`, and `x₃`. -/
lemma exercise_5_15_first_cut_left_side_eq
    {v : Fin 7 → ℝ}
    (hv : v ∈ exercise_5_15_relaxation) :
    3 * v 2 + v 4 + 11 * v 5 + 2 * v 6 =
      137 - 56 * v 0 - 14 * v 1 - 26 * v 2 := by
  rw [mem_exercise_5_15_relaxation_iff] at hv
  rcases hv with ⟨-, hrow1, hrow2, hrow3⟩
  -- The original three equations eliminate the continuous variables in one linear step.
  linarith

/-- Helper for Exercise 5.15: eliminating `y₂`, `y₃`, and `y₄` from the second rounded cut turns
its left-hand side into an affine expression in `x₁`, `x₂`, and `x₃`. -/
lemma exercise_5_15_second_cut_left_side_eq
    {v : Fin 7 → ℝ}
    (hv : v ∈ exercise_5_15_relaxation) :
    v 2 + 5 * v 4 + 13 * v 5 + 10 * v 6 =
      181 - 70 * v 0 - 28 * v 1 - 18 * v 2 := by
  rw [mem_exercise_5_15_relaxation_iff] at hv
  rcases hv with ⟨-, hrow1, hrow2, hrow3⟩
  -- The same row elimination exposes the second cut as integer-coordinate arithmetic.
  linarith

/-- Helper for Exercise 5.15: every mixed-integer feasible point has integral coordinates
`x₁`, `x₂`, and `x₃` in the small ranges needed for finite case analysis. -/
lemma exercise_5_15_integer_coordinate_bounds
    {v : Fin 7 → ℝ}
    (hv : v ∈ exercise_5_15_mixed_integer_feasible_set) :
    ∃ z0 z1 z2 : ℤ,
      v 0 = (z0 : ℝ) ∧
        v 1 = (z1 : ℝ) ∧
          v 2 = (z2 : ℝ) ∧
            0 ≤ z0 ∧ z0 ≤ 2 ∧ 0 ≤ z1 ∧ z1 ≤ 3 ∧ 0 ≤ z2 ∧ z2 ≤ 4 := by
  rw [mem_exercise_5_15_mixed_integer_feasible_set_iff] at hv
  rcases hv with ⟨hvrel, ⟨z0, hz0⟩, ⟨z1, hz1⟩, ⟨z2, hz2⟩⟩
  rw [mem_exercise_5_15_relaxation_iff] at hvrel
  rcases hvrel with ⟨hnonneg, hrow1, hrow2, hrow3⟩
  have hz0_nonneg_real : 0 ≤ (z0 : ℝ) := by
    simpa [hz0] using hnonneg 0
  have hz1_nonneg_real : 0 ≤ (z1 : ℝ) := by
    simpa [hz1] using hnonneg 1
  have hz2_nonneg_real : 0 ≤ (z2 : ℝ) := by
    simpa [hz2] using hnonneg 2
  have hz0_nonneg : 0 ≤ z0 := by
    exact_mod_cast hz0_nonneg_real
  have hz1_nonneg : 0 ≤ z1 := by
    exact_mod_cast hz1_nonneg_real
  have hz2_nonneg : 0 ≤ z2 := by
    exact_mod_cast hz2_nonneg_real
  have hz0_mul_bound_real : 5 * (z0 : ℝ) ≤ 12 := by
    have hv1_nonneg : 0 ≤ v 1 := by simpa using hnonneg 1
    have hv2_nonneg : 0 ≤ v 2 := by simpa using hnonneg 2
    have hv5_nonneg : 0 ≤ v 5 := by simpa using hnonneg 5
    linarith [hrow2, hz0, hv1_nonneg, hv2_nonneg, hv5_nonneg]
  have hz1_mul_bound_real : 3 * (z1 : ℝ) ≤ 11 := by
    have hv0_nonneg : 0 ≤ v 0 := by simpa using hnonneg 0
    have hv3_nonneg : 0 ≤ v 3 := by simpa using hnonneg 3
    have hv4_nonneg : 0 ≤ v 4 := by simpa using hnonneg 4
    linarith [hrow1, hz1, hv0_nonneg, hv3_nonneg, hv4_nonneg]
  have hz2_mul_bound_real : 3 * (z2 : ℝ) ≤ 12 := by
    have hv0_nonneg : 0 ≤ v 0 := by simpa using hnonneg 0
    have hv1_nonneg : 0 ≤ v 1 := by simpa using hnonneg 1
    have hv5_nonneg : 0 ≤ v 5 := by simpa using hnonneg 5
    linarith [hrow2, hz2, hv0_nonneg, hv1_nonneg, hv5_nonneg]
  have hz0_mul_bound : (5 : ℤ) * z0 ≤ 12 := by
    exact_mod_cast hz0_mul_bound_real
  have hz1_mul_bound : (3 : ℤ) * z1 ≤ 11 := by
    exact_mod_cast hz1_mul_bound_real
  have hz2_mul_bound : (3 : ℤ) * z2 ≤ 12 := by
    exact_mod_cast hz2_mul_bound_real
  have hz0_le_two : z0 ≤ 2 := by
    omega
  have hz1_le_three : z1 ≤ 3 := by
    omega
  have hz2_le_four : z2 ≤ 4 := by
    omega
  exact ⟨z0, z1, z2, hz0, hz1, hz2, hz0_nonneg, hz0_le_two, hz1_nonneg, hz1_le_three,
    hz2_nonneg, hz2_le_four⟩

/-- Helper for Exercise 5.15: every mixed-integer feasible point satisfies the two integer row
inequalities obtained from the original system after eliminating the continuous slack variables,
together with the small coordinate bounds already forced by nonnegativity. -/
lemma exercise_5_15_integer_row_constraints
    {v : Fin 7 → ℝ}
    (hv : v ∈ exercise_5_15_mixed_integer_feasible_set) :
    ∃ z0 z1 z2 : ℤ,
      v 0 = (z0 : ℝ) ∧
        v 1 = (z1 : ℝ) ∧
          v 2 = (z2 : ℝ) ∧
            0 ≤ z0 ∧
              z0 ≤ 2 ∧
                0 ≤ z1 ∧
                  z1 ≤ 3 ∧
                    0 ≤ z2 ∧
                      z2 ≤ 4 ∧
                        5 * z0 + z1 + 3 * z2 ≤ 12 ∧
                          z0 + 3 * z1 - 4 * z2 ≤ 5 := by
  have hvrel : v ∈ exercise_5_15_relaxation :=
    (mem_exercise_5_15_mixed_integer_feasible_set_iff.mp hv).1
  obtain ⟨z0, z1, z2, hz0, hz1, hz2, hz0_nonneg, hz0_le_two, hz1_nonneg, hz1_le_three,
      hz2_nonneg, hz2_le_four⟩ :=
    exercise_5_15_integer_coordinate_bounds hv
  rw [mem_exercise_5_15_relaxation_iff] at hvrel
  rcases hvrel with ⟨hnonneg, hrow1, hrow2, hrow3⟩
  -- Project the original rows to integer inequalities once the integer coordinates are fixed.
  have hrow2_bound_real : 5 * (z0 : ℝ) + (z1 : ℝ) + 3 * (z2 : ℝ) ≤ 12 := by
    have hv5_nonneg : 0 ≤ v 5 := by
      simpa using hnonneg 5
    linarith [hrow2, hz0, hz1, hz2, hv5_nonneg]
  have hrow13_bound_real : (z0 : ℝ) + 3 * (z1 : ℝ) - 4 * (z2 : ℝ) ≤ 5 := by
    have hv4_nonneg : 0 ≤ v 4 := by
      simpa using hnonneg 4
    have hv6_nonneg : 0 ≤ v 6 := by
      simpa using hnonneg 6
    linarith [hrow1, hrow3, hz0, hz1, hz2, hv4_nonneg, hv6_nonneg]
  have hrow2_bound : 5 * z0 + z1 + 3 * z2 ≤ 12 := by
    exact_mod_cast hrow2_bound_real
  have hrow13_bound : z0 + 3 * z1 - 4 * z2 ≤ 5 := by
    exact_mod_cast hrow13_bound_real
  exact ⟨z0, z1, z2, hz0, hz1, hz2, hz0_nonneg, hz0_le_two, hz1_nonneg, hz1_le_three,
    hz2_nonneg, hz2_le_four, hrow2_bound, hrow13_bound⟩

/-- Helper for Exercise 5.15: every mixed-integer feasible point satisfies the first rounded
Gomory mixed integer cut. -/
lemma exercise_5_15_mixed_integer_feasible_mem_first_cut
    {v : Fin 7 → ℝ}
    (hv : v ∈ exercise_5_15_mixed_integer_feasible_set) :
    v ∈ exercise_5_15_first_cut := by
  have hvrel : v ∈ exercise_5_15_relaxation :=
    (mem_exercise_5_15_mixed_integer_feasible_set_iff.mp hv).1
  obtain ⟨z0, z1, z2, hz0, hz1, hz2, hz0_nonneg, hz0_le_two, hz1_nonneg, hz1_le_three,
      hz2_nonneg, hz2_le_four, hrow2, hrow13⟩ :=
    exercise_5_15_integer_row_constraints hv
  rw [mem_exercise_5_15_first_cut_iff]
  -- Route correction: keep the cut in affine normal form, then discharge the remaining Presburger
  -- arithmetic over the integral coordinates only.
  rw [exercise_5_15_first_cut_left_side_eq hvrel, hz0, hz1, hz2]
  have hcut : (11 : ℤ) ≤ 137 - 56 * z0 - 14 * z1 - 26 * z2 := by
    interval_cases z0 <;> interval_cases z1 <;> interval_cases z2 <;> omega
  exact_mod_cast hcut

/-- Helper for Exercise 5.15: every mixed-integer feasible point satisfies the second rounded
Gomory mixed integer cut. -/
lemma exercise_5_15_mixed_integer_feasible_mem_second_cut
    {v : Fin 7 → ℝ}
    (hv : v ∈ exercise_5_15_mixed_integer_feasible_set) :
    v ∈ exercise_5_15_second_cut := by
  have hvrel : v ∈ exercise_5_15_relaxation :=
    (mem_exercise_5_15_mixed_integer_feasible_set_iff.mp hv).1
  obtain ⟨z0, z1, z2, hz0, hz1, hz2, hz0_nonneg, hz0_le_two, hz1_nonneg, hz1_le_three,
      hz2_nonneg, hz2_le_four, hrow2, hrow13⟩ :=
    exercise_5_15_integer_row_constraints hv
  rw [mem_exercise_5_15_second_cut_iff]
  -- Route correction: reuse the same integer row summary and close the different affine bound in
  -- `ℤ` before casting back to the real cut inequality.
  rw [exercise_5_15_second_cut_left_side_eq hvrel, hz0, hz1, hz2]
  have hcut : (13 : ℤ) ≤ 181 - 70 * z0 - 28 * z1 - 18 * z2 := by
    interval_cases z0 <;> interval_cases z1 <;> interval_cases z2 <;> omega
  exact_mod_cast hcut

/-- A rational number is compatible with a displayed decimal rounded to three places when it lies
within one half-thousandth of that display. -/
def rounds_to_three_decimals (exact displayed : ℚ) : Prop :=
  |(exact : ℝ) - displayed| < (1 : ℝ) / 2000

/-- Exercise 5.15 (1). The Gomory mixed integer inequality obtained from the displayed
`x₁`-basic row is valid for every mixed-integer feasible point of the original problem and cuts
off the fractional LP optimum. -/
theorem exercise_5_15_first_gomory_mixed_integer_inequality :
    exercise_5_15_mixed_integer_feasible_set ⊆ exercise_5_15_first_cut ∧
      exercise_5_15_fractional_solution ∉ exercise_5_15_first_cut := by
  constructor
  · intro v hv
    -- Reuse the normalization-and-bounds helper instead of repeating the tableau elimination.
    exact exercise_5_15_mixed_integer_feasible_mem_first_cut hv
  · intro hfrac
    -- The displayed fractional LP optimum violates the first rounded cut numerically.
    rw [mem_exercise_5_15_first_cut_iff] at hfrac
    simp [exercise_5_15_fractional_solution] at hfrac
    norm_num at hfrac

/-- Exercise 5.15 (2). The Gomory mixed integer inequality obtained from the displayed
`x₂`-basic row is valid for every mixed-integer feasible point of the original problem and cuts
off the fractional LP optimum. -/
theorem exercise_5_15_second_gomory_mixed_integer_inequality :
    exercise_5_15_mixed_integer_feasible_set ⊆ exercise_5_15_second_cut ∧
      exercise_5_15_fractional_solution ∉ exercise_5_15_second_cut := by
  constructor
  · intro v hv
    -- The second rounded cut is proved by the same bounded integer frontier.
    exact exercise_5_15_mixed_integer_feasible_mem_second_cut hv
  · intro hfrac
    -- The fractional LP optimum also violates the second rounded cut numerically.
    rw [mem_exercise_5_15_second_cut_iff] at hfrac
    simp [exercise_5_15_fractional_solution] at hfrac
    norm_num at hfrac

/-- Exercise 5.15 (3). The boundary point `(2, 1, 0, 3/2, 0, 1, 0)` remains feasible for the
mixed-integer program in the rounding example. -/
theorem exercise_5_15_rounding_example_boundary_point_feasible :
    exercise_5_15_boundary_point ∈ exercise_5_15_mixed_integer_feasible_set := by
  rw [mem_exercise_5_15_mixed_integer_feasible_set_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_exercise_5_15_relaxation_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Check coordinatewise nonnegativity of the explicit boundary point.
      intro i
      fin_cases i
      · norm_num [exercise_5_15_boundary_point]
      · norm_num [exercise_5_15_boundary_point]
      · norm_num [exercise_5_15_boundary_point]
      · norm_num [exercise_5_15_boundary_point]
      · norm_num [exercise_5_15_boundary_point]
      · norm_num [exercise_5_15_boundary_point]
      · norm_num [exercise_5_15_boundary_point]
    · simp [exercise_5_15_boundary_point]
      norm_num
    · simp [exercise_5_15_boundary_point]
      norm_num
    · simp [exercise_5_15_boundary_point]
      norm_num
  · -- Exhibit the integral value of `x₁`.
    refine ⟨2, ?_⟩
    simp [exercise_5_15_boundary_point]
  · -- Exhibit the integral value of `x₂`.
    refine ⟨1, ?_⟩
    simp [exercise_5_15_boundary_point]
  · -- Exhibit the integral value of `x₃`.
    refine ⟨0, ?_⟩
    simp [exercise_5_15_boundary_point]

/-- Exercise 5.15 (4). The exact `y₃` coefficient `0.2136` in the rounding example still
rounds to the displayed decimal `0.214`. -/
theorem exercise_5_15_rounding_example_y3_coefficient_rounds :
    rounds_to_three_decimals ((267 : ℚ) / 1250) ((107 : ℚ) / 500) := by
  -- The exact coefficient differs from the displayed one by `0.0004`, which is below `0.0005`.
  norm_num [rounds_to_three_decimals]

/-- Exercise 5.15 (5). The exact right-hand side `2.2144` in the rounding example still
rounds to the displayed decimal `2.214`. -/
theorem exercise_5_15_rounding_example_rhs_rounds :
    rounds_to_three_decimals ((1384 : ℚ) / 625) ((1107 : ℚ) / 500) := by
  -- The exact right-hand side differs from the displayed one by `0.0004` as well.
  norm_num [rounds_to_three_decimals]

/-- Exercise 5.15 (6). For the rounded-row example, the normalized `y₃` coefficient is less
than `1`, so the displayed cut would exclude the feasible boundary point. -/
theorem exercise_5_15_rounding_example_normalized_y3_coefficient_too_small :
    ¬ (1 ≤
      ((((267 : ℚ) / 1250 : ℝ) / (Int.fract ((1384 : ℚ) / 625) : ℝ)) *
        exercise_5_15_boundary_point 5)) := by
  -- Evaluate the exact fractional part of the rounded right-hand side before comparing.
  have hfract : (Int.fract ((1384 : ℚ) / 625) : ℝ) = 134 / 625 := by
    norm_num [Int.fract]
  rw [hfract]
  -- The normalized displayed coefficient is `267 / 268`, so it stays below `1`.
  simp [exercise_5_15_boundary_point]
  norm_num

end Exercise515
