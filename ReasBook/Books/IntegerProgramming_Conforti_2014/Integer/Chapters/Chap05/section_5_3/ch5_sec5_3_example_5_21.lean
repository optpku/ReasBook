/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped Matrix

section Example521

/-- The objective coefficient vector `(5.5, 2.1)` of the pure integer program in Example 5.21. -/
noncomputable def example_5_21_objective_coefficients : Fin 2 → ℝ :=
  ![((11 : ℝ) / 2), ((21 : ℝ) / 10)]

/-- The objective `z = 5.5 x₁ + 2.1 x₂` of the pure integer program in Example 5.21. -/
noncomputable def example_5_21_objective (x : Fin 2 → ℝ) : ℝ :=
  example_5_21_objective_coefficients ⬝ᵥ x

/-- The matrix encoding the four inequalities of the LP relaxation in Example 5.21:
`-x₁ ≤ 0`, `-x₂ ≤ 0`, `-x₁ + x₂ ≤ 2`, and `8 x₁ + 2 x₂ ≤ 17`. -/
def example_5_21_constraint_matrix : Matrix (Fin 4) (Fin 2) ℝ :=
  !![-(1 : ℝ), 0;
    0, -(1 : ℝ);
    -(1 : ℝ), 1;
    8, 2]

/-- The right-hand side vector `(0, 0, 2, 17)` of the LP relaxation in Example 5.21. -/
def example_5_21_constraint_rhs : Fin 4 → ℝ :=
  ![(0 : ℝ), 0, 2, 17]

/-- Both variables of Example 5.21 are required to be integral. -/
def example_5_21_integer_variable_indices : Finset (Fin 2) :=
  Finset.univ

/-- The original linear programming relaxation from Example 5.21. -/
def example_5_21_relaxation : Set (Fin 2 → ℝ) :=
  polyhedron_le_set example_5_21_constraint_matrix example_5_21_constraint_rhs

/-- Membership in `example_5_21_relaxation` is exactly the explicit nonnegativity and
constraint system of the original relaxation. -/
theorem mem_example_5_21_relaxation_iff
    {x : Fin 2 → ℝ} :
    x ∈ example_5_21_relaxation ↔
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ -x 0 + x 1 ≤ 2 ∧ 8 * x 0 + 2 * x 1 ≤ 17 := by
  -- Unfold the polyhedron definition and read each of the four rows separately.
  rw [example_5_21_relaxation, polyhedron_le_set]
  constructor
  · intro hx
    have h0 : -x 0 ≤ 0 := by
      simpa [example_5_21_constraint_matrix, example_5_21_constraint_rhs, dotProduct,
        Fin.sum_univ_two] using hx 0
    have h1 : -x 1 ≤ 0 := by
      simpa [example_5_21_constraint_matrix, example_5_21_constraint_rhs, dotProduct,
        Fin.sum_univ_two] using hx 1
    have h2 : -x 0 + x 1 ≤ 2 := by
      simpa [example_5_21_constraint_matrix, example_5_21_constraint_rhs, dotProduct,
        Fin.sum_univ_two] using hx 2
    have h3 : 8 * x 0 + 2 * x 1 ≤ 17 := by
      simpa [example_5_21_constraint_matrix, example_5_21_constraint_rhs, dotProduct,
        Fin.sum_univ_two] using hx 3
    refine ⟨?_, ?_, ?_, h3⟩
    · linarith
    · linarith
    · linarith
  · rintro ⟨hx0, hx1, hrow₁, hrow₂⟩ i
    fin_cases i
    · simp [example_5_21_constraint_matrix, example_5_21_constraint_rhs, dotProduct,
        Fin.sum_univ_two]
      linarith
    · simp [example_5_21_constraint_matrix, example_5_21_constraint_rhs, dotProduct,
        Fin.sum_univ_two]
      linarith
    · simp [example_5_21_constraint_matrix, example_5_21_constraint_rhs, dotProduct,
        Fin.sum_univ_two]
      linarith
    · simpa [example_5_21_constraint_matrix, example_5_21_constraint_rhs, dotProduct,
        Fin.sum_univ_two] using hrow₂

/-- The embedded integer-feasible points of the original pure integer program in Example 5.21. -/
def example_5_21_integer_feasible_set : Set (Fin 2 → ℝ) :=
  mixed_integer_feasible_set
    example_5_21_constraint_matrix
    example_5_21_constraint_rhs
    example_5_21_integer_variable_indices

/-- Membership in `example_5_21_integer_feasible_set` means feasibility in the original
relaxation together with integrality of both coordinates. -/
theorem mem_example_5_21_integer_feasible_set_iff
    {x : Fin 2 → ℝ} :
    x ∈ example_5_21_integer_feasible_set ↔
      x ∈ example_5_21_relaxation ∧
        x 0 ∈ Set.range (fun z : ℤ ↦ (z : ℝ)) ∧
          x 1 ∈ Set.range (fun z : ℤ ↦ (z : ℝ)) := by
  -- Expand the mixed-integer set and read the two integrality conditions coordinatewise.
  rw [example_5_21_integer_feasible_set, mem_mixed_integer_feasible_set_iff]
  constructor
  · intro hx
    rcases hx with ⟨hxrel, hint⟩
    refine ⟨hxrel, ?_, ?_⟩
    · rcases hint 0 (by simp [example_5_21_integer_variable_indices]) with ⟨z, hz⟩
      exact ⟨z, hz.symm⟩
    · rcases hint 1 (by simp [example_5_21_integer_variable_indices]) with ⟨z, hz⟩
      exact ⟨z, hz.symm⟩
  · rintro ⟨hxrel, hx0, hx1⟩
    refine ⟨hxrel, ?_⟩
    intro j hj
    fin_cases j
    · rcases hx0 with ⟨z, hz⟩
      exact ⟨z, hz.symm⟩
    · rcases hx1 with ⟨z, hz⟩
      exact ⟨z, hz.symm⟩

/-- The coefficient vector `(5, 2)` of the first Gomory mixed integer cut. -/
def example_5_21_first_cut_coefficients : Fin 2 → ℝ :=
  ![(5 : ℝ), 2]

/-- The Gomory mixed integer cut `5 x₁ + 2 x₂ ≤ 11` obtained after the first tableau. -/
def example_5_21_first_cut : Set (Fin 2 → ℝ) :=
  {x | example_5_21_first_cut_coefficients ⬝ᵥ x ≤ 11}

/-- Membership in `example_5_21_first_cut` is the inequality `5 x₁ + 2 x₂ ≤ 11`. -/
theorem mem_example_5_21_first_cut_iff
    {x : Fin 2 → ℝ} :
    x ∈ example_5_21_first_cut ↔ 5 * x 0 + 2 * x 1 ≤ 11 := by
  -- Expand the `Fin 2` dot product in the displayed cut.
  simp [example_5_21_first_cut, example_5_21_first_cut_coefficients, dotProduct,
    Fin.sum_univ_two]

/-- The coefficient vector `(0, 1)` of the Gomory fractional cut. -/
def example_5_21_fractional_cut_coefficients : Fin 2 → ℝ :=
  ![(0 : ℝ), 1]

/-- The Gomory fractional cut `x₂ ≤ 3` generated from the same tableau row. -/
def example_5_21_fractional_cut : Set (Fin 2 → ℝ) :=
  {x | example_5_21_fractional_cut_coefficients ⬝ᵥ x ≤ 3}

/-- Membership in `example_5_21_fractional_cut` is the inequality `x₂ ≤ 3`. -/
theorem mem_example_5_21_fractional_cut_iff
    {x : Fin 2 → ℝ} :
    x ∈ example_5_21_fractional_cut ↔ x 1 ≤ 3 := by
  -- Expand the `Fin 2` dot product in the fractional cut.
  simp [example_5_21_fractional_cut, example_5_21_fractional_cut_coefficients, dotProduct,
    Fin.sum_univ_two]

/-- The relaxation obtained by adding the first Gomory mixed integer cut. -/
def example_5_21_first_strengthened_relaxation : Set (Fin 2 → ℝ) :=
  example_5_21_relaxation ∩ example_5_21_first_cut

/-- Membership in `example_5_21_first_strengthened_relaxation` means satisfying the original
relaxation and the first Gomory mixed integer cut. -/
theorem mem_example_5_21_first_strengthened_relaxation_iff
    {x : Fin 2 → ℝ} :
    x ∈ example_5_21_first_strengthened_relaxation ↔
      x ∈ example_5_21_relaxation ∧ x ∈ example_5_21_first_cut := by
  -- The first strengthened relaxation is defined as an intersection.
  rfl

/-- The coefficient vector `(3, 1)` of the second Gomory mixed integer cut. -/
def example_5_21_second_cut_coefficients : Fin 2 → ℝ :=
  ![(3 : ℝ), 1]

/-- The Gomory mixed integer cut `3 x₁ + x₂ ≤ 6` obtained after resolving once. -/
def example_5_21_second_cut : Set (Fin 2 → ℝ) :=
  {x | example_5_21_second_cut_coefficients ⬝ᵥ x ≤ 6}

/-- Membership in `example_5_21_second_cut` is the inequality `3 x₁ + x₂ ≤ 6`. -/
theorem mem_example_5_21_second_cut_iff
    {x : Fin 2 → ℝ} :
    x ∈ example_5_21_second_cut ↔ 3 * x 0 + x 1 ≤ 6 := by
  -- Expand the `Fin 2` dot product in the second cut.
  simp [example_5_21_second_cut, example_5_21_second_cut_coefficients, dotProduct,
    Fin.sum_univ_two]

/-- The relaxation obtained after adding both Gomory mixed integer cuts from Example 5.21. -/
def example_5_21_second_strengthened_relaxation : Set (Fin 2 → ℝ) :=
  example_5_21_first_strengthened_relaxation ∩ example_5_21_second_cut

/-- Membership in `example_5_21_second_strengthened_relaxation` means satisfying the first
strengthened relaxation together with the second Gomory mixed integer cut. -/
theorem mem_example_5_21_second_strengthened_relaxation_iff
    {x : Fin 2 → ℝ} :
    x ∈ example_5_21_second_strengthened_relaxation ↔
      x ∈ example_5_21_first_strengthened_relaxation ∧ x ∈ example_5_21_second_cut := by
  -- The second strengthened relaxation is also defined as an intersection.
  rfl

/-- The fractional optimum `(1.3, 3.3)` of the original LP relaxation from Example 5.21. -/
noncomputable def example_5_21_fractional_solution : Fin 2 → ℝ :=
  ![(13 : ℝ) / 10, (33 : ℝ) / 10]

/-- The final integer solution `(1, 3)` obtained after adding the two Gomory mixed integer cuts
in Example 5.21. -/
def example_5_21_final_solution : Fin 2 → ℝ :=
  ![(1 : ℝ), (3 : ℝ)]

/-- Helper for Example 5.21: the objective is a positive linear combination of the two cut
left-hand sides used in the final optimality argument. -/
lemma example_5_21_objective_eq_cut_combination
    (x : Fin 2 → ℝ) :
    example_5_21_objective x =
      (4 / 5 : ℝ) * (5 * x 0 + 2 * x 1) + (1 / 2 : ℝ) * (3 * x 0 + x 1) := by
  -- Expand the objective dot product and collect coefficients to match the two cuts.
  simp [example_5_21_objective, example_5_21_objective_coefficients, dotProduct,
    Fin.sum_univ_two]
  ring

/-- Helper for Example 5.21: every integer-feasible point has first coordinate equal to an
integer between `0` and `2`. -/
lemma example_5_21_integer_feasible_x0_bounds
    {x : Fin 2 → ℝ}
    (hx : x ∈ example_5_21_integer_feasible_set) :
    ∃ z : ℤ, x 0 = (z : ℝ) ∧ 0 ≤ z ∧ z ≤ 2 := by
  -- Read off integrality of `x₁` and use the relaxation constraints to bound it.
  rw [mem_example_5_21_integer_feasible_set_iff] at hx
  rcases hx with ⟨hxrel, hx0, -⟩
  rcases hx0 with ⟨z, hz⟩
  rw [mem_example_5_21_relaxation_iff] at hxrel
  rcases hxrel with ⟨hx0_nonneg, hx1_nonneg, -, hrow₂⟩
  have hx0_eq : x 0 = (z : ℝ) := by
    simpa using hz.symm
  have hz_nonneg_real : 0 ≤ (z : ℝ) := by
    simpa [hx0_eq] using hx0_nonneg
  have hz_nonneg_int : 0 ≤ z := by
    exact_mod_cast hz_nonneg_real
  have hz_mul_bound_real : 8 * (z : ℝ) ≤ 17 := by
    linarith [hrow₂, hx1_nonneg, hx0_eq]
  have hz_mul_bound : (8 : ℤ) * z ≤ 17 := by
    exact_mod_cast hz_mul_bound_real
  have hz_le_two : z ≤ 2 := by
    omega
  exact ⟨z, hz.symm, hz_nonneg_int, hz_le_two⟩

/-- Helper for Example 5.21: every integer-feasible point satisfies the first Gomory mixed
integer cut `5 x₁ + 2 x₂ ≤ 11`. -/
lemma example_5_21_integer_feasible_mem_first_cut
    {x : Fin 2 → ℝ}
    (hx : x ∈ example_5_21_integer_feasible_set) :
    x ∈ example_5_21_first_cut := by
  -- Split on the only possible integral values of `x₁` and bound `x₂` from the relaxation.
  rcases example_5_21_integer_feasible_x0_bounds hx with ⟨z, hz, hz_nonneg, hz_le_two⟩
  rw [mem_example_5_21_integer_feasible_set_iff] at hx
  rcases hx with ⟨hxrel, -, -⟩
  rw [mem_example_5_21_relaxation_iff] at hxrel
  rcases hxrel with ⟨-, -, hrow₁, hrow₂⟩
  rw [mem_example_5_21_first_cut_iff]
  interval_cases z
  · have hx1_le_two : x 1 ≤ 2 := by
      have hx0_zero : x 0 = 0 := by
        simpa using hz
      linarith [hrow₁, hx0_zero]
    have hx0_zero : x 0 = 0 := by
      simpa using hz
    linarith [hx0_zero, hx1_le_two]
  · have hx1_le_three : x 1 ≤ 3 := by
      have hx0_one : x 0 = 1 := by
        simpa using hz
      linarith [hrow₁, hx0_one]
    have hx0_one : x 0 = 1 := by
      simpa using hz
    linarith [hx0_one, hx1_le_three]
  · have hx1_from_second_row : 2 * x 1 ≤ 1 := by
      have hx0_two : x 0 = 2 := by
        simpa using hz
      linarith [hrow₂, hx0_two]
    have hx0_two : x 0 = 2 := by
      simpa using hz
    linarith [hx0_two, hx1_from_second_row]

/-- Helper for Example 5.21: every integer-feasible point satisfies the second Gomory mixed
integer cut `3 x₁ + x₂ ≤ 6`. -/
lemma example_5_21_integer_feasible_mem_second_cut
    {x : Fin 2 → ℝ}
    (hx : x ∈ example_5_21_integer_feasible_set) :
    x ∈ example_5_21_second_cut := by
  -- Split on the integral value of `x₁`; only the case `x₁ = 2` needs the integrality of `x₂`.
  rcases example_5_21_integer_feasible_x0_bounds hx with ⟨z, hz, hz_nonneg, hz_le_two⟩
  rw [mem_example_5_21_integer_feasible_set_iff] at hx
  rcases hx with ⟨hxrel, -, hx1⟩
  rw [mem_example_5_21_relaxation_iff] at hxrel
  rcases hxrel with ⟨-, hx1_nonneg, hrow₁, hrow₂⟩
  rw [mem_example_5_21_second_cut_iff]
  interval_cases z
  · have hx1_le_two : x 1 ≤ 2 := by
      have hx0_zero : x 0 = 0 := by
        simpa using hz
      linarith [hrow₁, hx0_zero]
    have hx0_zero : x 0 = 0 := by
      simpa using hz
    linarith [hx0_zero, hx1_le_two]
  · have hx1_le_three : x 1 ≤ 3 := by
      have hx0_one : x 0 = 1 := by
        simpa using hz
      linarith [hrow₁, hx0_one]
    have hx0_one : x 0 = 1 := by
      simpa using hz
    linarith [hx0_one, hx1_le_three]
  · rcases hx1 with ⟨w, hw⟩
    have hx0_two : x 0 = 2 := by
      simpa using hz
    have hx1_eq : x 1 = (w : ℝ) := by
      simpa using hw.symm
    have hw_nonneg_real : 0 ≤ (w : ℝ) := by
      simpa [hx1_eq] using hx1_nonneg
    have hw_nonneg : 0 ≤ w := by
      exact_mod_cast hw_nonneg_real
    have hw_from_second_row_real : 2 * (w : ℝ) ≤ 1 := by
      linarith [hrow₂, hx0_two, hx1_eq]
    have hw_from_second_row : (2 : ℤ) * w ≤ 1 := by
      exact_mod_cast hw_from_second_row_real
    have hw_zero : w = 0 := by
      omega
    have hx1_zero : x 1 = 0 := by
      simp [hx1_eq, hw_zero]
    linarith [hx0_two, hx1_zero]

/-- Example 5.21 (1). Eliminating the slack variables
`x₃ = 2 + x₁ - x₂` and `x₄ = 17 - 8 x₁ - 2 x₂` from the tableau cut `6 x₃ + 7 x₄ ≥ 21`
yields the inequality `5 x₁ + 2 x₂ ≤ 11` in the original-variable space. -/
theorem example_5_21_first_cut_from_slack_elimination
    (x : Fin 2 → ℝ) :
    21 ≤ 6 * (2 + x 0 - x 1) + 7 * (17 - 8 * x 0 - 2 * x 1) ↔
      5 * x 0 + 2 * x 1 ≤ 11 := by
  -- Clear the slack-substitution arithmetic to expose the original-variable inequality.
  constructor <;> intro h <;> linarith

/-- Example 5.21 (2). The formulation strengthened by the first Gomory mixed integer cut is
contained in the formulation obtained from the Gomory fractional cut `x₂ ≤ 3`. -/
theorem example_5_21_first_strengthened_relaxation_subset_fractional_cut :
    example_5_21_first_strengthened_relaxation ⊆ example_5_21_fractional_cut := by
  intro x hx
  -- Combine the original row `-x₁ + x₂ ≤ 2` with the first mixed cut `5 x₁ + 2 x₂ ≤ 11`.
  rw [mem_example_5_21_first_strengthened_relaxation_iff] at hx
  rcases hx with ⟨hxrel, hxcut⟩
  rw [mem_example_5_21_relaxation_iff] at hxrel
  rcases hxrel with ⟨-, -, hrow₁, -⟩
  rw [mem_example_5_21_first_cut_iff] at hxcut
  rw [mem_example_5_21_fractional_cut_iff]
  linarith

/-- Example 5.21 (3). Eliminating the slack variables
`x₄ = 17 - 8 x₁ - 2 x₂` and `x₅ = 11 - 5 x₁ - 2 x₂` from the tableau cut `x₄ + 2 x₅ ≥ 3`
yields the inequality `3 x₁ + x₂ ≤ 6` in the original-variable space. -/
theorem example_5_21_second_cut_from_slack_elimination
    (x : Fin 2 → ℝ) :
    3 ≤ (17 - 8 * x 0 - 2 * x 1) + 2 * (11 - 5 * x 0 - 2 * x 1) ↔
      3 * x 0 + x 1 ≤ 6 := by
  -- Clear the second slack-substitution arithmetic to expose the next cut in original variables.
  constructor <;> intro h <;> linarith

/-- Example 5.21 (4). The fractional LP optimum `(1.3, 3.3)` is cut off by the first Gomory
mixed integer cut. -/
theorem example_5_21_fractional_solution_not_mem_first_strengthened_relaxation :
    example_5_21_fractional_solution ∉ example_5_21_first_strengthened_relaxation := by
  intro hx
  -- The first mixed cut already excludes the LP optimum `(1.3, 3.3)`.
  rw [mem_example_5_21_first_strengthened_relaxation_iff] at hx
  rcases hx with ⟨-, hxcut⟩
  rw [mem_example_5_21_first_cut_iff] at hxcut
  norm_num [example_5_21_fractional_solution] at hxcut

/-- Example 5.21 (5). The point `(1, 3)` is feasible for the original pure integer program. -/
theorem example_5_21_final_solution_mem_integer_feasible_set :
    example_5_21_final_solution ∈ example_5_21_integer_feasible_set := by
  -- Check the two inequalities and exhibit integer witnesses for both coordinates.
  rw [mem_example_5_21_integer_feasible_set_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_example_5_21_relaxation_iff]
    norm_num [example_5_21_final_solution]
  · exact ⟨1, by simp [example_5_21_final_solution]⟩
  · exact ⟨3, by simp [example_5_21_final_solution]⟩

/-- Example 5.21 (6). The point `(1, 3)` satisfies both Gomory mixed integer cuts. -/
theorem example_5_21_final_solution_mem_second_strengthened_relaxation :
    example_5_21_final_solution ∈ example_5_21_second_strengthened_relaxation := by
  -- Reuse integer feasibility and the validity of both Gomory cuts for integer-feasible points.
  have hfinal_feasible : example_5_21_final_solution ∈ example_5_21_integer_feasible_set :=
    example_5_21_final_solution_mem_integer_feasible_set
  have hfinal_relaxation : example_5_21_final_solution ∈ example_5_21_relaxation := by
    rw [mem_example_5_21_integer_feasible_set_iff] at hfinal_feasible
    exact hfinal_feasible.1
  rw [mem_example_5_21_second_strengthened_relaxation_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_example_5_21_first_strengthened_relaxation_iff]
    refine ⟨?_, ?_⟩
    · exact hfinal_relaxation
    · exact
        example_5_21_integer_feasible_mem_first_cut
          hfinal_feasible
  · exact
      example_5_21_integer_feasible_mem_second_cut
        hfinal_feasible

/-- Example 5.21 (7). The objective value at the final solution `(1, 3)` is `59 / 5 = 11.8`. -/
theorem example_5_21_objective_at_final_solution :
    example_5_21_objective example_5_21_final_solution = (59 : ℝ) / 5 := by
  -- Expand the two-coordinate dot product and evaluate it at `(1, 3)`.
  norm_num [example_5_21_objective, example_5_21_objective_coefficients,
    example_5_21_final_solution, dotProduct, Fin.sum_univ_two]

/-- Example 5.21 (8). The point `(1, 3)` is optimal for the original pure integer program. -/
theorem example_5_21_final_solution_optimal_for_integer_program
    {x : Fin 2 → ℝ}
    (hx : x ∈ example_5_21_integer_feasible_set) :
    example_5_21_objective x ≤ example_5_21_objective example_5_21_final_solution := by
  -- Bound the objective by the two Gomory cuts, then evaluate the resulting linear combination.
  have hfirst : 5 * x 0 + 2 * x 1 ≤ 11 := by
    exact (mem_example_5_21_first_cut_iff).1 (example_5_21_integer_feasible_mem_first_cut hx)
  have hsecond : 3 * x 0 + x 1 ≤ 6 := by
    exact (mem_example_5_21_second_cut_iff).1 (example_5_21_integer_feasible_mem_second_cut hx)
  calc
    example_5_21_objective x
        = (4 / 5 : ℝ) * (5 * x 0 + 2 * x 1) + (1 / 2 : ℝ) * (3 * x 0 + x 1) := by
          rw [example_5_21_objective_eq_cut_combination]
    _ ≤ (4 / 5 : ℝ) * 11 + (1 / 2 : ℝ) * 6 := by
          linarith
    _ = (59 : ℝ) / 5 := by
          norm_num
    _ = example_5_21_objective example_5_21_final_solution := by
          symm
          exact example_5_21_objective_at_final_solution

end Example521
