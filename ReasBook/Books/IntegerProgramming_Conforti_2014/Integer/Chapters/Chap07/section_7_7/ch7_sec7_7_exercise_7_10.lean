/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_2_theorem_7_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_2.ch2_sec2_2_definition_2_4.KnapsackSet
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1_part2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_last_coordinate_lifting
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_exercise_7_8

open scoped BigOperators Matrix
open SequenceIndependentLifting

section Exercise710

/-- The weight vector `(8,5,3,12)` from Exercise 7.10, indexed so that `i : Fin 4` represents the
textbook variable `x_(i+1)`. -/
def exercise_7_10_weights : Fin 4 → ℕ :=
  ![8, 5, 3, 12]

/-- The real-valued weight vector of Exercise 7.10, used by the Chapter 3 and 7.2 real-vector
owners, is the canonical coercion bridge from `exercise_7_10_weights`. -/
abbrev exercise_7_10_weights_real : Fin 4 → ℝ :=
  fun i ↦ (exercise_7_10_weights i : ℝ)

/-- The knapsack capacity in Exercise 7.10. -/
def exercise_7_10_capacity : ℕ :=
  14

/-- The natural `0,1` knapsack set attached to the data of Exercise 7.10. -/
def exercise_7_10_knapsack_set : Set (Fin 4 → ℝ) :=
  zero_one_knapsack_set exercise_7_10_weights_real exercise_7_10_capacity

/-- The minimal cover `C = {1,2,3}` from Exercise 7.10, represented on `Fin 4` by the zero-based
indices `{0,1,2}`. -/
def exercise_7_10_cover : Finset (Fin 4) :=
  {0, 1, 2}

/-- Membership in the concrete cover from Exercise 7.10 means being one of the first three
coordinates. -/
theorem mem_exercise_7_10_cover_iff
    (j : Fin 4) :
    j ∈ exercise_7_10_cover ↔ j.1 < 3 := by
  fin_cases j <;> decide

/-- The cover `C = {1,2,3}` is a minimal knapsack cover for the instance of Exercise 7.10. -/
theorem exercise_7_10_cover_is_minimal :
    IsMinimalKnapsackCover
      exercise_7_10_weights
      exercise_7_10_capacity
      exercise_7_10_cover := by
  -- Unfold minimality into the overweight cover inequality and the three erase checks.
  rw [isMinimalKnapsackCover_iff, isKnapsackCover_iff]
  constructor
  · decide
  · intro i hi
    fin_cases i
    · decide
    · decide
    · decide
    · simp [exercise_7_10_cover] at hi

/-- Canonical typeclass access to the minimal-cover structure on the Exercise 7.10 cover. -/
instance exercise_7_10_isMinimalKnapsackCover :
    IsMinimalKnapsackCover
      exercise_7_10_weights
      exercise_7_10_capacity
      exercise_7_10_cover :=
  exercise_7_10_cover_is_minimal

/-- The base cover-inequality coefficients `(1,1,1)` on `(x₁,x₂,x₃)` are the Chapter 7 owner
`SequenceIndependentLifting.base_coefficients` specialized to `Finset.univ`. -/
theorem exercise_7_10_cover_base_coeff_eq :
    base_coefficients (Finset.univ : Finset (Fin 3)) (fun _ ↦ (1 : ℝ)) =
      ![(1 : ℝ), 1, 1] := by
  ext i
  fin_cases i <;> simp [base_coefficients]

/-- The residual weight vector `(8,5,3)` for the lifting problem obtained from Exercise 7.10
after fixing `x₄ = 1`. -/
def exercise_7_10_x4_lifting_weights : Fin 3 → ℕ :=
  fun i ↦ exercise_7_10_weights ⟨i.1, Nat.lt_trans i.2 (by decide)⟩

/-- The real-valued residual weight vector `(8,5,3)` used by the canonical `0,1` knapsack-set
owner is the coercion bridge from `exercise_7_10_x4_lifting_weights`. -/
abbrev exercise_7_10_x4_lifting_weights_real : Fin 3 → ℝ :=
  fun i ↦ (exercise_7_10_x4_lifting_weights i : ℝ)

/-- The residual lifting weights are exactly `(8,5,3)`. -/
theorem exercise_7_10_x4_lifting_weights_eq :
    exercise_7_10_x4_lifting_weights = ![8, 5, 3] :=
  by
    ext i
    fin_cases i <;> rfl

/-- The residual capacity for the lifting problem after fixing `x₄ = 1`. -/
def exercise_7_10_x4_lifting_capacity : ℕ :=
  exercise_7_10_capacity - exercise_7_10_weights 3

/-- The residual lifting problem obtained by fixing `x₄ = 1` has capacity `2`. -/
theorem exercise_7_10_x4_lifting_capacity_eq :
    exercise_7_10_x4_lifting_capacity = 2 :=
  rfl

/-- The cover inequality attached to `C = {1,2,3}` in Exercise 7.10 has right-hand side `2`. -/
theorem exercise_7_10_cover_rhs_eq :
    cover_inequality_rhs exercise_7_10_cover = 2 := by
  have hcard : exercise_7_10_cover.card = 3 := by decide
  norm_num [cover_inequality_rhs_eq, hcard]

/-- Casting a binary natural assignment for `(x₁,x₂,x₃)` to `ℝ` identifies the residual
feasibility condition after fixing `x₄ = 1` with membership in the canonical `0,1` knapsack set
with weights `(8,5,3)` and capacity `2`. -/
theorem exercise_7_10_x4_lifting_feasible_iff_mem_zero_one_knapsack_set
    (x : Fin 3 → ℕ) :
    ((∀ i, x i = 0 ∨ x i = 1) ∧
        ∑ i, exercise_7_10_x4_lifting_weights i * x i ≤ exercise_7_10_x4_lifting_capacity) ↔
      (fun i ↦ (x i : ℝ)) ∈
        zero_one_knapsack_set
          exercise_7_10_x4_lifting_weights_real
          exercise_7_10_x4_lifting_capacity := by
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · rintro ⟨hbin, hweight⟩
    constructor
    · -- Cast the binary natural coordinates to the canonical real-valued knapsack owner.
      intro i
      rcases hbin i with hxi | hxi
      · left
        exact_mod_cast hxi
      · right
        exact_mod_cast hxi
    · -- The residual weight inequality is the same inequality after coercing `ℕ` to `ℝ`.
      exact_mod_cast hweight
  · rintro ⟨hbin, hweight⟩
    constructor
    · -- Read the binary real coordinates back as binary natural coordinates.
      intro i
      rcases hbin i with hxi | hxi
      · left
        exact_mod_cast hxi
      · right
        exact_mod_cast hxi
    · -- The owner inequality is again just the casted natural inequality.
      exact_mod_cast hweight

/-- Exercise 7.10 (1): Proposition 7.2 applied to the `x₄ = 1` slice of the Exercise 7.10
knapsack set gives the last-coordinate lifting coefficient `α₄ = 2`; equivalently, the slice
objective `x₁ + x₂ + x₃` has greatest value `0` there. -/
theorem exercise_7_10_alpha_4_spec :
    last_coordinate_lifting_coefficient
        exercise_7_10_knapsack_set
        (base_coefficients (Finset.univ : Finset (Fin 3)) fun _ ↦ (1 : ℝ))
        (cover_inequality_rhs exercise_7_10_cover) =
      2 ∧
      IsGreatest
        (last_coordinate_slice_values
          exercise_7_10_knapsack_set
          (base_coefficients (Finset.univ : Finset (Fin 3)) fun _ ↦ (1 : ℝ))
          1)
        0 := by
  have hGreatest :
      IsGreatest
        (last_coordinate_slice_values
          exercise_7_10_knapsack_set
          (base_coefficients (Finset.univ : Finset (Fin 3)) fun _ ↦ (1 : ℝ))
          1)
        0 := by
    refine ⟨?_, ?_⟩
    · -- The slice point `(0,0,0,1)` is feasible and attains value `0`.
      refine mem_last_coordinate_slice_values_iff.mpr ?_
      refine ⟨![0, 0, 0, 1], ?_, ?_, ?_⟩
      · rw [show exercise_7_10_knapsack_set =
            zero_one_knapsack_set exercise_7_10_weights_real exercise_7_10_capacity by rfl]
        rw [mem_zero_one_knapsack_set_iff]
        constructor
        · intro i
          fin_cases i <;> simp
        · norm_num [exercise_7_10_weights_real, exercise_7_10_weights, exercise_7_10_capacity,
            Fin.sum_univ_succ]
      · simp
      · rw [exercise_7_10_cover_base_coeff_eq, partial_lifting_value_eq_sum]
        norm_num [Fin.sum_univ_succ]
    · intro t ht
      rcases mem_last_coordinate_slice_values_iff.mp ht with ⟨x, hxS, hxlast, rfl⟩
      rw [show exercise_7_10_knapsack_set =
            zero_one_knapsack_set exercise_7_10_weights_real exercise_7_10_capacity by rfl] at hxS
      rw [mem_zero_one_knapsack_set_iff] at hxS
      rcases hxS with ⟨hbin, hweight⟩
      have hlast3 : x 3 = 1 := by
        simpa using hxlast
      have hx_nonneg : ∀ j, 0 ≤ x j := by
        intro j
        rcases hbin j with hxj | hxj <;> simp [hxj]
      have hweight_expanded' :
          8 * x 0 + (5 * x 1 + (3 * x 2 + 12 * x 3)) ≤ 14 := by
        simpa [exercise_7_10_weights_real, exercise_7_10_weights, exercise_7_10_capacity,
          Fin.sum_univ_succ] using hweight
      have hweight_expanded :
          8 * x 0 + 5 * x 1 + 3 * x 2 + 12 * x 3 ≤ 14 := by
        linarith
      have hx0 : x 0 = 0 := by
        rcases hbin 0 with hx0 | hx0
        · exact hx0
        · nlinarith [hweight_expanded, hx0, hlast3, hx_nonneg 1, hx_nonneg 2]
      have hx1 : x 1 = 0 := by
        rcases hbin 1 with hx1 | hx1
        · exact hx1
        · nlinarith [hweight_expanded, hx1, hlast3, hx_nonneg 0, hx_nonneg 2]
      have hx2 : x 2 = 0 := by
        rcases hbin 2 with hx2 | hx2
        · exact hx2
        · nlinarith [hweight_expanded, hx2, hlast3, hx_nonneg 0, hx_nonneg 1]
      -- Any feasible point on the `x₄ = 1` slice has zero first three coordinates.
      rw [exercise_7_10_cover_base_coeff_eq, partial_lifting_value_eq_sum]
      norm_num [Fin.sum_univ_succ, hx0, hx1, hx2]
  refine ⟨?_, hGreatest⟩
  -- Proposition 7.2's coefficient formula collapses to `2 - 0`.
  rw [last_coordinate_lifting_coefficient_eq, exercise_7_10_cover_rhs_eq, hGreatest.csSup_eq]
  norm_num

/-- The lifted coefficient vector of Exercise 7.10 is the canonical lifted-cover coefficient owner
for the cover `{1,2,3}` and the complement coefficient `2` on `x₄`. -/
theorem exercise_7_10_lifted_cover_coeff_eq :
    lifted_cover_inequality_coeff
        exercise_7_10_cover
        ![(0 : ℝ), 0, 0, 2] =
      ![(1 : ℝ), 1, 1, 2] := by
  ext i
  fin_cases i <;> rfl

/-- The zero solution on `(x₁,x₂,x₃)` is feasible for the
residual-capacity lifting problem after setting `x₄ = 1`. -/
theorem exercise_7_10_x4_lifting_zero_feasible :
    (0 : Fin 3 → ℝ) ∈
      zero_one_knapsack_set
        exercise_7_10_x4_lifting_weights_real
        exercise_7_10_x4_lifting_capacity := by
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · intro i
    left
    simp
  · simp

/-- The zero solution on `(x₁,x₂,x₃)` has objective value `0`. -/
theorem exercise_7_10_x4_lifting_zero_objective :
    ∑ i, (0 : Fin 3 → ℕ) i = 0 := by
  simp

/-- Every feasible solution of the residual-capacity lifting problem after setting `x₄ = 1` has
objective value at most `0`. -/
theorem exercise_7_10_x4_lifting_objective_nonpositive
    (y : Fin 3 → ℕ)
    (hy : (fun i ↦ (y i : ℝ)) ∈
      zero_one_knapsack_set
        exercise_7_10_x4_lifting_weights_real
        exercise_7_10_x4_lifting_capacity) :
    ∑ i, y i ≤ 0 := by
  rw [mem_zero_one_knapsack_set_iff] at hy
  rcases hy with ⟨hbin, hweight⟩
  have hy0_nonneg : 0 ≤ (y 0 : ℝ) := by exact_mod_cast Nat.zero_le (y 0)
  have hy1_nonneg : 0 ≤ (y 1 : ℝ) := by exact_mod_cast Nat.zero_le (y 1)
  have hy2_nonneg : 0 ≤ (y 2 : ℝ) := by exact_mod_cast Nat.zero_le (y 2)
  have hweight_expanded' :
      8 * (y 0 : ℝ) + (5 * (y 1 : ℝ) + 3 * (y 2 : ℝ)) ≤ 2 := by
    simpa [exercise_7_10_x4_lifting_weights_real, exercise_7_10_x4_lifting_weights_eq,
      exercise_7_10_x4_lifting_capacity_eq, Fin.sum_univ_succ] using hweight
  have hweight_expanded :
      8 * (y 0 : ℝ) + 5 * (y 1 : ℝ) + 3 * (y 2 : ℝ) ≤ 2 := by
    linarith
  have hy0 : y 0 = 0 := by
    rcases hbin 0 with hy0 | hy0
    · exact_mod_cast hy0
    · exfalso
      nlinarith [hweight_expanded, hy0, hy1_nonneg, hy2_nonneg]
  have hy1 : y 1 = 0 := by
    rcases hbin 1 with hy1 | hy1
    · exact_mod_cast hy1
    · exfalso
      nlinarith [hweight_expanded, hy1, hy0_nonneg, hy2_nonneg]
  have hy2 : y 2 = 0 := by
    rcases hbin 2 with hy2 | hy2
    · exact_mod_cast hy2
    · exfalso
      nlinarith [hweight_expanded, hy2, hy0_nonneg, hy1_nonneg]
  -- The residual capacity `2` is below every positive residual weight.
  -- Therefore only the zero point survives.
  simp [hy0, hy1, hy2, Fin.sum_univ_succ]

/-- Exercise 7.10 (2): the lifted cover inequality `x₁ + x₂ + x₃ + 2x₄ ≤ 2`
is not a Chvatal inequality for the natural `0,1` knapsack formulation
of Exercise 7.10. -/
theorem exercise_7_10_lifted_cover_inequality_is_not_chvatal :
    ¬ IsKnapsackChvatalPresentation
        exercise_7_10_weights
        exercise_7_10_capacity
        ![(1 : ℝ), 1, 1, 2]
        2 := by
  intro hchvatal
  rcases (isKnapsackChvatalPresentation_iff
      exercise_7_10_weights
      exercise_7_10_capacity
      ![(1 : ℝ), 1, 1, 2]
      2).mp hchvatal with ⟨u₀, u, v, hu₀, hu, hv, hcoeff_eq, hrhs⟩
  let x : Fin 4 → ℝ := ![0, 1, 1, (1 / 2 : ℝ)]
  have hx_nonneg : ∀ j, 0 ≤ x j := by
    intro j
    fin_cases j <;> norm_num [x]
  have hx_le_one : ∀ j, x j ≤ 1 := by
    intro j
    fin_cases j <;> norm_num [x]
  have hx_weight :
      ∑ j, exercise_7_10_weights_real j * x j ≤ exercise_7_10_capacity := by
    norm_num [x, exercise_7_10_weights_real, exercise_7_10_weights, exercise_7_10_capacity,
      Fin.sum_univ_succ]
  have hcoeff_point :
      ∀ j, ![(1 : ℝ), 1, 1, 2] j = u₀ * (exercise_7_10_weights j : ℝ) + u j - v j := by
    intro j
    exact (congrFun hcoeff_eq j).symm
  have hterm :
      ∀ j,
        (u₀ * (exercise_7_10_weights j : ℝ) + u j - v j) * x j ≤
          u₀ * ((exercise_7_10_weights j : ℝ) * x j) + u j := by
    intro j
    have haj_nonneg : 0 ≤ (exercise_7_10_weights j : ℝ) := by
      exact_mod_cast Nat.zero_le (exercise_7_10_weights j)
    have hax_nonneg :
        0 ≤ (exercise_7_10_weights j : ℝ) * x j :=
      mul_nonneg haj_nonneg (hx_nonneg j)
    nlinarith [hu₀, hu j, hv j, hx_nonneg j, hx_le_one j, hax_nonneg]
  have hagg :
      ![(1 : ℝ), 1, 1, 2] ⬝ᵥ x ≤
        u₀ * (exercise_7_10_capacity : ℝ) + Finset.univ.sum u := by
    calc
      ![(1 : ℝ), 1, 1, 2] ⬝ᵥ x
          = ∑ j, (u₀ * (exercise_7_10_weights j : ℝ) + u j - v j) * x j := by
              simp_rw [dotProduct, hcoeff_point]
      _ ≤ ∑ j, (u₀ * ((exercise_7_10_weights j : ℝ) * x j) + u j) := by
            exact Finset.sum_le_sum fun j _ ↦ hterm j
      _ = ∑ j, u₀ * ((exercise_7_10_weights j : ℝ) * x j) + ∑ j, u j := by
            rw [Finset.sum_add_distrib]
      _ = u₀ * (∑ j, (exercise_7_10_weights j : ℝ) * x j) + Finset.univ.sum u := by
            rw [← Finset.mul_sum]
      _ ≤ u₀ * (exercise_7_10_capacity : ℝ) + Finset.univ.sum u := by
            gcongr
  have hx_dot :
      ![(1 : ℝ), 1, 1, 2] ⬝ᵥ x = 3 := by
    norm_num [x, dotProduct, Fin.sum_univ_succ]
  have hthree_le_real :
      (3 : ℝ) ≤ u₀ * (exercise_7_10_capacity : ℝ) + Finset.univ.sum u := by
    simpa [hx_dot] using hagg
  have hthree_le_floor :
      (3 : ℤ) ≤ Int.floor (u₀ * (exercise_7_10_capacity : ℝ) + Finset.univ.sum u) :=
    Int.le_floor.mpr hthree_le_real
  simp [hrhs] at hthree_le_floor

end Exercise710
