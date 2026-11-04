/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1_part2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_last_coordinate_lifting
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_7

open scoped BigOperators Matrix

section Example73

/-- The natural-valued weight vector `(8,7,6,4,6,6,6)` from Example 7.3. -/
def example_7_3_weights_nat : Fin 7 → ℕ :=
  ![8, 7, 6, 4, 6, 6, 6]

/-- The real-valued weight vector `(8,7,6,4,6,6,6)` from Example 7.3, viewed as the coercion
bridge from `example_7_3_weights_nat` to the real-weight owners used later in the chapter. -/
abbrev example_7_3_weights : Fin 7 → ℝ :=
  fun i ↦ (example_7_3_weights_nat i : ℝ)

/-- The cover `C = {1,2,3,4}` from the textbook, represented in Lean with zero-based indices as
`{0,1,2,3}`. -/
def example_7_3_cover_set : Finset (Fin 7) :=
  {0, 1, 2, 3}

/-- The lifted inequality `x₁ + x₂ + x₃ + x₄ + x₅ ≤ 3` obtained from the order `5,6,7`. -/
def example_7_3_lifted_vector_5 : Fin 7 → ℝ :=
  lifted_cover_inequality_coeff
    example_7_3_cover_set
    ![(0 : ℝ), 0, 0, 0, 1, 0, 0]

/-- The lifted inequality `x₁ + x₂ + x₃ + x₄ + x₆ ≤ 3` obtained from the symmetric order
`6,5,7`. -/
def example_7_3_lifted_vector_6 : Fin 7 → ℝ :=
  lifted_cover_inequality_coeff
    example_7_3_cover_set
    ![(0 : ℝ), 0, 0, 0, 0, 1, 0]

/-- The lifted inequality `x₁ + x₂ + x₃ + x₄ + x₇ ≤ 3` obtained from the symmetric order
`7,5,6`. -/
def example_7_3_lifted_vector_7 : Fin 7 → ℝ :=
  lifted_cover_inequality_coeff
    example_7_3_cover_set
    ![(0 : ℝ), 0, 0, 0, 0, 0, 1]

/-- The fractional lifted inequality displayed at the end of Example 7.3. -/
noncomputable def example_7_3_fractional_lifted_vector : Fin 7 → ℝ :=
  lifted_cover_inequality_coeff
    example_7_3_cover_set
    ![(0 : ℝ), 0, 0, 0, (1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ)]

/-- Helper for Example 7.3: every singleton item fits in the capacity-`22` knapsack. -/
lemma example_7_3_weight_le_capacity (j : Fin 7) :
    example_7_3_weights_nat j ≤ 22 := by
  -- The displayed instance has all weights at most the right-hand side `22`.
  fin_cases j <;> norm_num [example_7_3_weights_nat]

/-- Helper for Example 7.3: any binary real vector is the real coercion of a natural-valued
`0/1` vector. -/
lemma example_7_3_binaryCoordsAsNat {n : ℕ} {x : Fin n → ℝ}
    (hbin : ∀ i, x i = 0 ∨ x i = 1) :
    ∃ y : Fin n → ℕ, (∀ i, y i ≤ 1) ∧ x = fun i ↦ (y i : ℝ) := by
  classical
  refine ⟨fun i ↦ if x i = 0 then 0 else 1, ?_, ?_⟩
  · -- The converted coordinates are visibly `0/1`, hence at most `1`.
    intro i
    by_cases hzero : x i = 0
    · simp [hzero]
    · simp [hzero]
  · -- Binary coordinates force the coercion back to the original real vector.
    funext i
    obtain hxi | hxi := hbin i
    · simp [hxi]
    · simp [hxi]

/-- Helper for Example 7.3: the first lifting slice cannot contain three of the first four cover
variables simultaneously. -/
lemma example_7_3_alpha5NatUpper
    (x : Fin 5 → ℕ)
    (hx01 : ∀ i, x i ≤ 1)
    (hxlast : ((x (Fin.last 4) : ℕ) : ℝ) = 1)
    (hweight : ∑ i, (![8, 7, 6, 4, 6] : Fin 5 → ℝ) i * (x i : ℝ) ≤ 22) :
    ∑ i : Fin 4, x i.castSucc ≤ 2 := by
  have hx0 := hx01 0
  have hx1 := hx01 1
  have hx2 := hx01 2
  have hx3 := hx01 3
  have hx4 := hx01 4
  have hxlastNat : x (Fin.last 4) = 1 := by
    exact_mod_cast hxlast
  have hxlastReal : (x (Fin.last 4) : ℝ) = 1 := by
    exact_mod_cast hxlastNat
  have hweightReal := hweight
  norm_num [Fin.sum_univ_succ] at hweightReal
  have h3 : (Fin.succ 2 : Fin 5) = 3 := by decide
  have h4 : ((Fin.succ 2).succ : Fin 5) = 4 := by decide
  rw [h3, h4] at hweightReal
  have hxlastReal' : (x 4 : ℝ) = 1 := by
    simpa using hxlastReal
  -- Normalize the displayed slice to the residual-capacity inequality with `x₅ = 1`.
  have hresidualReal :
      (8 : ℝ) * x 0 + (7 : ℝ) * x 1 + (6 : ℝ) * x 2 + (4 : ℝ) * x 3 ≤ 16 := by
    nlinarith [hweightReal, hxlastReal']
  have hresidual :
      8 * x 0 + 7 * x 1 + 6 * x 2 + 4 * x 3 ≤ 16 := by
    exact_mod_cast hresidualReal
  have hsum : x 0 + x 1 + x 2 + x 3 ≤ 2 := by
    omega
  simpa [Fin.sum_univ_succ, add_assoc] using hsum

/-- Helper for Example 7.3: once `x₆ = 1`, the remaining five binary coordinates have sum at most
`3`. -/
lemma example_7_3_alpha6NatUpper
    (x : Fin 6 → ℕ)
    (hx01 : ∀ i, x i ≤ 1)
    (hxlast : ((x (Fin.last 5) : ℕ) : ℝ) = 1)
    (hweight : ∑ i, (![8, 7, 6, 4, 6, 6] : Fin 6 → ℝ) i * (x i : ℝ) ≤ 22) :
    ∑ i : Fin 5, x i.castSucc ≤ 3 := by
  have hx0 := hx01 0
  have hx1 := hx01 1
  have hx2 := hx01 2
  have hx3 := hx01 3
  have hx4 := hx01 4
  have hx5 := hx01 5
  have hxlastNat : x (Fin.last 5) = 1 := by
    exact_mod_cast hxlast
  have hxlastReal : (x (Fin.last 5) : ℝ) = 1 := by
    exact_mod_cast hxlastNat
  have hweightReal := hweight
  norm_num [Fin.sum_univ_succ] at hweightReal
  have h3 : (Fin.succ 2 : Fin 6) = 3 := by decide
  have h4 : ((Fin.succ 2).succ : Fin 6) = 4 := by decide
  have h5 : ((Fin.succ 2).succ.succ : Fin 6) = 5 := by decide
  rw [h3, h4, h5] at hweightReal
  have hxlastReal' : (x 5 : ℝ) = 1 := by
    simpa using hxlastReal
  -- Fixing `x₆ = 1` leaves capacity `16` for the first five coordinates.
  have hresidualReal :
      (8 : ℝ) * x 0 + (7 : ℝ) * x 1 + (6 : ℝ) * x 2 + (4 : ℝ) * x 3 + (6 : ℝ) * x 4 ≤ 16 := by
    nlinarith [hweightReal, hxlastReal']
  have hresidual :
      8 * x 0 + 7 * x 1 + 6 * x 2 + 4 * x 3 + 6 * x 4 ≤ 16 := by
    exact_mod_cast hresidualReal
  have hsum : x 0 + x 1 + x 2 + x 3 + x 4 ≤ 3 := by
    omega
  simpa [Fin.sum_univ_succ, add_assoc] using hsum

/-- Helper for Example 7.3: once `x₇ = 1`, the first six binary coordinates still have sum at
most `3`. -/
lemma example_7_3_alpha7NatUpper
    (x : Fin 7 → ℕ)
    (hx01 : ∀ i, x i ≤ 1)
    (hxlast : ((x (Fin.last 6) : ℕ) : ℝ) = 1)
    (hweight : ∑ i, (![8, 7, 6, 4, 6, 6, 6] : Fin 7 → ℝ) i * (x i : ℝ) ≤ 22) :
    ∑ i : Fin 6, x i.castSucc ≤ 3 := by
  have hx0 := hx01 0
  have hx1 := hx01 1
  have hx2 := hx01 2
  have hx3 := hx01 3
  have hx4 := hx01 4
  have hx5 := hx01 5
  have hx6 := hx01 6
  have hxlastNat : x (Fin.last 6) = 1 := by
    exact_mod_cast hxlast
  have hxlastReal : (x (Fin.last 6) : ℝ) = 1 := by
    exact_mod_cast hxlastNat
  have hweightReal := hweight
  norm_num [Fin.sum_univ_succ] at hweightReal
  have h3 : (Fin.succ 2 : Fin 7) = 3 := by decide
  have h4 : ((Fin.succ 2).succ : Fin 7) = 4 := by decide
  have h5 : ((Fin.succ 2).succ.succ : Fin 7) = 5 := by decide
  have h6 : ((Fin.succ 2).succ.succ.succ : Fin 7) = 6 := by decide
  rw [h3, h4, h5, h6] at hweightReal
  have hxlastReal' : (x 6 : ℝ) = 1 := by
    simpa using hxlastReal
  -- The last coordinate again consumes weight `6`, so the residual support has size at most `3`.
  have hresidualReal :
      (8 : ℝ) * x 0 + (7 : ℝ) * x 1 + (6 : ℝ) * x 2 + (4 : ℝ) * x 3 +
        (6 : ℝ) * x 4 + (6 : ℝ) * x 5 ≤ 16 := by
    nlinarith [hweightReal, hxlastReal']
  have hresidual :
      8 * x 0 + 7 * x 1 + 6 * x 2 + 4 * x 3 + 6 * x 4 + 6 * x 5 ≤ 16 := by
    exact_mod_cast hresidualReal
  have hsum : x 0 + x 1 + x 2 + x 3 + x 4 + x 5 ≤ 3 := by
    omega
  simpa [Fin.sum_univ_succ, add_assoc] using hsum

/-- Helper for Example 7.3: the `x₅ = 1` slice objective reaches the maximal value `2`. -/
lemma example_7_3_alpha5MaxValue :
    IsGreatest
      (last_coordinate_slice_values
        (zero_one_knapsack_set (![8, 7, 6, 4, 6] : Fin 5 → ℝ) 22)
        (fun _ : Fin 4 ↦ (1 : ℝ))
        1)
      2 := by
  refine ⟨?_, ?_⟩
  · -- The textbook witness `(1,1,0,0,1)` attains the value `2` on the `x₅ = 1` slice.
    refine mem_last_coordinate_slice_values_iff.mpr ?_
    have hlast : (Fin.last 4 : Fin 5) = 4 := by decide
    refine ⟨![1, 1, 0, 0, 1], ?_, ?_, ?_⟩
    · rw [mem_zero_one_knapsack_set_iff]
      constructor
      · intro i
        fin_cases i <;> simp
      · norm_num [Fin.sum_univ_succ]
    · simp [hlast]
    · norm_num [partial_lifting_value_eq_sum, Fin.sum_univ_succ]
  · intro t ht
    rcases mem_last_coordinate_slice_values_iff.mp ht with ⟨x, hxS, hxlast, rfl⟩
    rw [mem_zero_one_knapsack_set_iff] at hxS
    rcases hxS with ⟨hbin, hweight⟩
    rcases example_7_3_binaryCoordsAsNat hbin with ⟨y, hy01, rfl⟩
    have hupperNat :=
      example_7_3_alpha5NatUpper y hy01 (by simpa using hxlast) hweight
    have hupperReal : ∑ i : Fin 4, ((y i.castSucc : ℕ) : ℝ) ≤ 2 := by
      exact_mod_cast hupperNat
    -- After converting to natural `0/1` coordinates, the upper bound is exactly the slice bound.
    simpa [partial_lifting_value_eq_sum]
      using hupperReal

/-- Helper for Example 7.3: the `x₆ = 1` slice objective reaches the maximal value `3`. -/
lemma example_7_3_alpha6MaxValue :
    IsGreatest
      (last_coordinate_slice_values
        (zero_one_knapsack_set (![8, 7, 6, 4, 6, 6] : Fin 6 → ℝ) 22)
        (fun _ : Fin 5 ↦ (1 : ℝ))
        1)
      3 := by
  refine ⟨?_, ?_⟩
  · -- The slice point `(0,0,1,1,1,1)` is feasible and gives partial value `3`.
    refine mem_last_coordinate_slice_values_iff.mpr ?_
    have hlast : (Fin.last 5 : Fin 6) = 5 := by decide
    refine ⟨![0, 0, 1, 1, 1, 1], ?_, ?_, ?_⟩
    · rw [mem_zero_one_knapsack_set_iff]
      constructor
      · intro i
        fin_cases i <;> simp
      · norm_num [Fin.sum_univ_succ]
    · simp [hlast]
    · norm_num [partial_lifting_value_eq_sum, Fin.sum_univ_succ]
  · intro t ht
    rcases mem_last_coordinate_slice_values_iff.mp ht with ⟨x, hxS, hxlast, rfl⟩
    rw [mem_zero_one_knapsack_set_iff] at hxS
    rcases hxS with ⟨hbin, hweight⟩
    rcases example_7_3_binaryCoordsAsNat hbin with ⟨y, hy01, rfl⟩
    have hupperNat :=
      example_7_3_alpha6NatUpper y hy01 (by simpa using hxlast) hweight
    have hupperReal : ∑ i : Fin 5, ((y i.castSucc : ℕ) : ℝ) ≤ 3 := by
      exact_mod_cast hupperNat
    -- The partial lifting value is the sum of the first five binary coordinates.
    simpa [partial_lifting_value_eq_sum]
      using hupperReal

/-- Helper for Example 7.3: the `x₇ = 1` slice objective also reaches the maximal value `3`. -/
lemma example_7_3_alpha7MaxValue :
    IsGreatest
      (last_coordinate_slice_values
        (zero_one_knapsack_set (![8, 7, 6, 4, 6, 6, 6] : Fin 7 → ℝ) 22)
        (fun _ : Fin 6 ↦ (1 : ℝ))
        1)
      3 := by
  refine ⟨?_, ?_⟩
  · -- The witness `(0,0,1,1,1,0,1)` attains the same maximal slice value `3`.
    refine mem_last_coordinate_slice_values_iff.mpr ?_
    have hlast : (Fin.last 6 : Fin 7) = 6 := by decide
    refine ⟨![0, 0, 1, 1, 1, 0, 1], ?_, ?_, ?_⟩
    · rw [mem_zero_one_knapsack_set_iff]
      constructor
      · intro i
        fin_cases i <;> simp
      · norm_num [Fin.sum_univ_succ]
    · simp [hlast]
    · norm_num [partial_lifting_value_eq_sum, Fin.sum_univ_succ]
  · intro t ht
    rcases mem_last_coordinate_slice_values_iff.mp ht with ⟨x, hxS, hxlast, rfl⟩
    rw [mem_zero_one_knapsack_set_iff] at hxS
    rcases hxS with ⟨hbin, hweight⟩
    rcases example_7_3_binaryCoordsAsNat hbin with ⟨y, hy01, rfl⟩
    have hupperNat :=
      example_7_3_alpha7NatUpper y hy01 (by simpa using hxlast) hweight
    have hupperReal : ∑ i : Fin 6, ((y i.castSucc : ℕ) : ℝ) ≤ 3 := by
      exact_mod_cast hupperNat
    -- The last-coordinate slice objective is again the sum over the non-last coordinates.
    simpa [partial_lifting_value_eq_sum]
      using hupperReal

/-- First claim in the running knapsack example: the index set `C = {1,2,3,4}` is a
minimal cover for the displayed `0,1` knapsack instance. -/
theorem example_7_3_cover_is_minimal :
    IsMinimalKnapsackCover example_7_3_weights_nat 22 example_7_3_cover_set := by
  -- Unfold minimality into the overweight cover inequality plus the four erase checks.
  rw [isMinimalKnapsackCover_iff, isKnapsackCover_iff]
  constructor
  · decide
  · intro i hi
    -- Each omitted-cover sum is one of `17`, `18`, `19`, or `21`.
    fin_cases i
    · decide
    · decide
    · decide
    · decide
    · simp [example_7_3_cover_set] at hi
    · simp [example_7_3_cover_set] at hi
    · simp [example_7_3_cover_set] at hi

/-- Second claim in the running knapsack example: the corresponding minimal cover inequality
`x₁ + x₂ + x₃ + x₄ ≤ 3` is facet-defining for the restricted polytope
`P_C = conv(K) ∩ {x_j = 0 for j ∉ C}` attached to the cover `C = {1,2,3,4}`. -/
theorem example_7_3_cover_inequality_facet_defining :
    facet_defining_inequality
      (cover_restricted_polytope example_7_3_weights_nat 22 example_7_3_cover_set)
      (cover_indicator example_7_3_cover_set)
      (cover_inequality_rhs example_7_3_cover_set) := by
  -- Proposition 7.1 upgrades the already verified minimal cover to a restricted facet.
  exact
    (cover_inequality_facet_defining_iff_minimal_cover
      example_7_3_weights_nat
      22
      example_7_3_weight_le_capacity
      example_7_3_cover_set
      example_7_3_cover_is_minimal.toIsKnapsackCover).2
      example_7_3_cover_is_minimal

/-- Third claim in the running knapsack example: for the first lifting step in the order
`5,6,7`, the auxiliary maximization problem over the `x₅ = 1` slice has optimal value
`2`, so Proposition 7.2 gives the last-coordinate lifting coefficient `α₅ = 1`. -/
theorem example_7_3_alpha_5_spec :
    last_coordinate_lifting_coefficient
        (zero_one_knapsack_set (![8, 7, 6, 4, 6] : Fin 5 → ℝ) 22)
        (fun _ : Fin 4 ↦ (1 : ℝ))
        3 =
      1 ∧
      IsGreatest
        (last_coordinate_slice_values
          (zero_one_knapsack_set (![8, 7, 6, 4, 6] : Fin 5 → ℝ) 22)
          (fun _ : Fin 4 ↦ (1 : ℝ))
          1)
        2 := by
  refine ⟨?_, example_7_3_alpha5MaxValue⟩
  -- Rewrite the coefficient formula using the computed slice supremum.
  rw [last_coordinate_lifting_coefficient_eq, example_7_3_alpha5MaxValue.csSup_eq]
  norm_num

/-- Fourth claim in the running knapsack example: for the second lifting step in the order
`5,6,7`, the auxiliary maximization problem over the `x₆ = 1` slice has optimal value
`3`, so Proposition 7.2 gives the last-coordinate lifting coefficient `α₆ = 0`. -/
theorem example_7_3_alpha_6_spec :
    last_coordinate_lifting_coefficient
        (zero_one_knapsack_set (![8, 7, 6, 4, 6, 6] : Fin 6 → ℝ) 22)
        (fun _ : Fin 5 ↦ (1 : ℝ))
        3 =
      0 ∧
      IsGreatest
        (last_coordinate_slice_values
          (zero_one_knapsack_set (![8, 7, 6, 4, 6, 6] : Fin 6 → ℝ) 22)
          (fun _ : Fin 5 ↦ (1 : ℝ))
          1)
        3 := by
  refine ⟨?_, example_7_3_alpha6MaxValue⟩
  -- The slice optimum equals the base right-hand side, so the next coefficient is zero.
  rw [last_coordinate_lifting_coefficient_eq, example_7_3_alpha6MaxValue.csSup_eq]
  norm_num

/-- Fifth claim in the running knapsack example: for the third lifting step in the order
`5,6,7`, the analogous auxiliary maximization problem over the `x₇ = 1` slice again has
optimal value `3`, so Proposition 7.2 gives the last-coordinate lifting coefficient `α₇ = 0`. -/
theorem example_7_3_alpha_7_spec :
    last_coordinate_lifting_coefficient
        (zero_one_knapsack_set (![8, 7, 6, 4, 6, 6, 6] : Fin 7 → ℝ) 22)
        (fun _ : Fin 6 ↦ (1 : ℝ))
        3 =
      0 ∧
      IsGreatest
        (last_coordinate_slice_values
          (zero_one_knapsack_set (![8, 7, 6, 4, 6, 6, 6] : Fin 7 → ℝ) 22)
          (fun _ : Fin 6 ↦ (1 : ℝ))
          1)
        3 := by
  refine ⟨?_, example_7_3_alpha7MaxValue⟩
  -- The third lifting step has the same optimal slice value as the second one.
  rw [last_coordinate_lifting_coefficient_eq, example_7_3_alpha7MaxValue.csSup_eq]
  norm_num

/-- Helper for Example 7.3: the cover right-hand side is `3` because the cover has four elements.
-/
lemma example_7_3_cover_rhs_eq :
    cover_inequality_rhs example_7_3_cover_set = 3 := by
  -- Expand the cardinality formula for the specific cover `{0,1,2,3}`.
  have hcard : example_7_3_cover_set.card = 4 := by
    simp [example_7_3_cover_set]
  rw [cover_inequality_rhs_eq, hcard]
  norm_num

/-- Helper for Example 7.3: the order `5,6,7` lifting has coefficient vector
`(1,1,1,1,1,0,0)`. -/
lemma example_7_3_lifted_vector_5_eq :
    example_7_3_lifted_vector_5 = ![(1 : ℝ), 1, 1, 1, 1, 0, 0] := by
  -- Check the displayed coefficient vector coordinatewise.
  ext j
  fin_cases j <;> simp [example_7_3_lifted_vector_5, example_7_3_cover_set,
    lifted_cover_inequality_coeff]

/-- Helper for Example 7.3: the order `6,5,7` lifting has coefficient vector
`(1,1,1,1,0,1,0)`. -/
lemma example_7_3_lifted_vector_6_eq :
    example_7_3_lifted_vector_6 = ![(1 : ℝ), 1, 1, 1, 0, 1, 0] := by
  -- Check the symmetric lifting vector coordinatewise.
  ext j
  fin_cases j <;> simp [example_7_3_lifted_vector_6, example_7_3_cover_set,
    lifted_cover_inequality_coeff]

/-- Helper for Example 7.3: the order `7,5,6` lifting has coefficient vector
`(1,1,1,1,0,0,1)`. -/
lemma example_7_3_lifted_vector_7_eq :
    example_7_3_lifted_vector_7 = ![(1 : ℝ), 1, 1, 1, 0, 0, 1] := by
  -- Check the last symmetric lifting vector coordinatewise.
  ext j
  fin_cases j <;> simp [example_7_3_lifted_vector_7, example_7_3_cover_set,
    lifted_cover_inequality_coeff]

/-- Helper for Example 7.3: the displayed fractional lifting has coefficient vector
`(1,1,1,1,1/2,1/2,1/2)`. -/
lemma example_7_3_fractional_lifted_vector_eq :
    example_7_3_fractional_lifted_vector =
      ![(1 : ℝ), 1, 1, 1, (1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ)] := by
  -- Expand the off-cover coefficients to the displayed fractional values.
  ext j
  fin_cases j <;> simp [example_7_3_fractional_lifted_vector, example_7_3_cover_set,
    lifted_cover_inequality_coeff]

/-- Helper for Example 7.3: if a coefficient vector is already `1` on the cover, reapplying
`lifted_cover_inequality_coeff` does nothing. -/
lemma example_7_3_lifted_cover_fixed
    {α : Fin 7 → ℝ}
    (hcover : ∀ j ∈ example_7_3_cover_set, α j = 1) :
    lifted_cover_inequality_coeff example_7_3_cover_set α = α := by
  -- Split on cover membership and use the prescribed cover values.
  ext j
  by_cases hj : j ∈ example_7_3_cover_set
  · simp [lifted_cover_inequality_coeff, hj, hcover j hj]
  · simp [lifted_cover_inequality_coeff, hj]

/-- Helper for Example 7.3: every feasible `0/1` point of the knapsack set is automatically a
point of the knapsack polytope. -/
lemma example_7_3_mem_polytope_of_mem_knapsack
    {x : Fin 7 → ℝ}
    (hx : x ∈ zero_one_knapsack_set example_7_3_weights 22) :
    x ∈ zero_one_knapsack_polytope example_7_3_weights 22 := by
  -- The polytope is the convex hull of the feasible set, so every feasible point is a vertex
  -- candidate of that convex hull.
  rw [zero_one_knapsack_polytope_eq_convexHull]
  exact subset_convexHull ℝ _ hx

/-- Helper for Example 7.3: expanding the displayed seven-variable weight inequality once gives a
stable natural-arithmetic normal form for all later validity proofs. -/
lemma example_7_3_weightSum_le_capacity_nat
    (y : Fin 7 → ℕ)
    (hweight : ∑ i, (example_7_3_weights_nat i : ℝ) * (y i : ℝ) ≤ 22) :
    8 * y 0 + 7 * y 1 + 6 * y 2 + 4 * y 3 + 6 * y 4 + 6 * y 5 + 6 * y 6 ≤ 22 := by
  -- Route correction: isolate the expensive `Fin.sum` expansion once so later proofs stay in a
  -- small nat-linear arithmetic world.
  have hweight' := hweight
  norm_num [Fin.sum_univ_succ, example_7_3_weights_nat] at hweight'
  have h3 : (Fin.succ 2 : Fin 7) = 3 := by decide
  have h4 : ((Fin.succ 2).succ : Fin 7) = 4 := by decide
  have h5 : ((Fin.succ 2).succ.succ : Fin 7) = 5 := by decide
  have h6 : ((Fin.succ 2).succ.succ.succ : Fin 7) = 6 := by decide
  rw [h3, h4, h5, h6] at hweight'
  have hweightNat' :
      8 * y 0 + (7 * y 1 + (6 * y 2 + (4 * y 3 + (6 * y 4 + (6 * y 5 + 6 * y 6))))) ≤ 22 := by
    exact_mod_cast hweight'
  omega

/-- Helper for Example 7.3: every feasible binary point can activate at most three variables from
the four-cover-plus-one-tail family. -/
lemma example_7_3_coverPlusTail_le_three_of_feasible
    (y : Fin 7 → ℕ)
    (j : Fin 7)
    (hj : j ∉ example_7_3_cover_set)
    (hy01 : ∀ i, y i ≤ 1)
    (hweight : ∑ i, (example_7_3_weights_nat i : ℝ) * (y i : ℝ) ≤ 22) :
    y 0 + y 1 + y 2 + y 3 + y j ≤ 3 := by
  -- After normalizing the knapsack bound, each off-cover case is a short binary-weight check.
  have hweightNat := example_7_3_weightSum_le_capacity_nat y hweight
  have hy0 := hy01 0
  have hy1 := hy01 1
  have hy2 := hy01 2
  have hy3 := hy01 3
  have hy4 := hy01 4
  have hy5 := hy01 5
  have hy6 := hy01 6
  fin_cases j
  · simp [example_7_3_cover_set] at hj
  · simp [example_7_3_cover_set] at hj
  · simp [example_7_3_cover_set] at hj
  · simp [example_7_3_cover_set] at hj
  · -- Turning on four variables among `x₁,x₂,x₃,x₄,x₅` would already exceed the capacity.
    have hsum : y 0 + y 1 + y 2 + y 3 + y 4 ≤ 3 := by
      omega
    simpa [Fin.sum_univ_succ, add_assoc, add_left_comm, add_comm] using hsum
  · -- The same weight pattern holds for the symmetric tail variable `x₆`.
    have hsum : y 0 + y 1 + y 2 + y 3 + y 5 ≤ 3 := by
      omega
    simpa [Fin.sum_univ_succ, add_assoc, add_left_comm, add_comm] using hsum
  · -- The third tail variable has the same weight `6`, so the same arithmetic closes.
    have hsum : y 0 + y 1 + y 2 + y 3 + y 6 ≤ 3 := by
      omega
    simpa [Fin.sum_univ_succ, add_assoc, add_left_comm, add_comm] using hsum

/-- Helper for Example 7.3: if all three tail variables are `1`, then the cover can contribute at
most one additional `1`. -/
lemma example_7_3_coverSum_le_one_of_allThreeTails
    (y : Fin 7 → ℕ)
    (hy01 : ∀ i, y i ≤ 1)
    (hweight : ∑ i, (example_7_3_weights_nat i : ℝ) * (y i : ℝ) ≤ 22)
    (hy4 : y 4 = 1)
    (hy5 : y 5 = 1)
    (hy6 : y 6 = 1) :
    y 0 + y 1 + y 2 + y 3 ≤ 1 := by
  -- The three active tail variables already use weight `18`, leaving capacity `4` for the cover.
  have hweightNat := example_7_3_weightSum_le_capacity_nat y hweight
  have hy0 := hy01 0
  have hy1 := hy01 1
  have hy2 := hy01 2
  have hy3 := hy01 3
  have hsum : y 0 + y 1 + y 2 + y 3 ≤ 1 := by
    omega
  simpa [Fin.sum_univ_succ, add_assoc, add_left_comm, add_comm] using hsum

/-- Helper for Example 7.3: the lifted inequality `x₁ + x₂ + x₃ + x₄ + x₅ ≤ 3` is valid on the
binary knapsack set. -/
lemma example_7_3_lifted_vector_5_valid :
    is_valid_inequality
      (zero_one_knapsack_set example_7_3_weights 22)
      example_7_3_lifted_vector_5
      3 := by
  rw [is_valid_inequality_iff]
  intro x hx
  rcases (mem_zero_one_knapsack_set_iff example_7_3_weights 22 x).mp hx with ⟨hbin, hweight⟩
  rcases example_7_3_binaryCoordsAsNat hbin with ⟨y, hy01, rfl⟩
  -- Route correction: use the shared off-cover tail lemma instead of re-expanding the same
  -- seven-variable dot product inside each validity proof.
  have hupperNat :=
    example_7_3_coverPlusTail_le_three_of_feasible y 4
      (by simp [example_7_3_cover_set])
      hy01
      hweight
  have hupperReal : (y 0 : ℝ) + y 1 + y 2 + y 3 + y 4 ≤ 3 := by
    exact_mod_cast hupperNat
  have h3 : (Fin.succ 2 : Fin 7) = 3 := by decide
  have h4 : ((Fin.succ 2).succ : Fin 7) = 4 := by decide
  calc
    example_7_3_lifted_vector_5 ⬝ᵥ (fun i ↦ (y i : ℝ))
        = (y 0 : ℝ) + y 1 + y 2 + y 3 + y 4 := by
            rw [example_7_3_lifted_vector_5_eq]
            norm_num [dotProduct, Fin.sum_univ_succ]
            rw [h3, h4]
            ring
    _ ≤ 3 := hupperReal

/-- Helper for Example 7.3: the lifted inequality `x₁ + x₂ + x₃ + x₄ + x₆ ≤ 3` is valid on the
binary knapsack set. -/
lemma example_7_3_lifted_vector_6_valid :
    is_valid_inequality
      (zero_one_knapsack_set example_7_3_weights 22)
      example_7_3_lifted_vector_6
      3 := by
  rw [is_valid_inequality_iff]
  intro x hx
  rcases (mem_zero_one_knapsack_set_iff example_7_3_weights 22 x).mp hx with ⟨hbin, hweight⟩
  rcases example_7_3_binaryCoordsAsNat hbin with ⟨y, hy01, rfl⟩
  -- The symmetric `x₆` inequality is the same off-cover arithmetic with tail index `5`.
  have hupperNat :=
    example_7_3_coverPlusTail_le_three_of_feasible y 5
      (by simp [example_7_3_cover_set])
      hy01
      hweight
  have hupperReal : (y 0 : ℝ) + y 1 + y 2 + y 3 + y 5 ≤ 3 := by
    exact_mod_cast hupperNat
  have h3 : (Fin.succ 2 : Fin 7) = 3 := by decide
  have h5 : ((Fin.succ 2).succ.succ : Fin 7) = 5 := by decide
  calc
    example_7_3_lifted_vector_6 ⬝ᵥ (fun i ↦ (y i : ℝ))
        = (y 0 : ℝ) + y 1 + y 2 + y 3 + y 5 := by
            rw [example_7_3_lifted_vector_6_eq]
            norm_num [dotProduct, Fin.sum_univ_succ]
            rw [h3, h5]
            ring
    _ ≤ 3 := hupperReal

/-- Helper for Example 7.3: the lifted inequality `x₁ + x₂ + x₃ + x₄ + x₇ ≤ 3` is valid on the
binary knapsack set. -/
lemma example_7_3_lifted_vector_7_valid :
    is_valid_inequality
      (zero_one_knapsack_set example_7_3_weights 22)
      example_7_3_lifted_vector_7
      3 := by
  rw [is_valid_inequality_iff]
  intro x hx
  rcases (mem_zero_one_knapsack_set_iff example_7_3_weights 22 x).mp hx with ⟨hbin, hweight⟩
  rcases example_7_3_binaryCoordsAsNat hbin with ⟨y, hy01, rfl⟩
  -- The third integral lifting is the same argument for the final off-cover coordinate.
  have hupperNat :=
    example_7_3_coverPlusTail_le_three_of_feasible y 6
      (by simp [example_7_3_cover_set])
      hy01
      hweight
  have hupperReal : (y 0 : ℝ) + y 1 + y 2 + y 3 + y 6 ≤ 3 := by
    exact_mod_cast hupperNat
  have h3 : (Fin.succ 2 : Fin 7) = 3 := by decide
  have h6 : ((Fin.succ 2).succ.succ.succ : Fin 7) = 6 := by decide
  calc
    example_7_3_lifted_vector_7 ⬝ᵥ (fun i ↦ (y i : ℝ))
        = (y 0 : ℝ) + y 1 + y 2 + y 3 + y 6 := by
            rw [example_7_3_lifted_vector_7_eq]
            norm_num [dotProduct, Fin.sum_univ_succ]
            rw [h3, h6]
            ring
    _ ≤ 3 := hupperReal

/-- Helper for Example 7.3: the fractional lifting
`x₁ + x₂ + x₃ + x₄ + 0.5 x₅ + 0.5 x₆ + 0.5 x₇ ≤ 3` is valid on the binary knapsack set. -/
lemma example_7_3_fractional_lifted_vector_valid :
    is_valid_inequality
      (zero_one_knapsack_set example_7_3_weights 22)
      example_7_3_fractional_lifted_vector
      3 := by
  rw [is_valid_inequality_iff]
  intro x hx
  rcases (mem_zero_one_knapsack_set_iff example_7_3_weights 22 x).mp hx with ⟨hbin, hweight⟩
  rcases example_7_3_binaryCoordsAsNat hbin with ⟨y, hy01, rfl⟩
  have hweightNat := example_7_3_weightSum_le_capacity_nat y hweight
  have hy0 := hy01 0
  have hy1 := hy01 1
  have hy2 := hy01 2
  have hy3 := hy01 3
  have hy4 := hy01 4
  have hy5 := hy01 5
  have hy6 := hy01 6
  have hcover4 :=
    example_7_3_coverPlusTail_le_three_of_feasible y 4
      (by simp [example_7_3_cover_set])
      hy01
      hweight
  have hcover5 :=
    example_7_3_coverPlusTail_le_three_of_feasible y 5
      (by simp [example_7_3_cover_set])
      hy01
      hweight
  have hcover6 :=
    example_7_3_coverPlusTail_le_three_of_feasible y 6
      (by simp [example_7_3_cover_set])
      hy01
      hweight
  have hy4_cases : y 4 = 0 ∨ y 4 = 1 := by omega
  have hy5_cases : y 5 = 0 ∨ y 5 = 1 := by omega
  have hy6_cases : y 6 = 0 ∨ y 6 = 1 := by omega
  -- Route correction: split by the number of active tail variables instead of asking one global
  -- `omega` call to rediscover the residual-capacity argument.
  have hdoubleNat :
      2 * (y 0 + y 1 + y 2 + y 3) + y 4 + y 5 + y 6 ≤ 6 := by
    rcases hy4_cases with h4 | h4 <;> rcases hy5_cases with h5 | h5 <;> rcases hy6_cases with h6 | h6
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · have hcover := example_7_3_coverSum_le_one_of_allThreeTails y hy01 hweight h4 h5 h6
      omega
  have hdoubleReal :
      (2 : ℝ) * ((y 0 : ℝ) + y 1 + y 2 + y 3) + y 4 + y 5 + y 6 ≤ 6 := by
    exact_mod_cast hdoubleNat
  have hupperReal :
      (y 0 : ℝ) + y 1 + y 2 + y 3 +
          (1 / 2 : ℝ) * y 4 + (1 / 2 : ℝ) * y 5 + (1 / 2 : ℝ) * y 6 ≤ 3 := by
    nlinarith
  have h3 : (Fin.succ 2 : Fin 7) = 3 := by decide
  have h4 : ((Fin.succ 2).succ : Fin 7) = 4 := by decide
  have h5 : ((Fin.succ 2).succ.succ : Fin 7) = 5 := by decide
  have h6 : ((Fin.succ 2).succ.succ.succ : Fin 7) = 6 := by decide
  calc
    example_7_3_fractional_lifted_vector ⬝ᵥ (fun i ↦ (y i : ℝ))
        = (y 0 : ℝ) + y 1 + y 2 + y 3 +
            (1 / 2 : ℝ) * y 4 + (1 / 2 : ℝ) * y 5 + (1 / 2 : ℝ) * y 6 := by
            rw [example_7_3_fractional_lifted_vector_eq]
            norm_num [dotProduct, Fin.sum_univ_succ]
            rw [h3, h4, h5, h6]
            ring
    _ ≤ 3 := hupperReal

/-- Helper for Example 7.3: the ambient seven-variable knapsack polytope has affine dimension `7`
because no item is overweight. -/
lemma example_7_3_polytope_finrank_direction_affineSpan :
    Module.finrank ℝ
      (affineSpan ℝ (zero_one_knapsack_polytope example_7_3_weights 22)).direction = 7 := by
  -- All weights are at most the capacity, so the full ambient coordinate space survives.
  simpa [example_7_3_weights, example_7_3_weights_nat, zero_one_knapsack_overweight_indices]
    using
      zero_one_knapsack_polytope_finrank_direction_affineSpan
        example_7_3_weights
        22
        (by
          intro j
          fin_cases j <;> norm_num [example_7_3_weights, example_7_3_weights_nat])
        (by norm_num)

/-- Helper for Example 7.3: the dot product with a coefficient vector viewed as a linear map. -/
private def example_7_3_dotProductLinearMap (c : Fin 7 → ℝ) :
    (Fin 7 → ℝ) →ₗ[ℝ] ℝ :=
  ∑ j, c j • LinearMap.proj j

/-- Helper for Example 7.3: `example_7_3_dotProductLinearMap c` evaluates as `c ⬝ᵥ x`. -/
private lemma example_7_3_dotProductLinearMap_apply
    (c x : Fin 7 → ℝ) :
    example_7_3_dotProductLinearMap c x = c ⬝ᵥ x := by
  -- The linear map is the coordinatewise dot product.
  simp [example_7_3_dotProductLinearMap, dotProduct]

/-- Helper for Example 7.3: a nonzero linear functional on `ℝ^7` has a six-dimensional kernel. -/
private lemma example_7_3_finrankKerEqSix
    {L : (Fin 7 → ℝ) →ₗ[ℝ] ℝ}
    (hL : L ≠ 0) :
    Module.finrank ℝ (LinearMap.ker L) = 6 := by
  let f : Module.Dual ℝ (Fin 7 → ℝ) := L
  have hf : f ≠ 0 := by
    simpa [f] using hL
  have hker_add_one :
      Module.finrank ℝ (LinearMap.ker L) + 1 = Fintype.card (Fin 7) := by
    simpa [f, Module.finrank_fintype_fun_eq_card] using f.finrank_ker_add_one_of_ne_zero hf
  norm_num at hker_add_one
  omega

/-- Helper for Example 7.3: the direction of a nonempty equality face lies in the kernel of the
defining dot-product functional. -/
private lemma example_7_3_face_direction_le_ker
    {P : Set (Fin 7 → ℝ)}
    {c x₀ : Fin 7 → ℝ}
    {δ : ℝ}
    (hx₀ : x₀ ∈ face_set P c δ) :
    (affineSpan ℝ (face_set P c δ)).direction ≤
      LinearMap.ker (example_7_3_dotProductLinearMap c) := by
  let F : Set (Fin 7 → ℝ) := face_set P c δ
  let H : AffineSubspace ℝ (Fin 7 → ℝ) :=
    AffineSubspace.mk' x₀ (LinearMap.ker (example_7_3_dotProductLinearMap c))
  have hx₀_eq : c ⬝ᵥ x₀ = δ := (mem_face_set_iff.mp hx₀).2
  have hF_le_H : F ⊆ H := by
    intro x hx
    -- Equalities at two points differ by a kernel vector.
    change x -ᵥ x₀ ∈ LinearMap.ker (example_7_3_dotProductLinearMap c)
    refine LinearMap.mem_ker.2 ?_
    rcases hx with ⟨_, hx_eq⟩
    rw [mem_linear_hyperplane_iff] at hx_eq
    simp [example_7_3_dotProductLinearMap_apply, vsub_eq_sub, hx_eq, hx₀_eq]
  have h_aff_le : affineSpan ℝ F ≤ H := (affineSpan_le).2 hF_le_H
  -- Passing from affine subspaces to directions identifies the desired kernel containment.
  simpa [F, H] using
    (AffineSubspace.direction_le h_aff_le :
      (affineSpan ℝ F).direction ≤ H.direction)

/-- Helper for Example 7.3: a valid equality face in the seven-variable knapsack polytope is a
facet once it contains seven affinely independent tight points. -/
private lemma example_7_3_face_finrank_eq_six_of_affineIndependentFamily
    {c : Fin 7 → ℝ}
    {p : Fin 7 → Fin 7 → ℝ}
    (hp_range :
      Set.range p ⊆
        face_set
          (zero_one_knapsack_polytope example_7_3_weights 22)
          c
          3)
    (hp_aff : AffineIndependent ℝ p)
    (hL_ne : example_7_3_dotProductLinearMap c ≠ 0) :
    Module.finrank ℝ
      (affineSpan ℝ
        (face_set
          (zero_one_knapsack_polytope example_7_3_weights 22)
          c
          3)).direction = 6 := by
  let F : Set (Fin 7 → ℝ) :=
    face_set
      (zero_one_knapsack_polytope example_7_3_weights 22)
      c
      3
  have hdir_le_ker :
      (affineSpan ℝ F).direction ≤
        LinearMap.ker (example_7_3_dotProductLinearMap c) := by
    -- Every direction vector of the equality face preserves the defining dot product.
    exact example_7_3_face_direction_le_ker (P := zero_one_knapsack_polytope example_7_3_weights 22)
      (c := c) (x₀ := p 0) (δ := 3) (hp_range ⟨0, rfl⟩)
  have hface_finrank_le :
      Module.finrank ℝ (affineSpan ℝ F).direction ≤ 6 := by
    -- The nonzero defining linear functional cuts the ambient space by codimension one.
    have hker_dim :
        Module.finrank ℝ (LinearMap.ker (example_7_3_dotProductLinearMap c)) = 6 :=
      example_7_3_finrankKerEqSix hL_ne
    simpa [hker_dim] using Submodule.finrank_mono hdir_le_ker
  have hp_finrank_le_face :
      Module.finrank ℝ (vectorSpan ℝ (Set.range p)) ≤
        Module.finrank ℝ (affineSpan ℝ F).direction := by
    -- Tight points lie in the face, so their vector span sits inside the face direction.
    rw [direction_affineSpan]
    exact Submodule.finrank_mono (vectorSpan_mono ℝ hp_range)
  have hp_span_plus_one :
      Module.finrank ℝ (vectorSpan ℝ (Set.range p)) + 1 = 7 := by
    simpa using
      (AffineIndependent.finrank_vectorSpan_add_one (k := ℝ) (p := p) hp_aff)
  have hface_plus_one_ge :
      7 ≤ Module.finrank ℝ (affineSpan ℝ F).direction + 1 := by
    calc
      7 = Module.finrank ℝ (vectorSpan ℝ (Set.range p)) + 1 := by
            simpa using hp_span_plus_one.symm
      _ ≤ Module.finrank ℝ (affineSpan ℝ F).direction + 1 := by
            simpa [add_comm] using add_le_add_right hp_finrank_le_face 1
  have hface_dim : Module.finrank ℝ (affineSpan ℝ F).direction = 6 := by
    omega
  simpa [F] using hface_dim

/-- Helper for Example 7.3: a valid equality face in the seven-variable knapsack polytope is a
facet once it contains seven affinely independent tight points. -/
private lemma example_7_3_face_isFacetOf_of_affineIndependentFamily
    {c : Fin 7 → ℝ}
    {p : Fin 7 → Fin 7 → ℝ}
    (hvalid :
      is_valid_inequality
        (zero_one_knapsack_set example_7_3_weights 22)
        c
        3)
    (hp_range :
      Set.range p ⊆
        face_set
          (zero_one_knapsack_polytope example_7_3_weights 22)
          c
          3)
    (hp_aff : AffineIndependent ℝ p)
    (hL_ne : example_7_3_dotProductLinearMap c ≠ 0) :
    IsFacetOf
      (zero_one_knapsack_polytope example_7_3_weights 22)
      (face_set
        (zero_one_knapsack_polytope example_7_3_weights 22)
        c
        3) := by
  let F : Set (Fin 7 → ℝ) :=
    face_set
      (zero_one_knapsack_polytope example_7_3_weights 22)
      c
      3
  have hvalidHull :
      is_valid_inequality
        (zero_one_knapsack_polytope example_7_3_weights 22)
        c
        3 := by
    -- Validity on the binary set extends to validity on its convex hull.
    rw [zero_one_knapsack_polytope_eq_convexHull]
    exact (is_valid_inequality_convexHull_iff).2 hvalid
  have hF_nonempty : F.Nonempty := by
    -- One point from the tight family witnesses nonemptiness of the equality face.
    exact ⟨p 0, hp_range ⟨0, rfl⟩⟩
  have hF_exposed : IsExposed ℝ (zero_one_knapsack_polytope example_7_3_weights 22) F := by
    -- Equality faces of valid inequalities are exposed.
    simpa [F] using isExposed_face_set_of_valid_inequality hvalidHull
  have hF_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction = 6 := by
    -- The tight affine-independent family gives the codimension-one face dimension.
    exact example_7_3_face_finrank_eq_six_of_affineIndependentFamily hp_range hp_aff hL_ne
  rw [isFacetOf_iff]
  refine ⟨hF_nonempty, hF_exposed, ?_⟩
  -- The equality face dimension `6` is exactly one less than the ambient dimension `7`.
  simp [F, hF_dim, example_7_3_polytope_finrank_direction_affineSpan]

/-- Helper for Example 7.3: every omit-one cover point is tight for any coefficient vector that
is `1` on the cover. -/
lemma example_7_3_omitPoint_mem_face_of_coverCoeffs
    {c : Fin 7 → ℝ}
    (hcover : ∀ j ∈ example_7_3_cover_set, c j = 1)
    {j : Fin 7}
    (hj : j ∈ example_7_3_cover_set) :
    omitPoint example_7_3_cover_set j ∈
      face_set
        (zero_one_knapsack_polytope example_7_3_weights 22)
        c
        3 := by
  rw [mem_face_set_iff]
  constructor
  · -- Minimal-cover omit points are feasible binary knapsack points, hence polytope vertices.
    exact
      example_7_3_mem_polytope_of_mem_knapsack
        (omitPoint_mem_zeroOneKnapsackSet
          example_7_3_weights_nat
          22
          example_7_3_cover_set
          example_7_3_cover_is_minimal
          hj)
  · -- The omit-one point keeps exactly the three remaining cover coefficients active.
    rw [omitPoint_dot_eq_sum_erase]
    calc
      (example_7_3_cover_set.erase j).sum c
          = (example_7_3_cover_set.erase j).sum (fun _ ↦ (1 : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hcover i (Finset.mem_of_mem_erase hi)
      _ = cover_inequality_rhs example_7_3_cover_set := by
            simpa [cover_inequality_rhs_eq] using
              (Finset.cast_card_erase_of_mem (R := ℝ) hj)
      _ = 3 := example_7_3_cover_rhs_eq

/-- Helper for Example 7.3: a displayed nonzero coefficient forces the equality-face functional to
be nontrivial. -/
private lemma example_7_3_dotProductLinearMap_ne_zero_of_coeff
    {c : Fin 7 → ℝ}
    {j : Fin 7}
    (hj : c j ≠ 0) :
    example_7_3_dotProductLinearMap c ≠ 0 := by
  -- Evaluate the functional on the `j`th basis vector to detect the nonzero coefficient.
  intro hzero
  have hcoord :=
    congrArg (fun L : (Fin 7 → ℝ) →ₗ[ℝ] ℝ ↦ L (Pi.single j 1)) hzero
  simp [example_7_3_dotProductLinearMap_apply] at hcoord
  exact hj hcoord

/-- Helper for Example 7.3: a feasible binary point with tight left-hand side belongs to the
corresponding equality face of the knapsack polytope. -/
private lemma example_7_3_mem_face_of_tight_knapsack_point
    {c x : Fin 7 → ℝ}
    (hx : x ∈ zero_one_knapsack_set example_7_3_weights 22)
    (htight : c ⬝ᵥ x = 3) :
    x ∈ face_set (zero_one_knapsack_polytope example_7_3_weights 22) c 3 := by
  rw [mem_face_set_iff]
  -- Move the binary witness into the convex hull, then keep the supplied equality.
  exact ⟨example_7_3_mem_polytope_of_mem_knapsack hx, htight⟩

/-- Sixth claim in the running knapsack example: the sequential lifting order `5,6,7`
yields the coefficient vector of the facet-defining lifting
`x₁ + x₂ + x₃ + x₄ + x₅ ≤ 3` of the minimal cover inequality. -/
theorem example_7_3_lifted_inequality_5_facet_defining :
    example_7_3_lifted_vector_5 ∈
      facet_defining_liftings_of_cover_inequality
        example_7_3_weights
        22
        example_7_3_cover_set := by
  let p : Fin 7 → Fin 7 → ℝ :=
    ![omitPoint example_7_3_cover_set 3,
      omitPoint example_7_3_cover_set 0,
      omitPoint example_7_3_cover_set 1,
      omitPoint example_7_3_cover_set 2,
      ![(0 : ℝ), 0, 1, 1, 1, 0, 0],
      ![(0 : ℝ), 0, 1, 1, 1, 1, 0],
      ![(0 : ℝ), 0, 1, 1, 1, 0, 1]]
  have hcover :
      ∀ j ∈ example_7_3_cover_set, example_7_3_lifted_vector_5 j = 1 := by
    intro j hj
    simpa [example_7_3_lifted_vector_5] using
      (lifted_cover_inequality_coeff_of_mem
        (C := example_7_3_cover_set)
        (α := ![(0 : ℝ), 0, 0, 0, 1, 0, 0])
        (j := j)
        hj)
  have hp_range :
      Set.range p ⊆
        face_set
          (zero_one_knapsack_polytope example_7_3_weights 22)
          example_7_3_lifted_vector_5
          3 := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i
    · -- The shared omit-one bridge supplies the common tight cover points.
      exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · -- Route correction: the three non-cover witnesses are checked directly in the full face.
      simpa [p] using
        example_7_3_mem_face_of_tight_knapsack_point
          (c := example_7_3_lifted_vector_5)
          (x := ![(0 : ℝ), 0, 1, 1, 1, 0, 0])
          (by
          rw [mem_zero_one_knapsack_set_iff]
          constructor
          · intro j
            fin_cases j <;> simp
          · norm_num [Fin.sum_univ_succ, example_7_3_weights, example_7_3_weights_nat])
          (by
            rw [example_7_3_lifted_vector_5_eq]
            norm_num [dotProduct, Fin.sum_univ_succ])
    · simpa [p] using
        example_7_3_mem_face_of_tight_knapsack_point
          (c := example_7_3_lifted_vector_5)
          (x := ![(0 : ℝ), 0, 1, 1, 1, 1, 0])
          (by
          rw [mem_zero_one_knapsack_set_iff]
          constructor
          · intro j
            fin_cases j <;> simp
          · norm_num [Fin.sum_univ_succ, example_7_3_weights, example_7_3_weights_nat])
          (by
            rw [example_7_3_lifted_vector_5_eq]
            norm_num [dotProduct, Fin.sum_univ_succ])
    · simpa [p] using
        example_7_3_mem_face_of_tight_knapsack_point
          (c := example_7_3_lifted_vector_5)
          (x := ![(0 : ℝ), 0, 1, 1, 1, 0, 1])
          (by
          rw [mem_zero_one_knapsack_set_iff]
          constructor
          · intro j
            fin_cases j <;> simp
          · norm_num [Fin.sum_univ_succ, example_7_3_weights, example_7_3_weights_nat])
          (by
            rw [example_7_3_lifted_vector_5_eq]
            norm_num [dotProduct, Fin.sum_univ_succ])
  have hp_aff : AffineIndependent ℝ p := by
    rw [affineIndependent_iff_linearIndependent_tail_sub]
    let u0 : Fin 7 → ℝ := ![(-1 : ℝ), 0, 0, 1, 0, 0, 0]
    let u1 : Fin 7 → ℝ := ![(0 : ℝ), -1, 0, 1, 0, 0, 0]
    let u2 : Fin 7 → ℝ := ![(0 : ℝ), 0, -1, 1, 0, 0, 0]
    let u3 : Fin 7 → ℝ := ![(-1 : ℝ), -1, 0, 1, 1, 0, 0]
    let u4 : Fin 7 → ℝ := ![(-1 : ℝ), -1, 0, 1, 1, 1, 0]
    let u5 : Fin 7 → ℝ := ![(-1 : ℝ), -1, 0, 1, 1, 0, 1]
    have htail :
        (fun i : Fin 6 ↦ p i.succ - p 0) = ![u0, u1, u2, u3, u4, u5] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [p, u0, u1, u2, u3, u4, u5, omitPoint, example_7_3_cover_set]
    rw [htail]
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h6coord := congrArg (fun x : Fin 7 → ℝ ↦ x 6) hg
    have h5coord := congrArg (fun x : Fin 7 → ℝ ↦ x 5) hg
    have h4coord := congrArg (fun x : Fin 7 → ℝ ↦ x 4) hg
    have h2coord := congrArg (fun x : Fin 7 → ℝ ↦ x 2) hg
    have h1coord := congrArg (fun x : Fin 7 → ℝ ↦ x 1) hg
    have h0coord := congrArg (fun x : Fin 7 → ℝ ↦ x 0) hg
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h6coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h5coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h4coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h2coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h1coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h0coord
    have h5zero : g 5 = 0 := by simpa using h6coord
    have h4zero : g 4 = 0 := by simpa [h5zero] using h5coord
    have h3zero : g 3 = 0 := by linarith [h4coord, h4zero, h5zero]
    have h2zero : g 2 = 0 := by simpa using h2coord
    have h1zero : g 1 = 0 := by linarith [h1coord, h3zero, h4zero, h5zero]
    have h0zero : g 0 = 0 := by linarith [h0coord, h3zero, h4zero, h5zero]
    fin_cases i
    · exact h0zero
    · exact h1zero
    · exact h2zero
    · exact h3zero
    · exact h4zero
    · exact h5zero
  have hL_ne : example_7_3_dotProductLinearMap example_7_3_lifted_vector_5 ≠ 0 :=
    example_7_3_dotProductLinearMap_ne_zero_of_coeff (j := 0) (by
      rw [example_7_3_lifted_vector_5_eq]
      norm_num)
  -- The existing face-to-facet wrapper closes the lifted-cover owner once the tight family is set up.
  refine (mem_facet_defining_liftings_of_cover_inequality_iff).2 ?_
  simpa [lifted_cover_face, example_7_3_cover_rhs_eq, example_7_3_lifted_cover_fixed hcover] using
    example_7_3_face_isFacetOf_of_affineIndependentFamily
      example_7_3_lifted_vector_5_valid
      hp_range
      hp_aff
      hL_ne

/-- Seventh claim in the running knapsack example: by symmetry, the order `6,5,7`
yields the coefficient vector of the facet-defining lifting
`x₁ + x₂ + x₃ + x₄ + x₆ ≤ 3`. -/
theorem example_7_3_lifted_inequality_6_facet_defining :
    example_7_3_lifted_vector_6 ∈
      facet_defining_liftings_of_cover_inequality
        example_7_3_weights
        22
        example_7_3_cover_set := by
  let p : Fin 7 → Fin 7 → ℝ :=
    ![omitPoint example_7_3_cover_set 3,
      omitPoint example_7_3_cover_set 0,
      omitPoint example_7_3_cover_set 1,
      omitPoint example_7_3_cover_set 2,
      ![(0 : ℝ), 0, 1, 1, 0, 1, 0],
      ![(0 : ℝ), 0, 1, 1, 1, 1, 0],
      ![(0 : ℝ), 0, 1, 1, 0, 1, 1]]
  have hcover :
      ∀ j ∈ example_7_3_cover_set, example_7_3_lifted_vector_6 j = 1 := by
    intro j hj
    simpa [example_7_3_lifted_vector_6] using
      (lifted_cover_inequality_coeff_of_mem
        (C := example_7_3_cover_set)
        (α := ![(0 : ℝ), 0, 0, 0, 0, 1, 0])
        (j := j)
        hj)
  have hp_range :
      Set.range p ⊆
        face_set
          (zero_one_knapsack_polytope example_7_3_weights 22)
          example_7_3_lifted_vector_6
          3 := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · simpa [p] using
        example_7_3_mem_face_of_tight_knapsack_point
          (c := example_7_3_lifted_vector_6)
          (x := ![(0 : ℝ), 0, 1, 1, 0, 1, 0])
          (by
          rw [mem_zero_one_knapsack_set_iff]
          constructor
          · intro j
            fin_cases j <;> simp
          · norm_num [Fin.sum_univ_succ, example_7_3_weights, example_7_3_weights_nat])
          (by
            rw [example_7_3_lifted_vector_6_eq]
            norm_num [dotProduct, Fin.sum_univ_succ])
    · simpa [p] using
        example_7_3_mem_face_of_tight_knapsack_point
          (c := example_7_3_lifted_vector_6)
          (x := ![(0 : ℝ), 0, 1, 1, 1, 1, 0])
          (by
          rw [mem_zero_one_knapsack_set_iff]
          constructor
          · intro j
            fin_cases j <;> simp
          · norm_num [Fin.sum_univ_succ, example_7_3_weights, example_7_3_weights_nat])
          (by
            rw [example_7_3_lifted_vector_6_eq]
            norm_num [dotProduct, Fin.sum_univ_succ])
    · simpa [p] using
        example_7_3_mem_face_of_tight_knapsack_point
          (c := example_7_3_lifted_vector_6)
          (x := ![(0 : ℝ), 0, 1, 1, 0, 1, 1])
          (by
          rw [mem_zero_one_knapsack_set_iff]
          constructor
          · intro j
            fin_cases j <;> simp
          · norm_num [Fin.sum_univ_succ, example_7_3_weights, example_7_3_weights_nat])
          (by
            rw [example_7_3_lifted_vector_6_eq]
            norm_num [dotProduct, Fin.sum_univ_succ])
  have hp_aff : AffineIndependent ℝ p := by
    rw [affineIndependent_iff_linearIndependent_tail_sub]
    let u0 : Fin 7 → ℝ := ![(-1 : ℝ), 0, 0, 1, 0, 0, 0]
    let u1 : Fin 7 → ℝ := ![(0 : ℝ), -1, 0, 1, 0, 0, 0]
    let u2 : Fin 7 → ℝ := ![(0 : ℝ), 0, -1, 1, 0, 0, 0]
    let u3 : Fin 7 → ℝ := ![(-1 : ℝ), -1, 0, 1, 0, 1, 0]
    let u4 : Fin 7 → ℝ := ![(-1 : ℝ), -1, 0, 1, 1, 1, 0]
    let u5 : Fin 7 → ℝ := ![(-1 : ℝ), -1, 0, 1, 0, 1, 1]
    have htail :
        (fun i : Fin 6 ↦ p i.succ - p 0) = ![u0, u1, u2, u3, u4, u5] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [p, u0, u1, u2, u3, u4, u5, omitPoint, example_7_3_cover_set]
    rw [htail]
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h6coord := congrArg (fun x : Fin 7 → ℝ ↦ x 6) hg
    have h4coord := congrArg (fun x : Fin 7 → ℝ ↦ x 4) hg
    have h5coord := congrArg (fun x : Fin 7 → ℝ ↦ x 5) hg
    have h2coord := congrArg (fun x : Fin 7 → ℝ ↦ x 2) hg
    have h1coord := congrArg (fun x : Fin 7 → ℝ ↦ x 1) hg
    have h0coord := congrArg (fun x : Fin 7 → ℝ ↦ x 0) hg
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h6coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h4coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h5coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h2coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h1coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h0coord
    have h5zero : g 5 = 0 := by simpa using h6coord
    have h4zero : g 4 = 0 := by simpa [h5zero] using h4coord
    have h3zero : g 3 = 0 := by linarith [h5coord, h4zero, h5zero]
    have h2zero : g 2 = 0 := by simpa using h2coord
    have h1zero : g 1 = 0 := by linarith [h1coord, h3zero, h4zero, h5zero]
    have h0zero : g 0 = 0 := by linarith [h0coord, h3zero, h4zero, h5zero]
    fin_cases i
    · exact h0zero
    · exact h1zero
    · exact h2zero
    · exact h3zero
    · exact h4zero
    · exact h5zero
  have hL_ne : example_7_3_dotProductLinearMap example_7_3_lifted_vector_6 ≠ 0 :=
    example_7_3_dotProductLinearMap_ne_zero_of_coeff (j := 0) (by
      rw [example_7_3_lifted_vector_6_eq]
      norm_num)
  refine (mem_facet_defining_liftings_of_cover_inequality_iff).2 ?_
  simpa [lifted_cover_face, example_7_3_cover_rhs_eq, example_7_3_lifted_cover_fixed hcover] using
    example_7_3_face_isFacetOf_of_affineIndependentFamily
      example_7_3_lifted_vector_6_valid
      hp_range
      hp_aff
      hL_ne

/-- Eighth claim in the running knapsack example: by symmetry, the order `7,5,6`
yields the coefficient vector of the facet-defining lifting
`x₁ + x₂ + x₃ + x₄ + x₇ ≤ 3`. -/
theorem example_7_3_lifted_inequality_7_facet_defining :
    example_7_3_lifted_vector_7 ∈
      facet_defining_liftings_of_cover_inequality
        example_7_3_weights
        22
        example_7_3_cover_set := by
  let p : Fin 7 → Fin 7 → ℝ :=
    ![omitPoint example_7_3_cover_set 3,
      omitPoint example_7_3_cover_set 0,
      omitPoint example_7_3_cover_set 1,
      omitPoint example_7_3_cover_set 2,
      ![(0 : ℝ), 0, 1, 1, 0, 0, 1],
      ![(0 : ℝ), 0, 1, 1, 1, 0, 1],
      ![(0 : ℝ), 0, 1, 1, 0, 1, 1]]
  have hcover :
      ∀ j ∈ example_7_3_cover_set, example_7_3_lifted_vector_7 j = 1 := by
    intro j hj
    simpa [example_7_3_lifted_vector_7] using
      (lifted_cover_inequality_coeff_of_mem
        (C := example_7_3_cover_set)
        (α := ![(0 : ℝ), 0, 0, 0, 0, 0, 1])
        (j := j)
        hj)
  have hp_range :
      Set.range p ⊆
        face_set
          (zero_one_knapsack_polytope example_7_3_weights 22)
          example_7_3_lifted_vector_7
          3 := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · simpa [p] using
        example_7_3_mem_face_of_tight_knapsack_point
          (c := example_7_3_lifted_vector_7)
          (x := ![(0 : ℝ), 0, 1, 1, 0, 0, 1])
          (by
          rw [mem_zero_one_knapsack_set_iff]
          constructor
          · intro j
            fin_cases j <;> simp
          · norm_num [Fin.sum_univ_succ, example_7_3_weights, example_7_3_weights_nat])
          (by
            rw [example_7_3_lifted_vector_7_eq]
            norm_num [dotProduct, Fin.sum_univ_succ])
    · simpa [p] using
        example_7_3_mem_face_of_tight_knapsack_point
          (c := example_7_3_lifted_vector_7)
          (x := ![(0 : ℝ), 0, 1, 1, 1, 0, 1])
          (by
          rw [mem_zero_one_knapsack_set_iff]
          constructor
          · intro j
            fin_cases j <;> simp
          · norm_num [Fin.sum_univ_succ, example_7_3_weights, example_7_3_weights_nat])
          (by
            rw [example_7_3_lifted_vector_7_eq]
            norm_num [dotProduct, Fin.sum_univ_succ])
    · simpa [p] using
        example_7_3_mem_face_of_tight_knapsack_point
          (c := example_7_3_lifted_vector_7)
          (x := ![(0 : ℝ), 0, 1, 1, 0, 1, 1])
          (by
          rw [mem_zero_one_knapsack_set_iff]
          constructor
          · intro j
            fin_cases j <;> simp
          · norm_num [Fin.sum_univ_succ, example_7_3_weights, example_7_3_weights_nat])
          (by
            rw [example_7_3_lifted_vector_7_eq]
            norm_num [dotProduct, Fin.sum_univ_succ])
  have hp_aff : AffineIndependent ℝ p := by
    rw [affineIndependent_iff_linearIndependent_tail_sub]
    let u0 : Fin 7 → ℝ := ![(-1 : ℝ), 0, 0, 1, 0, 0, 0]
    let u1 : Fin 7 → ℝ := ![(0 : ℝ), -1, 0, 1, 0, 0, 0]
    let u2 : Fin 7 → ℝ := ![(0 : ℝ), 0, -1, 1, 0, 0, 0]
    let u3 : Fin 7 → ℝ := ![(-1 : ℝ), -1, 0, 1, 0, 0, 1]
    let u4 : Fin 7 → ℝ := ![(-1 : ℝ), -1, 0, 1, 1, 0, 1]
    let u5 : Fin 7 → ℝ := ![(-1 : ℝ), -1, 0, 1, 0, 1, 1]
    have htail :
        (fun i : Fin 6 ↦ p i.succ - p 0) = ![u0, u1, u2, u3, u4, u5] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [p, u0, u1, u2, u3, u4, u5, omitPoint, example_7_3_cover_set]
    rw [htail]
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h4coord := congrArg (fun x : Fin 7 → ℝ ↦ x 4) hg
    have h5coord := congrArg (fun x : Fin 7 → ℝ ↦ x 5) hg
    have h6coord := congrArg (fun x : Fin 7 → ℝ ↦ x 6) hg
    have h2coord := congrArg (fun x : Fin 7 → ℝ ↦ x 2) hg
    have h1coord := congrArg (fun x : Fin 7 → ℝ ↦ x 1) hg
    have h0coord := congrArg (fun x : Fin 7 → ℝ ↦ x 0) hg
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h4coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h5coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h6coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h2coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h1coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h0coord
    have h4zero : g 4 = 0 := by simpa using h4coord
    have h5zero : g 5 = 0 := by simpa [h4zero] using h5coord
    have h3zero : g 3 = 0 := by linarith [h6coord, h4zero, h5zero]
    have h2zero : g 2 = 0 := by simpa using h2coord
    have h1zero : g 1 = 0 := by linarith [h1coord, h3zero, h4zero, h5zero]
    have h0zero : g 0 = 0 := by linarith [h0coord, h3zero, h4zero, h5zero]
    fin_cases i
    · exact h0zero
    · exact h1zero
    · exact h2zero
    · exact h3zero
    · exact h4zero
    · exact h5zero
  have hL_ne : example_7_3_dotProductLinearMap example_7_3_lifted_vector_7 ≠ 0 :=
    example_7_3_dotProductLinearMap_ne_zero_of_coeff (j := 0) (by
      rw [example_7_3_lifted_vector_7_eq]
      norm_num)
  refine (mem_facet_defining_liftings_of_cover_inequality_iff).2 ?_
  simpa [lifted_cover_face, example_7_3_cover_rhs_eq, example_7_3_lifted_cover_fixed hcover] using
    example_7_3_face_isFacetOf_of_affineIndependentFamily
      example_7_3_lifted_vector_7_valid
      hp_range
      hp_aff
      hL_ne

/-- Example 7.3: the fractional inequality
`x₁ + x₂ + x₃ + x₄ + 0.5 x₅ + 0.5 x₆ + 0.5 x₇ ≤ 3`
is a facet-defining lifting of the minimal cover inequality attached to
`C = {1,2,3,4}`. -/
theorem example_7_3_fractional_lifted_inequality_facet_defining :
    example_7_3_fractional_lifted_vector ∈
      facet_defining_liftings_of_cover_inequality
        example_7_3_weights
        22
        example_7_3_cover_set := by
  let p : Fin 7 → Fin 7 → ℝ :=
    ![omitPoint example_7_3_cover_set 3,
      omitPoint example_7_3_cover_set 0,
      omitPoint example_7_3_cover_set 1,
      omitPoint example_7_3_cover_set 2,
      ![(0 : ℝ), 0, 1, 1, 1, 1, 0],
      ![(0 : ℝ), 0, 1, 1, 1, 0, 1],
      ![(0 : ℝ), 0, 1, 1, 0, 1, 1]]
  have hcover :
      ∀ j ∈ example_7_3_cover_set, example_7_3_fractional_lifted_vector j = 1 := by
    intro j hj
    simpa [example_7_3_fractional_lifted_vector] using
      (lifted_cover_inequality_coeff_of_mem
        (C := example_7_3_cover_set)
        (α := ![(0 : ℝ), 0, 0, 0, (1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ)])
        (j := j)
        hj)
  have hp_range :
      Set.range p ⊆
        face_set
          (zero_one_knapsack_polytope example_7_3_weights 22)
          example_7_3_fractional_lifted_vector
          3 := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · exact example_7_3_omitPoint_mem_face_of_coverCoeffs hcover (by simp [example_7_3_cover_set])
    · simpa [p] using
        example_7_3_mem_face_of_tight_knapsack_point
          (c := example_7_3_fractional_lifted_vector)
          (x := ![(0 : ℝ), 0, 1, 1, 1, 1, 0])
          (by
          rw [mem_zero_one_knapsack_set_iff]
          constructor
          · intro j
            fin_cases j <;> simp
          · norm_num [Fin.sum_univ_succ, example_7_3_weights, example_7_3_weights_nat])
          (by
            rw [example_7_3_fractional_lifted_vector_eq]
            norm_num [dotProduct, Fin.sum_univ_succ])
    · simpa [p] using
        example_7_3_mem_face_of_tight_knapsack_point
          (c := example_7_3_fractional_lifted_vector)
          (x := ![(0 : ℝ), 0, 1, 1, 1, 0, 1])
          (by
          rw [mem_zero_one_knapsack_set_iff]
          constructor
          · intro j
            fin_cases j <;> simp
          · norm_num [Fin.sum_univ_succ, example_7_3_weights, example_7_3_weights_nat])
          (by
            rw [example_7_3_fractional_lifted_vector_eq]
            norm_num [dotProduct, Fin.sum_univ_succ])
    · simpa [p] using
        example_7_3_mem_face_of_tight_knapsack_point
          (c := example_7_3_fractional_lifted_vector)
          (x := ![(0 : ℝ), 0, 1, 1, 0, 1, 1])
          (by
          rw [mem_zero_one_knapsack_set_iff]
          constructor
          · intro j
            fin_cases j <;> simp
          · norm_num [Fin.sum_univ_succ, example_7_3_weights, example_7_3_weights_nat])
          (by
            rw [example_7_3_fractional_lifted_vector_eq]
            norm_num [dotProduct, Fin.sum_univ_succ])
  have hp_aff : AffineIndependent ℝ p := by
    rw [affineIndependent_iff_linearIndependent_tail_sub]
    let u0 : Fin 7 → ℝ := ![(-1 : ℝ), 0, 0, 1, 0, 0, 0]
    let u1 : Fin 7 → ℝ := ![(0 : ℝ), -1, 0, 1, 0, 0, 0]
    let u2 : Fin 7 → ℝ := ![(0 : ℝ), 0, -1, 1, 0, 0, 0]
    let u3 : Fin 7 → ℝ := ![(-1 : ℝ), -1, 0, 1, 1, 1, 0]
    let u4 : Fin 7 → ℝ := ![(-1 : ℝ), -1, 0, 1, 1, 0, 1]
    let u5 : Fin 7 → ℝ := ![(-1 : ℝ), -1, 0, 1, 0, 1, 1]
    have htail :
        (fun i : Fin 6 ↦ p i.succ - p 0) = ![u0, u1, u2, u3, u4, u5] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [p, u0, u1, u2, u3, u4, u5, omitPoint, example_7_3_cover_set]
    rw [htail]
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h6coord := congrArg (fun x : Fin 7 → ℝ ↦ x 6) hg
    have h5coord := congrArg (fun x : Fin 7 → ℝ ↦ x 5) hg
    have h4coord := congrArg (fun x : Fin 7 → ℝ ↦ x 4) hg
    have h2coord := congrArg (fun x : Fin 7 → ℝ ↦ x 2) hg
    have h1coord := congrArg (fun x : Fin 7 → ℝ ↦ x 1) hg
    have h0coord := congrArg (fun x : Fin 7 → ℝ ↦ x 0) hg
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h6coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h5coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h4coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h2coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h1coord
    simp [Fin.sum_univ_succ, u0, u1, u2, u3, u4, u5] at h0coord
    have h3zero : g 3 = 0 := by linarith [h4coord, h5coord, h6coord]
    have h4zero : g 4 = 0 := by linarith [h4coord, h5coord, h6coord]
    have h5zero : g 5 = 0 := by linarith [h4coord, h5coord, h6coord]
    have h2zero : g 2 = 0 := by simpa using h2coord
    have h1zero : g 1 = 0 := by linarith [h1coord, h3zero, h4zero, h5zero]
    have h0zero : g 0 = 0 := by linarith [h0coord, h3zero, h4zero, h5zero]
    fin_cases i
    · exact h0zero
    · exact h1zero
    · exact h2zero
    · exact h3zero
    · exact h4zero
    · exact h5zero
  have hL_ne : example_7_3_dotProductLinearMap example_7_3_fractional_lifted_vector ≠ 0 :=
    example_7_3_dotProductLinearMap_ne_zero_of_coeff (j := 0) (by
      rw [example_7_3_fractional_lifted_vector_eq]
      norm_num)
  refine (mem_facet_defining_liftings_of_cover_inequality_iff).2 ?_
  simpa [lifted_cover_face, example_7_3_cover_rhs_eq, example_7_3_lifted_cover_fixed hcover] using
    example_7_3_face_isFacetOf_of_affineIndependentFamily
      example_7_3_fractional_lifted_vector_valid
      hp_range
      hp_aff
      hL_ne

/-- Final obstruction for the running knapsack example: the displayed fractional
coefficient vector cannot equal a coefficient vector with integral lifting coefficients
on `x₅`, `x₆`, and `x₇`. In particular, it cannot come from the sequential-lifting
formulas of Proposition 7.2. -/
theorem example_7_3_fractional_lifting_obstruction :
    ¬ ∃ α5 α6 α7 : ℤ,
      example_7_3_fractional_lifted_vector =
        lifted_cover_inequality_coeff
          example_7_3_cover_set
          ![(0 : ℝ), 0, 0, 0, (α5 : ℝ), (α6 : ℝ), (α7 : ℝ)] := by
  rintro ⟨α5, α6, α7, hα⟩
  have hcoord := congrArg (fun v ↦ v 4) hα
  -- Evaluating at the first off-cover coordinate forces an integer to equal `1 / 2`.
  simp [example_7_3_fractional_lifted_vector, example_7_3_cover_set,
    lifted_cover_inequality_coeff] at hcoord
  have hdouble : (1 : ℤ) = 2 * α5 := by
    have hdoubleReal : (1 : ℝ) = 2 * (α5 : ℝ) := by
      nlinarith [hcoord]
    exact_mod_cast hdoubleReal
  omega

end Example73
