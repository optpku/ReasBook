import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_example_7_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_2_theorem_7_7

open SequenceIndependentLifting

section Example78

local notation "weights" => example_7_3_weights
local notation "capacity" => (22 : ℝ)
local notation "cover" => example_7_3_cover_set
local notation "ones" => (fun _ : Fin 7 ↦ (1 : ℝ))
local notation "rhs" => (3 : ℝ)
local notation "knapsack" => zero_one_knapsack_set weights capacity
local notation "profile" => lifting_profile weights capacity cover ones rhs

/-- In Example 7.8, every variable outside the cover `C = {1,2,3,4}` has residual weight `6`. -/
theorem example_7_8_weight_eq_six_of_not_mem_cover
    {j : Fin 7}
    (hj : j ∉ cover) :
    weights j = 6 := by
  fin_cases j <;> simp [example_7_3_cover_set, example_7_3_weights, example_7_3_weights_nat] at hj ⊢

/-- In Example 7.8, every cover weight is nonnegative, so the cover-side hypothesis of
Theorem 7.7 is satisfied. -/
theorem example_7_8_weight_nonneg_of_mem_cover
    {j : Fin 7}
    (hj : j ∈ cover) :
    0 ≤ weights j := by
  fin_cases j <;> simp [example_7_3_cover_set, example_7_3_weights, example_7_3_weights_nat] at hj ⊢

/-- Consequently, every residual weight occurring in the lifting step of Example 7.8 lies in the
interval `[0,22]` required by Theorem 7.7. -/
theorem example_7_8_weight_mem_Icc_of_not_mem_cover
    {j : Fin 7}
    (hj : j ∉ cover) :
    weights j ∈ Set.Icc (0 : ℝ) capacity := by
  rw [example_7_8_weight_eq_six_of_not_mem_cover hj]
  norm_num

/-- The base inequality of Example 7.8 is the cover inequality from Example 7.3, expressed via
the Section 7.2.2 owner `base_coefficients`. -/
theorem example_7_8_base_coefficients_eq :
    base_coefficients cover ones = lifted_cover_inequality_coeff cover 0 := by
  ext j
  by_cases hj : j ∈ cover <;> simp [base_coefficients, lifted_cover_inequality_coeff, hj]

/-- In Example 7.8, the lifted coefficients produced from the Section 7.2.2 lifting profile agree
with the displayed fractional lifted vector from Example 7.3 once the profile takes the value
`1 / 2` at the residual weight `6`. -/
theorem example_7_8_lifted_coefficients_eq
    (hprofile_half : profile 6 = 1 / 2) :
    lifted_coefficients cover ones weights profile = example_7_3_fractional_lifted_vector := by
  have hprofile_inv_two : profile 6 = (2 : ℝ)⁻¹ := by
    simpa using hprofile_half
  ext j
  fin_cases j
  · simp [lifted_coefficients, example_7_3_fractional_lifted_vector, lifted_cover_inequality_coeff,
      example_7_3_cover_set]
  · simp [lifted_coefficients, example_7_3_fractional_lifted_vector, lifted_cover_inequality_coeff,
      example_7_3_cover_set]
  · simp [lifted_coefficients, example_7_3_fractional_lifted_vector, lifted_cover_inequality_coeff,
      example_7_3_cover_set]
  · simp [lifted_coefficients, example_7_3_fractional_lifted_vector, lifted_cover_inequality_coeff,
      example_7_3_cover_set]
  · simpa [lifted_coefficients, example_7_3_fractional_lifted_vector,
      lifted_cover_inequality_coeff, example_7_3_cover_set, example_7_3_weights,
      example_7_3_weights_nat] using hprofile_inv_two
  · simpa [lifted_coefficients, example_7_3_fractional_lifted_vector,
      lifted_cover_inequality_coeff, example_7_3_cover_set, example_7_3_weights,
      example_7_3_weights_nat] using hprofile_inv_two
  · simpa [lifted_coefficients, example_7_3_fractional_lifted_vector,
      lifted_cover_inequality_coeff, example_7_3_cover_set, example_7_3_weights,
      example_7_3_weights_nat] using hprofile_inv_two

/-- Example 7.8 rewritten in the canonical Section 7.2.2 owner language:
the base inequality is supplied as `base_coefficients cover ones ≤ rhs`, and the example data
itself discharges the interval side condition from Theorem 7.7. -/
theorem example_7_8_sequence_independent_lifting_of_base_coefficients
    (hbase : is_valid_inequality knapsack (base_coefficients cover ones) rhs)
    (hf_super : is_superadditive_on_Icc profile capacity)
    (hprofile_half : profile 6 = 1 / 2) :
    is_unique_maximal_lifting_of_base_inequality knapsack cover ones rhs
      example_7_3_fractional_lifted_vector := by
  have hcover_nonneg : ∀ ⦃j : Fin 7⦄, j ∈ cover → 0 ≤ weights j := by
    intro j hj
    exact example_7_8_weight_nonneg_of_mem_cover hj
  have hweights : ∀ ⦃j : Fin 7⦄, j ∉ cover → weights j ∈ Set.Icc (0 : ℝ) capacity := by
    intro j hj
    exact example_7_8_weight_mem_Icc_of_not_mem_cover hj
  simpa [example_7_8_lifted_coefficients_eq hprofile_half] using
    lifting_profile_is_unique_maximal_lifting
      weights capacity cover ones rhs
      hbase hcover_nonneg hweights hf_super

/-- Example 7.8. For the binary knapsack set
`8x_1 + 7x_2 + 6x_3 + 4x_4 + 6x_5 + 6x_6 + 6x_7 ≤ 22`, the cover
`C = {1,2,3,4}` from Example 7.3 has the sequence-independent lifting
`x_1 + x_2 + x_3 + x_4 + (1/2)x_5 + (1/2)x_6 + (1/2)x_7 ≤ 3`. This is the
source-facing specialization of the Section 7.2.2 owner
`is_unique_maximal_lifting_of_base_inequality`. -/
theorem example_7_8_sequence_independent_lifting
    (hbase : is_valid_inequality knapsack (lifted_cover_inequality_coeff cover 0) rhs)
    (hf_super : is_superadditive_on_Icc profile capacity)
    (hprofile_half : profile 6 = 1 / 2) :
    is_unique_maximal_lifting_of_base_inequality knapsack cover ones rhs
      example_7_3_fractional_lifted_vector := by
  have hbase' : is_valid_inequality knapsack (base_coefficients cover ones) rhs := by
    simpa [example_7_8_base_coefficients_eq] using hbase
  exact
    example_7_8_sequence_independent_lifting_of_base_coefficients hbase' hf_super hprofile_half

/-- Consequently, the displayed fractional inequality of Example 7.8 is valid for the binary
knapsack set from Example 7.3. -/
theorem example_7_8_sequence_independent_lifting_valid
    (hbase : is_valid_inequality knapsack (lifted_cover_inequality_coeff cover 0) rhs)
    (hf_super : is_superadditive_on_Icc profile capacity)
    (hprofile_half : profile 6 = 1 / 2) :
    is_valid_inequality knapsack example_7_3_fractional_lifted_vector rhs := by
  exact
    (example_7_8_sequence_independent_lifting hbase hf_super hprofile_half).is_lifting
      |>.is_valid_inequality

end Example78
