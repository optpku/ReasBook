/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.SparsePairing

@[expose] public section

namespace ConsensusADMM.RefinedEndpoint.Certificate

open Period1024
open scoped RealInnerProductSpace

/-- The first index block is the first image orbit. -/
theorem orbitVertex_eta (i : ℕ) (hi : i < 1024) :
    orbitVertex i = eta (i : Phase) := by
  simp [orbitVertex, gramFamily, Nat.not_le.mpr hi]

/-- The second index block is the scaled multiplier orbit. -/
theorem orbitVertex_multiplier (i : ℕ) :
    orbitVertex (1024 + i) = scaledMultiplier (i : Phase) := by
  have hi : 1024 ≤ 1024 + i := by omega
  simp only [orbitVertex, hi, decide_true, gramFamily, ite_true]
  congr 1
  change ((1024 + i : ℕ) : ZMod 1024) = (i : ZMod 1024)
  rw [Nat.cast_add]
  change (1024 : ZMod 1024) + (i : ZMod 1024) = (i : ZMod 1024)
  rw [show (1024 : ZMod 1024) = 0 by decide +kernel, zero_add]

@[simp] theorem orbitVertex_zero : orbitVertex 0 = eta 0 := by
  simpa using orbitVertex_eta 0 (by decide)

@[simp] theorem orbitVertex_1023 : orbitVertex 1023 = eta (-1) := by
  rw [orbitVertex_eta 1023 (by decide)]
  congr 1

@[simp] theorem orbitVertex_1024 : orbitVertex 1024 = scaledMultiplier 0 := by
  simpa using orbitVertex_multiplier 0

@[simp] theorem orbitVertex_2047 : orbitVertex 2047 = scaledMultiplier (-1) := by
  rw [show 2047 = 1024 + 1023 by decide, orbitVertex_multiplier]
  congr 1

theorem phase_prev_nat (j : ℕ) (hj : 0 < j) :
    ((j - 1 : ℕ) : Phase) = (j : Phase) - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]

theorem upper_scaled : (upperDenominator : ℝ) * ADMM.RefinedEndpoint.upper =
    (upperNumerator : ℝ) := by
  rw [upper_quotient]
  have hq : (upperDenominator : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt upperDenominator_pos)
  field_simp

/-- The first sparse normal is exactly the paper's normal times a positive integer. -/
theorem firstNormal_sparseValue :
    sparseValue firstNormalNumerator = (upperDenominator : ℝ) •
      firstSupportNormal ADMM.RefinedEndpoint.upper eta scaledMultiplier 0 := by
  simp only [firstNormalNumerator, sparseValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, orbitVertex_1023, orbitVertex_zero,
    orbitVertex_1024, orbitVertex_2047, Int.cast_neg, Int.cast_sub, neg_smul,
    sub_smul, firstSupportNormal, imageVertex, displacement, zero_sub,
    smul_sub, smul_add, smul_smul, upper_scaled]
  abel

/-- The same positive normal scaling is used in the second block. -/
theorem secondNormal_sparseValue :
    sparseValue secondNormalNumerator = (upperDenominator : ℝ) •
      secondSupportNormal ADMM.RefinedEndpoint.upper scaledMultiplier 0 := by
  simp only [secondNormalNumerator, sparseValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, orbitVertex_1024, orbitVertex_2047,
    Int.cast_sub, sub_smul, secondSupportNormal, displacement, zero_sub,
    smul_sub, smul_add, smul_smul, upper_scaled]
  abel

/-- Code zero is the first-block support comparison with the origin. -/
theorem firstTarget_zero : sparseValue (firstTarget 0) =
    imageVertex eta scaledMultiplier 0 := by
  simp only [firstTarget, ite_true, sparseValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, orbitVertex_zero, orbitVertex_1024,
    orbitVertex_2047, Int.cast_one, Int.cast_neg, one_smul, neg_one_smul,
    imageVertex, displacement, zero_sub]
  abel

/-- Positive codes give all the nonself first-block comparisons. -/
theorem firstTarget_pos (j : ℕ) (hj : 0 < j) (hN : j < 1024) :
    sparseValue (firstTarget j) =
      imageVertex eta scaledMultiplier 0 - imageVertex eta scaledMultiplier (j : Phase) := by
  simp only [firstTarget, Nat.ne_of_gt hj, ite_false, sparseValue, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, orbitVertex_zero,
    orbitVertex_1024, orbitVertex_2047, orbitVertex_eta j hN, orbitVertex_multiplier,
    phase_prev_nat j hj, Int.cast_one, Int.cast_neg, one_smul, neg_one_smul,
    imageVertex, displacement, zero_sub]
  abel

/-- Code zero is the second-block support comparison with the origin. -/
theorem secondTarget_zero : sparseValue (secondTarget 0) = eta 0 := by
  simp [secondTarget, sparseValue]

/-- Positive codes give all the nonself second-block comparisons. -/
theorem secondTarget_pos (j : ℕ) (hj : 0 < j) (hN : j < 1024) :
    sparseValue (secondTarget j) = eta 0 - eta (j : Phase) := by
  simp [secondTarget, Nat.ne_of_gt hj, sparseValue, orbitVertex_eta j hN,
    sub_eq_add_neg]

theorem residual_sparseValue : sparseValue residualVector = displacement scaledMultiplier 0 := by
  simp [residualVector, sparseValue, displacement, sub_eq_add_neg]

end ConsensusADMM.RefinedEndpoint.Certificate
