/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

private theorem ennreal_inv_three_six_mul_two_six :
    ((3 : ℝ≥0∞) / 6)⁻¹ * ((2 : ℝ≥0∞) / 6) = (2 : ℝ≥0∞) / 3 := by
  rw [show ((3 : ℝ≥0∞) / 6) = (((3 : NNReal) / 6 : NNReal) : ℝ≥0∞) by simp]
  rw [show ((2 : ℝ≥0∞) / 6) = (((2 : NNReal) / 6 : NNReal) : ℝ≥0∞) by simp]
  rw [show (((((3 : NNReal) / 6 : NNReal) : ℝ≥0∞))⁻¹) =
      ((((3 : NNReal) / 6 : NNReal)⁻¹ : NNReal) : ℝ≥0∞) by
      simpa using (ENNReal.coe_inv (by norm_num : ((3 : NNReal) / 6 : NNReal) ≠ 0)).symm]
  rw [show ((2 : ℝ≥0∞) / 3) = (((2 : NNReal) / 3 : NNReal) : ℝ≥0∞) by simp]
  exact_mod_cast
    (show (((3 : NNReal) / 6 : NNReal)⁻¹) * ((2 : NNReal) / 6 : NNReal) = (2 : NNReal) / 3 by
      apply NNReal.coe_inj.mp
      norm_num)

-- Proof sketch: rewrite the conditioned event with `ProbabilityTheory.cond_apply`, compute the
-- two relevant uniform probabilities with `ProbabilityTheory.uniformOn_apply_finset`, and finish
-- with the finite-cardinality ratio `((3/6)⁻¹ * (2/6) = 2/3)`.
/-- Example 8.1: For the uniform probability measure on the die faces `{1, \dots, 6}`, the
conditional probability that the outcome is odd, given that it is at most `3`, is `2/3`. -/
theorem die_uniform_conditional_probability_odd_given_le_three :
    (uniformOn (Set.Icc (1 : ℕ) 6))[({1, 3, 5} : Finset ℕ) | ({1, 2, 3} : Finset ℕ)] =
      (2 : ℝ≥0∞) / 3 := by
  simpa [Finset.coe_Icc] using
    (show (uniformOn (((Finset.Icc 1 6 : Finset ℕ) : Set ℕ)))[({1, 3, 5} : Finset ℕ) |
        ({1, 2, 3} : Finset ℕ)] = (2 : ℝ≥0∞) / 3 from by
      rw [cond_apply (show MeasurableSet ((({1, 2, 3} : Finset ℕ) : Set ℕ)) by simp)]
      rw [show ((({1, 2, 3} : Finset ℕ) : Set ℕ) ∩ (({1, 3, 5} : Finset ℕ) : Set ℕ)) =
          (({1, 3} : Finset ℕ) : Set ℕ) by
            ext n
            simp
            omega]
      rw [uniformOn_apply_finset, uniformOn_apply_finset]
      exact ennreal_inv_three_six_mul_two_six)
