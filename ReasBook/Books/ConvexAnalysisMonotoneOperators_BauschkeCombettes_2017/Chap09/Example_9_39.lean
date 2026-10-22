/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ENNReal

universe u

variable {ι : Type u} [Fintype ι]

-- Proof sketch: specialize the finite-sum Hölder inequality from `Real.inner_le_Lp_mul_Lq` to
-- `Finset.univ`, with exponents `p.toReal` and `p.conjExponent.toReal`, then rewrite the two
-- right-hand factors using the canonical `WithLp` norm formulas on finite products.
/-- Example 9.39: for finite real families, the sum of the absolute values of the coordinate
products is bounded by the product of the `ℓ^p` norm of `x` and the `ℓ^{p*}` norm of `y`, where
`p* = p.conjExponent`. -/
theorem holder_sum_abs_mul_le_withLpNorm_mul_conjExponent_withLpNorm
    (p : ENNReal) (hp : 1 ≤ p) (x y : ι → ℝ) :
    ∑ i, |x i * y i| ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp p.conjExponent y‖ := by
  have hx₁ : ‖WithLp.toLp 1 x‖ = ∑ i, |x i| := by
    simpa [Real.norm_eq_abs] using PiLp.norm_eq_of_L1 (WithLp.toLp 1 x)
  have hy₁ : ‖WithLp.toLp 1 y‖ = ∑ i, |y i| := by
    simpa [Real.norm_eq_abs] using PiLp.norm_eq_of_L1 (WithLp.toLp 1 y)
  rcases hp.eq_or_lt with rfl | hp'
  · calc
      ∑ i, |x i * y i| = ∑ i, |x i| * |y i| := by simp [abs_mul]
      _ ≤ ∑ i, |x i| * ‖WithLp.toLp ∞ y‖ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        exact mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (WithLp.toLp ∞ y) i)
          (abs_nonneg (x i))
      _ = (∑ i, |x i|) * ‖WithLp.toLp ∞ y‖ := by rw [Finset.sum_mul]
      _ = ‖WithLp.toLp 1 x‖ * ‖WithLp.toLp ∞ y‖ := by rw [← hx₁]
      _ = ‖WithLp.toLp 1 x‖ * ‖WithLp.toLp (ENNReal.conjExponent 1) y‖ := by
        rw [show ENNReal.conjExponent 1 = ∞ by simp [ENNReal.conjExponent]]
  · rcases eq_or_ne p ∞ with rfl | hp_top
    · calc
        ∑ i, |x i * y i| = ∑ i, |x i| * |y i| := by simp [abs_mul]
        _ ≤ ∑ i, ‖WithLp.toLp ∞ x‖ * |y i| := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          exact mul_le_mul_of_nonneg_right
            (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (WithLp.toLp ∞ x) i)
            (abs_nonneg (y i))
        _ = ‖WithLp.toLp ∞ x‖ * ∑ i, |y i| := by rw [Finset.mul_sum]
        _ = ‖WithLp.toLp ∞ x‖ * ‖WithLp.toLp 1 y‖ := by rw [hy₁]
        _ = ‖WithLp.toLp ∞ x‖ * ‖WithLp.toLp (ENNReal.conjExponent ∞) y‖ := by
          rw [show ENNReal.conjExponent ∞ = 1 by simp [ENNReal.conjExponent]]
    · have hp_toReal : 1 < p.toReal := by
        rw [← ENNReal.toReal_one]
        exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp'
      letI : p.HolderConjugate p.conjExponent := ENNReal.HolderConjugate.conjExponent hp'.le
      have hpq : p.toReal.HolderConjugate p.conjExponent.toReal :=
        ENNReal.HolderConjugate.toReal hp_toReal
      have hx :
          ‖WithLp.toLp p x‖ = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal) := by
        simpa [Real.norm_eq_abs] using
          PiLp.norm_eq_sum (lt_trans zero_lt_one hp_toReal) (WithLp.toLp p x)
      have hy :
          ‖WithLp.toLp p.conjExponent y‖ =
            (∑ i, |y i| ^ p.conjExponent.toReal) ^ (1 / p.conjExponent.toReal) := by
        simpa [Real.norm_eq_abs] using
          PiLp.norm_eq_sum hpq.symm.pos (WithLp.toLp p.conjExponent y)
      calc
        ∑ i, |x i * y i| = ∑ i, |x i| * |y i| := by simp [abs_mul]
        _ ≤ (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal) *
              (∑ i, |y i| ^ p.conjExponent.toReal) ^ (1 / p.conjExponent.toReal) := by
          simpa using
            (Real.inner_le_Lp_mul_Lq Finset.univ (fun i ↦ |x i|) (fun i ↦ |y i|) hpq)
        _ = ‖WithLp.toLp p x‖ * ‖WithLp.toLp p.conjExponent y‖ := by rw [hx, hy]
