/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Exercise_12_1_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem nonneg_of_lower_bounds_inv_succ_mul (a x : ℝ)
    (hx : ∀ m : ℕ, -((1 : ℝ) / (m + 1 : ℝ)) * a ≤ x) :
    0 ≤ x := by
  have hlim :
      Filter.Tendsto (fun m : ℕ ↦ -((1 : ℝ) / (m + 1 : ℝ)) * a) Filter.atTop (nhds 0) := by
    simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (-a)
  exact le_of_tendsto' hlim hx

-- Proof sketch: apply `ProbabilityTheory.variance_nonneg` to `X 0 + X 1`, expand the variance of
-- the first `m + 2` coordinates to obtain the finite exchangeable bound from Exercise 12.1.3, and
-- let `m → ∞`. If `cov[X 0, X 1; μ]` were negative, then for large `m` the lower bound
-- `-(1 / (m + 1)) * Var[X 0; μ]` would become stricter than the covariance itself, a
-- contradiction.
/-- Exercise 12.1.4: for a square-integrable exchangeable real sequence, the covariance of its
first two coordinates is nonnegative. -/
theorem covariance_first_two_nonneg_of_isExchangeable {X : ℕ → Ω → ℝ}
    (hX : IsExchangeable X μ) (hX_sq : ∀ n, MemLp (X n) 2 μ) :
    0 ≤ cov[X 0, X 1; μ] := by
  refine nonneg_of_lower_bounds_inv_succ_mul (Var[X 0; μ]) (cov[X 0, X 1; μ]) ?_
  intro m
  simpa [div_eq_mul_inv, show ((m : ℝ) + 2 - 1) = (m + 1 : ℝ) by ring] using
    cov_ge_neg_inv_mul_var_of_exchangeable μ (X ∘ Fin.val)
      (show (0 : Fin (m + 2)) ≠ 1 by simp)
      (hX.comp_embedding Fin.valEmbedding) (fun i ↦ hX_sq i)
