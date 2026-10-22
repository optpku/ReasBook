/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

section

variable {X : Type u}

/-- The explicit rate term
`δ_k = 2 (√(ν / (k + 1)) + ν / (k + 1))
  (1 + log (2 + (3 / 2) √(ν (k + 1))))`
from the relative-accuracy estimate for the barrier subgradient method. -/
def barrierSubgradientRelativeAccuracyDelta (ν : ℝ) (k : ℕ) : ℝ :=
  2 * (Real.sqrt (ν / ((k : ℝ) + 1)) + ν / ((k : ℝ) + 1)) *
    (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt (ν * ((k : ℝ) + 1))))

/-- The explicit relative-accuracy rate is positive whenever the barrier parameter `ν` is
positive. -/
theorem barrierSubgradientRelativeAccuracyDelta_pos {ν : ℝ} (hν : 0 < ν) (k : ℕ) :
    0 < barrierSubgradientRelativeAccuracyDelta ν k := by
  have hk_pos : 0 < ((k : ℝ) + 1) := Nat.cast_add_one_pos k
  have hratio_pos : 0 < ν / ((k : ℝ) + 1) := div_pos hν hk_pos
  have hsqrt_ratio_pos : 0 < Real.sqrt (ν / ((k : ℝ) + 1)) := Real.sqrt_pos.2 hratio_pos
  have hfirst_factor_pos :
      0 < Real.sqrt (ν / ((k : ℝ) + 1)) + ν / ((k : ℝ) + 1) :=
    add_pos hsqrt_ratio_pos hratio_pos
  have hsqrt_nonneg : 0 ≤ Real.sqrt (ν * ((k : ℝ) + 1)) := Real.sqrt_nonneg _
  have hlog_arg_ge_two :
      (2 : ℝ) ≤ 2 + (3 / 2 : ℝ) * Real.sqrt (ν * ((k : ℝ) + 1)) := by
    nlinarith
  have hlog_nonneg :
      0 ≤ Real.log (2 + (3 / 2 : ℝ) * Real.sqrt (ν * ((k : ℝ) + 1))) := by
    have hlog_arg_ge_one :
        (1 : ℝ) ≤ 2 + (3 / 2 : ℝ) * Real.sqrt (ν * ((k : ℝ) + 1)) := by
      linarith
    apply Real.log_nonneg
    exact hlog_arg_ge_one
  have hthird_factor_pos :
      0 < 1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt (ν * ((k : ℝ) + 1))) := by
    linarith
  -- The explicit rate is a product of three positive factors.
  unfold barrierSubgradientRelativeAccuracyDelta
  exact mul_pos (mul_pos zero_lt_two hfirst_factor_pos) hthird_factor_pos

/-- The geometric mean of the positive values `ψ(x₀), …, ψ(x_k)`. -/
def positiveIterateGeometricMean
    (ψ : X → {r : ℝ // 0 < r}) (x : ℕ → X) (k : ℕ) : ℝ :=
  Real.rpow
    (Finset.prod (Finset.range (k + 1)) fun i ↦ (ψ (x i) : ℝ))
    (1 / ((k : ℝ) + 1))

/-- Expanding `positiveIterateGeometricMean ψ x k` gives the geometric mean of the first `k + 1`
positive values along the iterate sequence. -/
@[simp] theorem positiveIterateGeometricMean_def
    (ψ : X → {r : ℝ // 0 < r}) (x : ℕ → X) (k : ℕ) :
    positiveIterateGeometricMean ψ x k =
      Real.rpow
        (Finset.prod (Finset.range (k + 1)) fun i ↦ (ψ (x i) : ℝ))
        (1 / ((k : ℝ) + 1)) :=
  rfl

/-- Helper for Theorem 7.16: the product of the first `k + 1` positive iterate values is
strictly positive. -/
lemma positive_iterate_product_pos
    (ψ : X → {r : ℝ // 0 < r}) (x : ℕ → X) (k : ℕ) :
    0 < Finset.prod (Finset.range (k + 1)) (fun i ↦ (ψ (x i) : ℝ)) := by
  -- Every factor in the finite product is positive by construction.
  refine Finset.prod_pos ?_
  intro i hi
  exact (ψ (x i)).property

/-- Helper for Theorem 7.16: the geometric mean is the exponential of the averaged logarithms
of the positive iterate values. -/
theorem positiveIterateGeometricMean_eq_exp_average_log
    (ψ : X → {r : ℝ // 0 < r}) (x : ℕ → X) (k : ℕ) :
    positiveIterateGeometricMean ψ x k =
      Real.exp
        ((Finset.sum (Finset.range (k + 1)) fun i ↦ Real.log (ψ (x i) : ℝ)) /
          ((k : ℝ) + 1)) := by
  have hprod_pos : 0 < Finset.prod (Finset.range (k + 1)) (fun i ↦ (ψ (x i) : ℝ)) :=
    positive_iterate_product_pos ψ x k
  have hprod_ne :
      ∀ i ∈ Finset.range (k + 1), (ψ (x i) : ℝ) ≠ 0 := by
    intro i hi
    exact (ψ (x i)).property.ne'
  -- Rewrite the `rpow` definition through `log` and collapse the logarithm of the product.
  calc
    positiveIterateGeometricMean ψ x k =
        Real.exp
          (Real.log (Finset.prod (Finset.range (k + 1)) fun i ↦ (ψ (x i) : ℝ)) *
            (1 / ((k : ℝ) + 1))) := by
      rw [positiveIterateGeometricMean_def]
      simpa using
        (Real.rpow_def_of_pos hprod_pos (1 / ((k : ℝ) + 1)))
    _ = Real.exp
          ((Finset.sum (Finset.range (k + 1)) fun i ↦ Real.log (ψ (x i) : ℝ)) /
            ((k : ℝ) + 1)) := by
      rw [Real.log_prod hprod_ne, div_eq_mul_inv]
      congr 1
      ring

/-- Exponentiating the logarithmic average estimate yields the geometric-mean lower bound
`[∏_{i=0}^k ψ(x_i)]^(1 / (k + 1)) ≥ ψ⋆ exp(-δ_k)`. -/
theorem positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate
    (ψ : X → {r : ℝ // 0 < r}) (x : ℕ → X)
    (ψStar : {r : ℝ // 0 < r}) {ν : ℝ} (k : ℕ)
    (hlog_rate :
      Real.log (ψStar : ℝ) -
          (Finset.sum (Finset.range (k + 1)) fun i ↦ Real.log (ψ (x i) : ℝ)) /
            ((k : ℝ) + 1) ≤
        barrierSubgradientRelativeAccuracyDelta ν k) :
    positiveIterateGeometricMean ψ x k ≥
      (ψStar : ℝ) * Real.exp (-barrierSubgradientRelativeAccuracyDelta ν k) := by
  have havg_lower :
      Real.log (ψStar : ℝ) - barrierSubgradientRelativeAccuracyDelta ν k ≤
        (Finset.sum (Finset.range (k + 1)) fun i ↦ Real.log (ψ (x i) : ℝ)) /
          ((k : ℝ) + 1) := by
    linarith
  have hexp :
      Real.exp (Real.log (ψStar : ℝ) - barrierSubgradientRelativeAccuracyDelta ν k) ≤
        positiveIterateGeometricMean ψ x k := by
    -- Exponentiating preserves the averaged-log inequality and lands on the geometric mean.
    calc
      Real.exp (Real.log (ψStar : ℝ) - barrierSubgradientRelativeAccuracyDelta ν k) ≤
          Real.exp
            ((Finset.sum (Finset.range (k + 1)) fun i ↦ Real.log (ψ (x i) : ℝ)) /
              ((k : ℝ) + 1)) :=
        Real.exp_le_exp_of_le havg_lower
      _ = positiveIterateGeometricMean ψ x k := by
        rw [positiveIterateGeometricMean_eq_exp_average_log]
  have hleft :
      Real.exp (Real.log (ψStar : ℝ) - barrierSubgradientRelativeAccuracyDelta ν k) =
        (ψStar : ℝ) * Real.exp (-barrierSubgradientRelativeAccuracyDelta ν k) := by
    -- Split the exponential of the sum `log ψ⋆ + (-δ_k)` into the optimal value and the rate.
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log ψStar.property]
  simpa [hleft] using hexp

-- Proof sketch: apply the logarithmic-average bridge to get the `exp (-δ_k)` bound, then use
-- `1 - δ_k ≤ exp (-δ_k)` to derive the linearized estimate.
/-- Theorem 7.16: if the averaged logarithmic loss of the positive iterates relative to the
positive optimum `ψ⋆` is bounded by the explicit Chapter 7 rate `δ_k`, then the geometric mean of
the first `k + 1` iterate values is at least `ψ⋆ exp (-δ_k)` and therefore also at least
`ψ⋆ (1 - δ_k)`. -/
theorem positiveIterateGeometricMean_relative_accuracy_of_log_rate
    (ψ : X → {r : ℝ // 0 < r}) (x : ℕ → X)
    (ψStar : {r : ℝ // 0 < r}) {ν : ℝ} (k : ℕ)
    (hlog_rate :
      Real.log (ψStar : ℝ) -
          (Finset.sum (Finset.range (k + 1)) fun i ↦ Real.log (ψ (x i) : ℝ)) /
            ((k : ℝ) + 1) ≤
        barrierSubgradientRelativeAccuracyDelta ν k) :
    positiveIterateGeometricMean ψ x k ≥
        (ψStar : ℝ) * Real.exp (-barrierSubgradientRelativeAccuracyDelta ν k) ∧
      positiveIterateGeometricMean ψ x k ≥
        (ψStar : ℝ) * (1 - barrierSubgradientRelativeAccuracyDelta ν k) := by
  have hexp_bound :
      positiveIterateGeometricMean ψ x k ≥
        (ψStar : ℝ) * Real.exp (-barrierSubgradientRelativeAccuracyDelta ν k) :=
    positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate ψ x ψStar k hlog_rate
  have hlinear_le :
      (ψStar : ℝ) * (1 - barrierSubgradientRelativeAccuracyDelta ν k) ≤
        (ψStar : ℝ) * Real.exp (-barrierSubgradientRelativeAccuracyDelta ν k) := by
    exact mul_le_mul_of_nonneg_left
      (Real.one_sub_le_exp_neg (barrierSubgradientRelativeAccuracyDelta ν k))
      ψStar.property.le
  constructor
  · exact hexp_bound
  · exact le_trans hlinear_le hexp_bound

end
