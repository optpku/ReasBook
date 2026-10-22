/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Example_10_45
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_46

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open WithLp (ofLp)

noncomputable section

section

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℝ (Fin m)

/- Example 10.49 is `bridge/view`: the source-facing objects are the explicit piecewise affine
maximum `q` and its log-sum-exp smoothing `q_μ`, while the canonical chapter owners are the
coordinatewise maximum smoothing from Example 10.45 and the affine-precomposition owner
`IsSmoothApproximationNonneg.precompose_linearMap_add` from Theorem 10.46. The faithful public API
therefore keeps the textbook formulas as source-facing evaluation lemmas, while the underlying
definitions reuse those owners directly through the canonical Euclidean matrix action
`Matrix.toEuclideanLin A`. The smoothing statement is recorded via the nonnegative-parameter owner
`IsSmoothApproximationNonneg`, since the error parameter `log m` may be zero when `m = 1`. -/

/-- The piecewise affine maximum
`x ↦ max_i ((A x)_i + b_i)` associated to the matrix `A` and offset vector `b`. -/
def piecewise_affine_max (A : Matrix (Fin m) (Fin n) ℝ) (b : F) : E → ℝ :=
  fun x ↦ coordinatewiseMax (Matrix.toEuclideanLin A x + b).ofLp

/-- Evaluating `piecewise_affine_max A b` at `x` gives the textbook formula
`max_i ((A x)_i + b_i)`. -/
@[simp] theorem piecewise_affine_max_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (b : F) (x : E) :
    piecewise_affine_max A b x =
      coordinatewiseMax (fun i ↦ Matrix.mulVec A (ofLp x) i + ofLp b i) := by
  refine congrArg coordinatewiseMax ?_
  ext i
  simp

/-- The log-sum-exp smoothing of the piecewise affine maximum:
`x ↦ μ log (∑ i, exp (((A x)_i + b_i) / μ)) - μ log m`. -/
def piecewise_affine_max_smoothing
    (A : Matrix (Fin m) (Fin n) ℝ) (b : F) (μ : PosReal) : E → ℝ :=
  fun x ↦ shifted_log_sum_exp_smoothing μ (Matrix.toEuclideanLin A x + b)

/-- Evaluating `piecewise_affine_max_smoothing A b μ` at `x` gives the textbook log-sum-exp
formula from Example 10.49. -/
@[simp] theorem piecewise_affine_max_smoothing_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (b : F) (μ : PosReal) (x : E) :
    piecewise_affine_max_smoothing A b μ x =
      (μ : ℝ) *
          Real.log
            (∑ i : Fin m, Real.exp (((Matrix.mulVec A (ofLp x) i + ofLp b i) / (μ : ℝ)))) -
        (μ : ℝ) * Real.log (m : ℝ) := by
  rw [piecewise_affine_max_smoothing]
  exact shifted_log_sum_exp_smoothing_apply μ (Matrix.toEuclideanLin A x + b)

-- Proof sketch: apply Example 10.45 to the coordinatewise maximum on `ℝ^m`, then use the
-- owner-level affine-precomposition theorem from Theorem 10.46 in its source-facing
-- `x ↦ A x + b` form.
/-- Example 10.49: for a piecewise affine maximum
`q(x) = max_i ((A x)_i + b_i)`, the log-sum-exp function `q_μ` is a `1 / μ`-smooth approximation
with parameters `(‖A‖₂,₂², log m)`. -/
theorem piecewise_affine_max_smoothing_is_smooth_approximation
    (hm : 0 < m) (A : Matrix (Fin m) (Fin n) ℝ) (b : F) (μ : PosReal) :
    IsSmoothApproximationNonneg
      (piecewise_affine_max A b)
      (piecewise_affine_max_smoothing A b μ)
      (‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖₊ ^ (2 : ℕ))
      (log_cardinality_nonneg hm)
      μ := by
  simpa only [piecewise_affine_max, piecewise_affine_max_smoothing, one_mul] using
    IsSmoothApproximationNonneg.precompose_linearMap_add
      (coordinatewise_max_shifted_log_sum_exp_is_smooth_approximation_nonneg hm μ)
      (Matrix.toEuclideanLin A).toContinuousLinearMap b

end
