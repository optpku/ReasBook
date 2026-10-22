/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.3.12 lies in the one-dimensional interval-integral/Riemann-sum domain.

Sampled owner-style declarations:
* `∫ x in (0 : ℝ)..1, f x`, the canonical interval-integral owner for the exact quantity on
  `[0, 1]`
* `intervalIntegral.sum_integral_adjacent_intervals`, the canonical adjacent-cell decomposition API
* `MonotoneOn.integral_le_sum` and `AntitoneOn.sum_le_integral` from
  `Mathlib/Analysis/SumIntegralComparisons`, the comparison lemmas organized around endpoint
  Riemann sums

Best owner abstraction:
* the exact integral already belongs to the canonical `intervalIntegral` API
* the right-endpoint uniform-grid sample below is source-facing data; there is no upstream chapter
  or mathlib owner declaration for this exact sampled sum

Primitive data:
* `f : ℝ → ℝ`
* `N : ℕ+`

Derived API:
* the exact quantity is reused directly as `∫ x in (0 : ℝ)..1, f x`
* the error estimate is derived later in Proposition 1.3.13, so this file only owns the sampled
  sum itself -/

/-- Definition 1.3.12: The uniform-grid Riemann-sum approximation on `[0, 1]` with right-endpoint
grid points `x_i = i / N` for a positive number `N` of subintervals is
`(1 / N) * ∑_{i=1}^N f(x_i)`. The exact comparison quantity remains the canonical interval
integral `∫ x in (0 : ℝ)..1, f x = ∫_0^1 f(x) dx`. -/
noncomputable def uniformGridRiemannSum (f : ℝ → ℝ) (N : ℕ+) : ℝ :=
  (1 / (N : ℝ)) * ∑ i ∈ Finset.range (N : ℕ), f ((i + 1 : ℝ) / N)

/-- Unfolding formula for the uniform-grid right-endpoint Riemann sum. -/
theorem uniformGridRiemannSum_def (f : ℝ → ℝ) (N : ℕ+) :
    uniformGridRiemannSum f N = (1 / (N : ℝ)) * ∑ i ∈ Finset.range (N : ℕ), f ((i + 1 : ℝ) / N) :=
  rfl
