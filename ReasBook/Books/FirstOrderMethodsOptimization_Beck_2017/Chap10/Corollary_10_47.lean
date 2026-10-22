/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_46

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/- Corollary 10.47 is `bridge/view`: the source statement is about closure of smoothability under
nonnegative linear combinations and affine precomposition. The owner abstractions are the Chapter
10 predicates `is_smoothable`, `is_smoothable_nonneg`, and the approximation-level closure lemmas
from Theorem 10.46. This corollary should therefore reuse those owners directly rather than
rebuilding a local nonnegative smoothability predicate. -/

namespace is_smoothable_nonneg

/-- The Chapter 10 smoothability owner is closed under nonnegative weighted sums, with parameters
obtained by the same weighted sum. -/
theorem nonneg_weighted_sum
    {h1 h2 : E → ℝ} {α1 β1 α2 β2 : NNReal}
    (hh1 : is_smoothable_nonneg h1 α1 β1)
    (hh2 : is_smoothable_nonneg h2 α2 β2)
    (gamma1 gamma2 : NNReal) :
    is_smoothable_nonneg
      (fun x ↦ (gamma1 : ℝ) * h1 x + (gamma2 : ℝ) * h2 x)
      (gamma1 * α1 + gamma2 * α2)
      (gamma1 * β1 + gamma2 * β2) := by
  intro μ
  rcases hh1 μ with ⟨h1μ, hh1μ⟩
  rcases hh2 μ with ⟨h2μ, hh2μ⟩
  exact ⟨_, hh1μ.nonneg_weighted_sum hh2μ gamma1 gamma2⟩

/-- Precomposing a nonnegative smoothability witness by a continuous affine map multiplies the
smoothness parameter by `‖φ.contLinear‖²` and preserves the error parameter. -/
theorem precompose_continuousAffineMap
    {h : V → ℝ} {α β : NNReal}
    (hh : is_smoothable_nonneg h α β)
    (φ : E →ᴬ[ℝ] V) :
    is_smoothable_nonneg
      (fun x ↦ h (φ x))
      (α * ‖φ.contLinear‖₊ ^ (2 : ℕ))
      β := by
  intro μ
  rcases hh μ with ⟨hμ, hhμ⟩
  exact ⟨_, hhμ.precompose_continuousAffineMap φ⟩

end is_smoothable_nonneg

-- Proof sketch: first convert both smoothable inputs to `is_smoothable_nonneg`. For each `μ`,
-- choose the corresponding approximation witnesses and combine their convexity, pointwise bounds,
-- and smoothness estimates termwise. This is exactly the smooth-approximation closure mechanism
-- from `IsSmoothApproximationNonneg.nonneg_weighted_sum` lifted from one fixed `μ` to the
-- `∀ μ` smoothability predicate.
/-- Corollary 10.47 (1): part (a). A nonnegative linear combination of two smoothable convex
functions is nonnegatively smoothable, with parameters obtained by the same linear combination. -/
theorem weighted_sum_is_smoothable_nonneg
    {h1 h2 : E → ℝ} {alpha1 beta1 alpha2 beta2 : PosReal}
    (gamma1 gamma2 : NNReal)
    (hh1 : is_smoothable h1 alpha1 beta1)
    (hh2 : is_smoothable h2 alpha2 beta2) :
    is_smoothable_nonneg
      (fun x ↦ (gamma1 : ℝ) * h1 x + (gamma2 : ℝ) * h2 x)
      (gamma1 * PosReal.toNNReal alpha1 + gamma2 * PosReal.toNNReal alpha2)
      (gamma1 * PosReal.toNNReal beta1 + gamma2 * PosReal.toNNReal beta2) := by
  simpa using
    is_smoothable_nonneg.nonneg_weighted_sum
      (is_smoothable_to_nonneg hh1)
      (is_smoothable_to_nonneg hh2)
      gamma1
      gamma2

-- Proof sketch: convert the smoothability of `h` to the nonnegative owner, then for each `μ`
-- precompose the chosen approximation with the continuous affine map
-- `A.toContinuousAffineMap + ContinuousAffineMap.const ℝ E b`; the approximation inequalities are
-- evaluated at `A x + b`, and the smoothness constant picks up the factor `‖A‖^2`. This is the
-- fixed-`μ` closure statement from
-- `IsSmoothApproximationNonneg.precompose_continuousAffineMap` lifted
-- to smoothability.
/-- Corollary 10.47 (2): part (b). If `h` is smoothable, then the affine precomposition
`x ↦ h (A x + b)` is nonnegatively smoothable with parameters `(α ‖A‖^2, β)`. -/
theorem affine_precomposition_is_smoothable_nonneg
    {h : V → ℝ} {alpha beta : PosReal}
    (A : E →L[ℝ] V) (b : V)
    (hh : is_smoothable h alpha beta) :
    is_smoothable_nonneg
      (fun x ↦ h (A x + b))
      (PosReal.toNNReal alpha * ‖A‖₊ ^ (2 : ℕ))
      (PosReal.toNNReal beta) := by
  simpa [ContinuousAffineMap.add_contLinear] using
    is_smoothable_nonneg.precompose_continuousAffineMap
      (is_smoothable_to_nonneg hh)
      (A.toContinuousAffineMap + ContinuousAffineMap.const ℝ E b)

end
