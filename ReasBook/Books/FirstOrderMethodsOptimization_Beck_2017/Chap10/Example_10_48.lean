/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Example_10_44
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_46

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/- Example 10.48 is `bridge/view`: the source-facing objects are the affine norm `x ↦ ‖A x + b‖`
and its radial smoothing, while the chapter owner abstractions are the norm smoothing from
Example 10.44 and the source-facing affine-precomposition bridge
`IsSmoothApproximationNonneg.precompose_linearMap_add` from Theorem 10.46. Since the affine
parameter `‖A‖²` can vanish, the faithful main statement uses the chapter's nonnegative-parameter
owner `IsSmoothApproximationNonneg`; the explicit `x ↦ A x + b` presentation is then derived from
that owner bridge rather than rebuilt through a local continuous-affine proof. -/

/-- The affine norm `x ↦ ‖A x + b‖`, with values in `ℝ`. On Euclidean spaces this is the
textbook affine norm model. -/
def affine_norm (A : E →L[ℝ] F) (b : F) : E → ℝ :=
  fun x ↦ ‖A x + b‖

/-- The radial smoothing of the affine norm with parameter `μ`:
`x ↦ √(‖A x + b‖² + μ²) - μ`. -/
def affine_norm_smooth_approximation (A : E →L[ℝ] F) (b : F) (μ : PosReal) :
    E → ℝ :=
  fun x ↦ norm_smooth_approximation μ (A x + b)

/-- Evaluating `affine_norm_smooth_approximation A b μ` at `x` gives the textbook
formula `√(‖A x + b‖² + μ²) - μ`. -/
@[simp] theorem affine_norm_smooth_approximation_apply
    (A : E →L[ℝ] F) (b : F) (μ : PosReal) (x : E) :
    affine_norm_smooth_approximation A b μ x =
      Real.sqrt (‖A x + b‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) - μ := by
  simp [affine_norm_smooth_approximation]

end

section

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [ProperSpace F]

-- Proof sketch: convert the canonical norm smoothing witness from Example 10.44 to the
-- nonnegative-parameter owner and then apply the source-facing affine-precomposition bridge
-- `IsSmoothApproximationNonneg.precompose_linearMap_add` from Theorem 10.46.
/-- Example 10.48: for a continuous linear map into a proper real inner-product space, hence in
particular for matrices between finite-dimensional Euclidean spaces, the function
`x ↦ √(‖A x + b‖² + μ²) - μ` is a
`1 / μ`-smooth approximation of `x ↦ ‖A x + b‖` with parameters `(‖A‖², 1)`. -/
theorem affine_norm_smooth_approximation_is_smooth_approximation
    (A : E →L[ℝ] F) (b : F) (μ : PosReal) :
    IsSmoothApproximationNonneg
      (affine_norm A b)
      (affine_norm_smooth_approximation A b μ)
      (‖A‖₊ ^ (2 : ℕ))
      1
      μ := by
  have h1 : PosReal.toNNReal (1 : PosReal) = (1 : NNReal) := by
    ext
    rfl
  simpa only [affine_norm, affine_norm_smooth_approximation, h1, one_mul] using
    (norm_smooth_approximation_is_smooth_approximation μ).toNonneg.precompose_linearMap_add A b

end
