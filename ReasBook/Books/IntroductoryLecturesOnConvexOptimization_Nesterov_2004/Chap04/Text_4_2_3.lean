/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open InnerProductSpace
open scoped Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.3 lies in the real-Hilbert-space Hessian domain.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the chapter owner for the intrinsic Hessian operator
* `fderiv_gradient_isSymmetric_of_contDiffAt` in `Chap01/Theorem_1_4_19`, the chapter symmetry
  bridge for `C²` Hessians
* `InnerProductSpace.toDualMap`, the canonical forward Riesz map into the strong dual
* `LinearMap.IsSymmetric.isSelfAdjoint`, the canonical bridge from symmetry to self-adjointness

Owner abstraction:
* core/canonical: `hessian f x`
* bridge/view: `toDualMap ∘ hessian f x`

Primitive data:
* `f`
* `x`
* differentiability of `∇ f` at `x`
* `ContDiffAt ℝ 2 f x`

Derived API:
* the dual-valued Hessian view `toDualMap ∘ hessian f x`
* its pointwise pairing formula
* its derivative formula for the dual-valued gradient map
* self-adjointness of `hessian f x`

This file therefore reuses the chapter owner `hessian f x` directly. The dual-valued formulation
appearing in the text is kept only as a thin bridge via the forward Riesz map `toDualMap`
(equivalently the forward direction of `toDual`), rather than as a second public Hessian owner. -/

/-- Applying the dual-valued Hessian bridge `toDualMap ∘ hessian f x` to a direction `u` and then
to a test vector `v` gives the Hessian pairing at `x`. -/
@[simp] theorem hessian_toDualMap_apply (f : E → ℝ) (x u v : E) :
    (((toDualMap ℝ E).toContinuousLinearMap.comp (hessian f x)) u) v =
      inner ℝ (hessian f x u) v := by
  simp

/-- Text 4.2.3: if `f` is twice differentiable at `x`, then the Hessian at `x` is the continuous
linear operator from the primal space `E` to the continuous dual `E⋆` obtained by differentiating
the gradient and composing with the Riesz identification `E ≃ E⋆`. -/
-- Proof sketch: view `y ↦ ∇ f y` as the first derivative of `f`, compose its derivative at `x`
-- with the forward Riesz map `InnerProductSpace.toDualMap`, and apply the chain rule.
theorem hessian_toDualMap_hasFDerivAt
    (f : E → ℝ) (x : E) (hf : DifferentiableAt ℝ (∇ f) x) :
    HasFDerivAt ((toDualMap ℝ E) ∘ ∇ f)
      ((toDualMap ℝ E).toContinuousLinearMap.comp (hessian f x)) x := by
  simpa [Function.comp] using
    ((toDualMap ℝ E).toContinuousLinearMap.hasFDerivAt.comp x hf.hasFDerivAt)

/-- If `f` is `C²` at `x`, then the intrinsic Hessian operator `hessian f x` is self-adjoint. -/
-- Proof sketch: identify the Hessian with the second derivative of `f`; Schwarz symmetry for the
-- second derivative gives a symmetric bilinear form, and on a real Hilbert space this is
-- equivalent to self-adjointness of the associated continuous linear operator.
theorem hessian_isSelfAdjoint_of_contDiffAt
    (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    IsSelfAdjoint (hessian f x) := by
  simpa using (fderiv_gradient_isSymmetric_of_contDiffAt hf).isSelfAdjoint
