/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

/-
Definition 4.1.4 lies in the cubic-regularization local-optimality domain on finite-dimensional
real inner-product spaces.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`;
* the `Gradient`-scope notation `∇` from mathlib;
* `spectrum ℝ (hessian f x)`, the canonical spectral owner for the intrinsic Hessian operator;
* `sInf` and `max` on `ℝ`, the canonical owners for the least spectral value and the textbook
  “take the larger defect” construction.

Source/core/bridge triage:
* source-facing: `cubicRegularizationLocalOptimalityMeasure`;
* core/canonical: `‖∇ f x‖` and `sInf (spectrum ℝ (hessian f x))`;
* bridge/view: the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)` used downstream when
  the Hessian is later displayed as a matrix and its least spectral value is written as
  `λ_min(∇² f x)`.

Primitive data:
* an ambient space `E`;
* an objective `f : E → ℝ`;
* scalars `L` and `M`;
* a point `x`.

Derived API:
* the defining formula for the source-facing local optimality measure;
* the owner notation `μ[f; L; M](x)`, with the textbook shorthand `μ[M](x)` recovered locally
  downstream once `f` and `L` are fixed.

This keeps the source-facing owner from the text but moves it to the same intrinsic ambient layer
as the chapter's Hessian owner, while using the primitive canonical spectral term directly instead
of depending on the later local alias for the least Hessian eigenvalue. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Definition 4.1.4: the local optimality measure `μ_M(x)` for cubic regularization is the
maximum of the square root of the scaled gradient norm term and the scaled negative least Hessian
eigenvalue term. -/
def cubicRegularizationLocalOptimalityMeasure (f : E → ℝ) (L M : ℝ) (x : E) : ℝ :=
  max (Real.sqrt ((2 / (L + M)) * ‖∇ f x‖))
    (-(2 / (2 * L + M)) * sInf (spectrum ℝ (hessian f x)))

namespace CubicRegularizationLocalOptimalityMeasure

scoped notation:max "μ[" f ";" L ";" M "](" x ")" =>
  cubicRegularizationLocalOptimalityMeasure f L M x

end CubicRegularizationLocalOptimalityMeasure

open scoped CubicRegularizationLocalOptimalityMeasure

-- Proof sketch: this is the defining expansion of
-- `cubicRegularizationLocalOptimalityMeasure`.
/-- The local optimality measure `μ[f; L; M](x)` is given by the textbook maximum formula. -/
@[simp] theorem cubicRegularizationLocalOptimalityMeasure_eq_max
    (f : E → ℝ) (L M : ℝ) (x : E) :
    μ[f; L; M](x) =
      max (Real.sqrt ((2 / (L + M)) * ‖∇ f x‖))
        (-(2 / (2 * L + M)) * sInf (spectrum ℝ (hessian f x))) :=
  rfl

-- Proof sketch: rewrite `μ[f; L; M](x)` using
-- `cubicRegularizationLocalOptimalityMeasure_eq_max`; the claim is then `le_max_left`.
/-- The scaled gradient term is bounded above by the local optimality measure. -/
theorem sqrt_scaledGradientNorm_le_cubicRegularizationLocalOptimalityMeasure
    (f : E → ℝ) (L M : ℝ) (x : E) :
    Real.sqrt ((2 / (L + M)) * ‖∇ f x‖) ≤ μ[f; L; M](x) := by
  rw [cubicRegularizationLocalOptimalityMeasure_eq_max]
  exact le_max_left _ _

-- Proof sketch: rewrite `μ[f; L; M](x)` using
-- `cubicRegularizationLocalOptimalityMeasure_eq_max`; the claim is then `le_max_right`.
/-- The scaled negative least-Hessian-eigenvalue term is bounded above by the local optimality
measure. -/
theorem scaledNegLeastHessianEigenvalue_le_cubicRegularizationLocalOptimalityMeasure
    (f : E → ℝ) (L M : ℝ) (x : E) :
    -(2 / (2 * L + M)) * sInf (spectrum ℝ (hessian f x)) ≤ μ[f; L; M](x) := by
  rw [cubicRegularizationLocalOptimalityMeasure_eq_max]
  exact le_max_right _ _

end
