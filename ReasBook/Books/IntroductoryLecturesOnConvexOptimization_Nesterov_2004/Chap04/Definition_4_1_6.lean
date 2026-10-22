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

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 4.1.6 lies in the cubic-regularization / Hessian-spectrum domain on finite-dimensional
real inner-product spaces.

Sampled owner declarations:
* `hessian` and `hessianMatrix` in `Chap01/Definition_1_4_16`, the intrinsic Hessian owner and
  its Euclidean matrix bridge;
* `spectrum ℝ T`, the canonical spectral owner for a real endomorphism or matrix;
* `ContinuousLinearMap.spectrum_eq` and `Matrix.spectrum_toLpLin`, the canonical bridges between
  the intrinsic Hessian operator and its standard-basis matrix realization.

Best owner abstraction:
* source-facing: the cubic-regularization decrement `δ_k`;
* core/canonical: `‖∇ f x‖` together with `sInf (spectrum ℝ (hessian f x))`;
* bridge/view: the matrix shorthands `λ_min(H)`, `λ_max(H)`, and the Euclidean Hessian-matrix
  spectral formula below.

Primitive data:
* the ambient finite-dimensional real inner-product space `E`;
* an objective `f : E → ℝ`;
* a point `x` or iterate `xk`;
* a scalar `L`.

Derived API:
* the thin matrix-spectrum abbreviations `Matrix.leastEigenvalue` and
  `Matrix.greatestEigenvalue`;
* the intrinsic Hessian least-spectral-value owner `hessianLeastEigenvalue`;
* the source-facing decrement owner `cubicRegularizationDelta`;
* the Euclidean bridge identifying `hessianLeastEigenvalue` with the spectrum of the Hessian
  matrix.

This keeps the source-facing decrement owner from the text, but treats the matrix spectral names as
thin bridge vocabulary over the canonical spectrum owner instead of as an independent second layer
of primitive data. -/

namespace Matrix

/-- The textbook least-eigenvalue quantity of a real square matrix, defined as the infimum of its
real spectrum. For a symmetric real matrix, this is the usual smallest eigenvalue. -/
abbrev leastEigenvalue {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℝ) : ℝ :=
  sInf (spectrum ℝ H)

/-- The textbook greatest-eigenvalue quantity of a real square matrix, defined as the supremum of
its real spectrum. For a symmetric real matrix, this is the usual largest eigenvalue. -/
abbrev greatestEigenvalue {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℝ) : ℝ :=
  sSup (spectrum ℝ H)

end Matrix

notation:max "λ_min(" H:max ")" => Matrix.leastEigenvalue H
notation:max "λ_max(" H:max ")" => Matrix.greatestEigenvalue H

/-- The textbook least-Hessian-eigenvalue quantity at `x`, defined from the real spectrum of the
intrinsic Hessian operator `hessian f x`. On `ℝⁿ`, the standard-basis Hessian matrix formula is a
bridge theorem. When `f` is `C²` at `x`, the Hessian is symmetric, so this is the usual least
eigenvalue of the Hessian matrix. -/
abbrev hessianLeastEigenvalue (f : E → ℝ) (x : E) : ℝ :=
  sInf (spectrum ℝ (hessian f x))

scoped[Gradient] notation:max "λ_min(" "∇²" f:max x:max ")" => hessianLeastEigenvalue f x

/-- Definition 4.1.6: for the textbook cubic-regularization quantity attached to a twice
continuously differentiable real objective `f`, a scalar `L > 0`, and an iterate `x_k`, the
quantity `δ_k` is `L * ‖∇ f(x_k)‖ / λ_min(∇²f(x_k))^2`. -/
def cubicRegularizationDelta (f : E → ℝ) (xk : E) (L : ℝ) : ℝ :=
  L * ‖∇ f xk‖ / (λ_min(∇² f xk)) ^ 2

/-- Unfolding `cubicRegularizationDelta` gives the textbook formula in terms of the intrinsic
gradient norm and least Hessian spectral value. -/
@[simp] theorem cubicRegularizationDelta_def (f : E → ℝ) (xk : E) (L : ℝ) :
    cubicRegularizationDelta f xk L =
      L * ‖∇ f xk‖ / (λ_min(∇² f xk)) ^ 2 :=
  rfl

section

variable {n : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin n)

/-- On `ℝⁿ`, the intrinsic least-Hessian-spectral-value owner agrees with the infimum of the real
spectrum of the standard-basis Hessian matrix. -/
theorem hessianLeastEigenvalue_eq_sInf_spectrum_hessianMatrix (f : F → ℝ) (x : F) :
    λ_min(∇² f x) = sInf (spectrum ℝ (∇² f x)) := by
  unfold hessianLeastEigenvalue
  rw [ContinuousLinearMap.spectrum_eq]
  rw [← Matrix.spectrum_toLpLin 2]
  rw [hessianMatrix_toEuclideanLin]

end
