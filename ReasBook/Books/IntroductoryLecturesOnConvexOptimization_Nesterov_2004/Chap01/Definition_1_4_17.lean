/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.FirstOrderTaylorModel
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section TaylorModel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 1.4.17 lies in the second-order local Taylor-model domain for smooth optimization.

Primary domain:
* second-order local models on real Hilbert spaces

Relevant owner-style declarations sampled before refining:
* `HasGradientAt` in mathlib, the owner for genuine first-order differential data
* `HasFDerivAt` in mathlib, the owner for genuine second-order differential data of the gradient
* `hessian` in `Definition_1_4_16`, the intrinsic operator-valued Hessian owner
* `hessianMatrix` in `Definition_1_4_16`, the Euclidean matrix view of that intrinsic Hessian

Source/core/bridge triage:
* source-facing/core: `secondOrderTaylorModelAt f x`
* bridge/view: the evaluation formula `secondOrderTaylorModelAt_apply`
* bridge/view: the Euclidean matrix rewrite
  `secondOrderTaylorModelAt_apply_hessianMatrix`

Primitive data:
* the function `f`
* the base point `x`

Derived API:
* pointwise evaluation of the quadratic model at `y`
* the `ℝⁿ` matrix realization via `∇² f x`

The public owner for this numbered item is therefore the second-order Taylor model itself. The
first-order Taylor model and the generic quadratic regularization operator live in the auxiliary
module `Chap01/FirstOrderTaylorModel`. -/

/-- Definition 1.4.17: the second-order Taylor model of `f` at `x`. -/
def secondOrderTaylorModelAt (f : E → ℝ) (x : E) : E → ℝ :=
  fun y ↦
    f x +
      inner ℝ (∇ f x) (y - x) +
        (1 / 2 : ℝ) * inner ℝ (hessian f x (y - x)) (y - x)

/-- Evaluating `secondOrderTaylorModelAt f x` recovers the displayed quadratic formula. -/
@[simp] theorem secondOrderTaylorModelAt_apply (f : E → ℝ) (x y : E) :
    secondOrderTaylorModelAt f x y =
      f x +
        inner ℝ (∇ f x) (y - x) +
          (1 / 2 : ℝ) * inner ℝ (hessian f x (y - x)) (y - x) :=
  rfl

section EuclideanSpace

variable {n : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin n)

/-- On `ℝⁿ`, the quadratic Taylor model can be rewritten using the Hessian matrix `∇² f x`
acting on the displacement `y - x`. -/
theorem secondOrderTaylorModelAt_apply_hessianMatrix
    (f : F → ℝ) (x y : F) :
    secondOrderTaylorModelAt f x y =
      f x +
        inner ℝ (∇ f x) (y - x) +
          (1 / 2 : ℝ) * inner ℝ ((∇² f x).toEuclideanLin (y - x)) (y - x) := by
  rw [secondOrderTaylorModelAt_apply]
  have hlin :
      (∇² f x).toEuclideanLin (y - x) = hessian f x (y - x) := by
    simpa using
      congrArg (fun T : F →ₗ[ℝ] F ↦ T (y - x)) (hessianMatrix_toEuclideanLin f x)
  rw [← hlin]

end EuclideanSpace

end TaylorModel
