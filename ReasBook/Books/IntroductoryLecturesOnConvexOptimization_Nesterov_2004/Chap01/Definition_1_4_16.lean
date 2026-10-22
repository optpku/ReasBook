/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/- Definition 1.4.16 lies in the second-order differential-calculus domain on Euclidean space.

Source/core/bridge triage:
* source-facing: the Hessian matrix of `f : ℝⁿ → ℝ` at `xBar`
* core/canonical: the derivative of the gradient map, viewed as a continuous linear endomorphism
* bridge/view: the standard-basis matrix of that endomorphism

Sampled owner-style declarations:
* `gradient`
* `fderiv`
* `LinearMap.toMatrixOrthonormal`
* `Matrix.toEuclideanLin_eq_toLin_orthonormal`

The file therefore keeps the intrinsic operator owner `hessian f x` and exposes the textbook
matrix as its standard Euclidean matrix view. -/

/-- The Hessian of `f` at `x`, viewed intrinsically as the derivative of the gradient map. -/
abbrev hessian (f : X → ℝ) (x : X) : X →L[ℝ] X :=
  fderiv ℝ (∇ f) x

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

/-- Definition 1.4.16: if `f : ℝⁿ → ℝ`, the Hessian of `f` at `x` is the matrix of the
derivative of the gradient map in the standard orthonormal basis of `ℝⁿ`. -/
abbrev hessianMatrix (f : E → ℝ) (x : E) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrixOrthonormal e (hessian f x)

@[inherit_doc hessianMatrix]
scoped[Gradient] notation "∇²" => hessianMatrix

-- Proof sketch: unfold `hessianMatrix` and apply the entrywise formula for
-- `LinearMap.toMatrixOrthonormal` in the standard orthonormal basis.
/-- The `(i,j)` entry of the Hessian matrix is the inner product of the `i`th standard basis
vector with the Hessian operator applied to the `j`th standard basis vector. -/
theorem hessianMatrix_apply (f : E → ℝ) (x : E) (i j : Fin n) :
    ∇² f x i j = inner ℝ (e i) (hessian f x (e j)) := by
  simpa [hessianMatrix] using
    (LinearMap.toMatrixOrthonormal_apply_apply e (hessian f x) i j)

/-- Helper for Definition 1.4.16: the `i`th coordinate of the Euclidean gradient is the inner
product with the `i`th standard basis vector. -/
lemma gradient_coordinate_eq_inner_basis (f : E → ℝ) (i : Fin n) :
    (fun y : E ↦ ((∇ f) y) i) = fun y : E ↦ inner ℝ (e i) ((∇ f) y) := by
  -- The Euclidean orthonormal basis recovers coordinates by inner product.
  funext y
  simpa using (EuclideanSpace.basisFun_inner (x := ((∇ f) y)) (i := i)).symm

/-- Helper for Definition 1.4.16: the derivative of a gradient coordinate is obtained by composing
the Hessian operator with the corresponding coordinate functional. -/
lemma hasFDerivAt_gradient_coordinate
    (f : E → ℝ) (x : E) (i : Fin n) (hgrad : DifferentiableAt ℝ (∇ f) x) :
    HasFDerivAt (fun y : E ↦ ((∇ f) y) i) (((innerSL ℝ) (e i)).comp (hessian f x)) x := by
  -- Rewrite the coordinate map in the standard inner-product form.
  rw [gradient_coordinate_eq_inner_basis (f := f) (i := i)]
  -- The chain rule differentiates the fixed coordinate functional after the gradient.
  simpa [hessian, Function.comp, innerSL_apply_apply] using
    (((innerSL ℝ) (e i)).hasFDerivAt.comp x hgrad.hasFDerivAt)

/-- Helper for Definition 1.4.16: evaluating the derivative of the `i`th gradient coordinate on
the `j`th standard basis vector gives the corresponding Hessian inner-product entry. -/
lemma fderiv_gradient_coordinate_apply_basis
    (f : E → ℝ) (x : E) (i j : Fin n) (hgrad : DifferentiableAt ℝ (∇ f) x) :
    fderiv ℝ (fun y : E ↦ ((∇ f) y) i) x (e j) = inner ℝ (e i) (hessian f x (e j)) := by
  -- Replace the Fréchet derivative by the chain-rule derivative from the previous lemma.
  rw [(hasFDerivAt_gradient_coordinate (f := f) (x := x) (i := i) hgrad).fderiv]
  -- Evaluating the composed coordinate functional gives the advertised inner product.
  rfl

-- Proof sketch: combine `hessianMatrix_apply` with the coordinate formula for the gradient and
-- differentiate the `i`th gradient coordinate in the `j`th basis direction.
/-- Under differentiability of the gradient at `x`, the `(i,j)` entry of the Hessian matrix is
the derivative of the `i`th gradient coordinate in the `j`th standard basis direction, i.e. the
textbook second partial derivative. -/
theorem hessianMatrix_apply_eq_fderiv_gradient_coordinate
    (f : E → ℝ) (x : E) (i j : Fin n) (hgrad : DifferentiableAt ℝ (∇ f) x) :
    ∇² f x i j = fderiv ℝ (fun y : E ↦ ((∇ f) y) i) x (e j) := by
  -- First read the matrix entry through the intrinsic Hessian operator.
  rw [hessianMatrix_apply]
  -- Then identify the directional derivative of the gradient coordinate with the same quantity.
  rw [fderiv_gradient_coordinate_apply_basis (f := f) (x := x) (i := i) (j := j) hgrad]

-- Proof sketch: rewrite `∇² f x` as `LinearMap.toMatrixOrthonormal e (hessian f x)` and apply
-- `Matrix.toEuclideanLin_eq_toLin_orthonormal`.
/-- Turning the Hessian matrix back into its Euclidean linear action recovers the intrinsic
Hessian operator. -/
theorem hessianMatrix_toEuclideanLin (f : E → ℝ) (x : E) :
    (∇² f x).toEuclideanLin = hessian f x := by
  rw [hessianMatrix, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  simp

end
