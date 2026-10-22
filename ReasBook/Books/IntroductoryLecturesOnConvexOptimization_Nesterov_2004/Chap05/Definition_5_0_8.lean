/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

/- Definition 5.0.8 lies in the finite-dimensional real Euclidean third-order differential
calculus domain.

Source/core/bridge triage:
* source-facing: the textbook matrix surface `f'''(x)[u]`
* core/canonical: the directional derivative operator `fderiv ℝ (hessian f) x u`
* bridge/view: its standard-basis matrix on `ℝⁿ`

Primary domain:
* third-order differential calculus for real-valued functions on finite-dimensional real
  inner-product spaces, with a Euclidean matrix bridge on `ℝⁿ`

Sampled owner-style declarations:
* `hessian` / `hessianMatrix` / `∇²` in `Chap01/Definition_1_4_16`
* `LinearMap.toMatrixOrthonormal`
* `LinearMap.toMatrixOrthonormal_apply_apply`
* `Matrix.toEuclideanLin_eq_toLin_orthonormal`

Best owner abstraction:
* the operator-valued directional derivative of the Hessian map, reused directly as
  `fderiv ℝ (hessian f) x u` from the chapter owner `hessian`

Primitive data:
* `f : E → ℝ`
* `x u : E`

Derived API:
* the intrinsic operator expression `fderiv ℝ (hessian f) x u`
* its standard-basis matrix surface on `ℝⁿ`

This refinement keeps `fderiv ℝ (hessian f) x u` as the owner and exposes the Euclidean matrix
surface only as a thin bridge abbreviation plus notation, matching the chapter style for `∇²`. -/

section EuclideanMatrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

/-- Definition 5.0.8: the textbook matrix `f'''(x)[u]`, viewed as the standard-basis matrix of
the canonical operator `fderiv ℝ (hessian f) x u`. This is only a Euclidean matrix bridge; the
owner remains the operator `fderiv ℝ (hessian f) x u`. -/
abbrev thirdDerivativeMatrix (f : E → ℝ) (x u : E) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrixOrthonormal e (fderiv ℝ (hessian f) x u)

@[inherit_doc thirdDerivativeMatrix]
scoped[Gradient] notation "∇³" => thirdDerivativeMatrix

-- Proof sketch: unfold `thirdDerivativeMatrix` and apply the entrywise formula for
-- `LinearMap.toMatrixOrthonormal` in the standard orthonormal basis.
/-- The `(i,j)` entry of the textbook matrix `∇³ f x u` is the inner product of the `i`th
standard basis vector with the Hessian-direction operator `fderiv ℝ (hessian f) x u` applied to
the `j`th standard basis vector. -/
theorem thirdDerivativeMatrix_apply (f : E → ℝ) (x u : E) (i j : Fin n) :
    ∇³ f x u i j = inner ℝ (e i) (fderiv ℝ (hessian f) x u (e j)) := by
  simpa [thirdDerivativeMatrix] using
    (LinearMap.toMatrixOrthonormal_apply_apply e (fderiv ℝ (hessian f) x u) i j)

-- Proof sketch: rewrite `∇³ f x u` as `LinearMap.toMatrixOrthonormal e (fderiv ℝ (hessian f) x
-- u)` and apply `Matrix.toEuclideanLin_eq_toLin_orthonormal`.
/-- Turning the Euclidean matrix `∇³ f x u` back into its linear action recovers the intrinsic
directional derivative operator of the Hessian. -/
theorem thirdDerivativeMatrix_toEuclideanLin (f : E → ℝ) (x u : E) :
    (∇³ f x u).toEuclideanLin = fderiv ℝ (hessian f) x u := by
  rw [thirdDerivativeMatrix, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  simp

end EuclideanMatrix
