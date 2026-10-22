/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

/- Algorithm 4.1.1 lies in the second-order / Levenberg--Marquardt regularization domain.

Sampled owner-style declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic Hessian operator owner;
* `hessianMatrix` / `∇²`, the Euclidean matrix bridge for that owner;
* `ContinuousLinearMap.det`, the intrinsic finite-dimensional nondegeneracy owner;
* `ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero`, the canonical inverse bridge for a
  nondegenerate operator;
* `Matrix.PosDef`, the Euclidean bridge owner for strict positivity.

Source/core/bridge triage:
* source-facing: the regularized Hessian `G_k` and the Levenberg--Marquardt update at `x_k`;
* core/canonical: the intrinsic operator `hessian f xk + γ • 1`;
* bridge/view: the textbook Euclidean matrix formula `G_k = ∇² f xk + γ I` together with the
  positive-definiteness witness on that matrix view.

Primitive data:
* the objective `f`;
* the current iterate `xk`;
* the regularization parameter `γ`.

Derived API:
* the intrinsic regularized Hessian operator;
* the intrinsic nondegeneracy hypothesis needed to invert that operator in finite dimensions;
* in Euclidean coordinates, the matrix identity
  `G_k = ∇² f(x_k) + γ I`;
* the Euclidean bridge from matrix positive definiteness to operator nondegeneracy;
* the regularized Newton step, defined through the intrinsic inverse operator and restated below
  in the textbook inverse-matrix form.

This refinement keeps the public owner on the intrinsic Hessian operator and treats the raw matrix
formula only as a Euclidean bridge. -/

section Core

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The intrinsic regularized Hessian operator
`G_k = hessian f xk + γ • 1` used by Algorithm 4.1.1. -/
abbrev levenbergMarquardtRegularizedHessian
    (f : E → ℝ) (xk : E) (γ : ℝ) : E →L[ℝ] E :=
  hessian f xk + γ • (1 : E →L[ℝ] E)

end Core

section Invertible

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance finiteDimensionalComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

/-- Algorithm 4.1.1 on the intrinsic operator layer: if the regularized Hessian operator
`G_k = hessian f xk + γ • 1` is nondegenerate, then the Levenberg--Marquardt update is obtained
by applying its inverse to the gradient. -/
def levenbergMarquardtRegularizedNewtonStep
    (f : E → ℝ) (xk : E) (γ : ℝ)
    (hG : (levenbergMarquardtRegularizedHessian f xk γ).det ≠ 0) : E :=
  xk - (((levenbergMarquardtRegularizedHessian f xk γ).toContinuousLinearEquivOfDetNeZero
    hG).symm (∇ f xk))

end Invertible

section Euclidean

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- The intrinsic regularized Hessian operator is the Euclidean linear action of the textbook
matrix `∇² f(x_k) + γ I`. -/
theorem levenbergMarquardtRegularizedHessian_eq_matrix_toEuclideanLin
    (f : E → ℝ) (xk : E) (γ : ℝ) :
    (levenbergMarquardtRegularizedHessian f xk γ : E →ₗ[ℝ] E) =
      (∇² f xk + γ • (1 : Mat)).toEuclideanLin := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  ext x
  simp [hessianMatrix, levenbergMarquardtRegularizedHessian]

/-- If the Euclidean matrix `∇² f(x_k) + γ I` is positive definite, then the intrinsic
regularized Hessian operator is nondegenerate. -/
theorem levenbergMarquardtRegularizedHessian_det_ne_zero_of_posDef
    (f : E → ℝ) (xk : E) (γ : ℝ)
    (hG : (∇² f xk + γ • (1 : Mat)).PosDef) :
    (levenbergMarquardtRegularizedHessian f xk γ).det ≠ 0 := by
  change LinearMap.det (levenbergMarquardtRegularizedHessian f xk γ).toLinearMap ≠ 0
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (levenbergMarquardtRegularizedHessian f xk γ).toLinearMap]
  simpa [hessianMatrix, levenbergMarquardtRegularizedHessian] using hG.det_pos.ne'

/-- In Euclidean coordinates, the intrinsic Levenberg--Marquardt step recovers the textbook
inverse-matrix formula `x_k - [∇² f(x_k) + γ I]⁻¹ ∇ f(x_k)`. -/
theorem levenbergMarquardtRegularizedNewtonStep_eq_matrixFormula
    (f : E → ℝ) (xk : E) (γ : ℝ)
    (hG : (levenbergMarquardtRegularizedHessian f xk γ).det ≠ 0) :
    levenbergMarquardtRegularizedNewtonStep f xk γ hG =
      xk - ((∇² f xk + γ • (1 : Mat))⁻¹).toEuclideanLin (∇ f xk) := by
  let A : Mat := ∇² f xk + γ • (1 : Mat)
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hA_det : A.det ≠ 0 := by
    have hG' :
        LinearMap.det (levenbergMarquardtRegularizedHessian f xk γ).toLinearMap ≠ 0 := by
      simpa using hG
    rw [← LinearMap.det_toMatrix b (levenbergMarquardtRegularizedHessian f xk γ).toLinearMap] at hG'
    simpa [A, hessianMatrix, levenbergMarquardtRegularizedHessian] using hG'
  let eM : E ≃ₗ[ℝ] E := Matrix.toLinearEquiv b A (isUnit_iff_ne_zero.mpr hA_det)
  let eF : E ≃ₗ[ℝ] E :=
    ((levenbergMarquardtRegularizedHessian f xk γ).toContinuousLinearEquivOfDetNeZero
      hG).toLinearEquiv
  have heq : eM = eF := by
    apply LinearEquiv.toLinearMap_injective
    change A.toEuclideanLin = (levenbergMarquardtRegularizedHessian f xk γ : E →ₗ[ℝ] E)
    simpa [A] using (levenbergMarquardtRegularizedHessian_eq_matrix_toEuclideanLin f xk γ).symm
  have hsymm := congrArg (fun e' : E ≃ₗ[ℝ] E ↦ e'.symm (∇ f xk)) heq
  have hmatrix :
      eM.symm (∇ f xk) = (A⁻¹).toEuclideanLin (∇ f xk) := by
    change (Matrix.toLinearEquiv b A (isUnit_iff_ne_zero.mpr hA_det)).symm (∇ f xk) =
      (Matrix.toLin b b A⁻¹) (∇ f xk)
    rfl
  calc
    levenbergMarquardtRegularizedNewtonStep f xk γ hG = xk - eF.symm (∇ f xk) := by
      rfl
    _ = xk - eM.symm (∇ f xk) := by
      simpa using congrArg (fun y ↦ xk - y) hsymm.symm
    _ = xk - (A⁻¹).toEuclideanLin (∇ f xk) := by rw [hmatrix]
    _ = xk - ((∇² f xk + γ • (1 : Mat))⁻¹).toEuclideanLin (∇ f xk) := by
      rfl

/-- Under the textbook Euclidean positive-definiteness hypothesis, the intrinsic
Levenberg--Marquardt step specializes to the usual inverse-matrix formula. -/
theorem levenbergMarquardtRegularizedNewtonStep_eq_matrixFormula_of_posDef
    (f : E → ℝ) (xk : E) (γ : ℝ)
    (hG : (∇² f xk + γ • (1 : Mat)).PosDef) :
    levenbergMarquardtRegularizedNewtonStep f xk γ
        (levenbergMarquardtRegularizedHessian_det_ne_zero_of_posDef f xk γ hG) =
      xk - ((∇² f xk + γ • (1 : Mat))⁻¹).toEuclideanLin (∇ f xk) :=
  levenbergMarquardtRegularizedNewtonStep_eq_matrixFormula f xk γ
    (levenbergMarquardtRegularizedHessian_det_ne_zero_of_posDef f xk γ hG)

end Euclidean
