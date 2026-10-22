/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_4.QuadraticFunctional
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

noncomputable section

open scoped Matrix

namespace GaussianMean

universe u

section

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The additive-constant-free negative log-likelihood in the unknown mean for a single
observed vector `d` from a Gaussian model with known covariance matrix `C`. -/
def negLogLikelihood (C : Matrix n n ℝ) (d : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n → ℝ :=
  fun μ ↦ (1 / 2 : ℝ) * inner ℝ ((C⁻¹).toEuclideanLin (d - μ)) (d - μ)

/-- The defining residual-form formula for `GaussianMean.negLogLikelihood`. -/
theorem negLogLikelihood_def (C : Matrix n n ℝ) (d μ : EuclideanSpace ℝ n) :
    negLogLikelihood C d μ =
      (1 / 2 : ℝ) * inner ℝ ((C⁻¹).toEuclideanLin (d - μ)) (d - μ) := by
  -- Unfold the objective once to expose the residual-form expression.
  rfl

/-- For positive-definite covariance, `GaussianMean.negLogLikelihood` is the quadratic functional
with matrix part `C⁻¹`, linear term `-C⁻¹ d`, and a constant depending only on `d`. -/
theorem negLogLikelihood_eq_quadraticFunctional
    (C : Matrix n n ℝ) (d : EuclideanSpace ℝ n) (hC : C.PosDef) :
    negLogLikelihood C d =
      QuadraticOptimization.quadraticFunctional
        ((1 / 2 : ℝ) * inner ℝ ((C⁻¹).toEuclideanLin d) d)
        (-Matrix.toEuclideanLin C⁻¹ d)
        C⁻¹ := by
  funext μ
  -- The inverse covariance acts self-adjointly because positive-definite matrices are symmetric.
  have hCinvSymm : (C⁻¹)ᵀ = C⁻¹ := by
    simpa using hC.inv.isHermitian.eq
  have hCinvAdj :
      ((C⁻¹).toEuclideanLin).adjoint = (C⁻¹).toEuclideanLin := by
    calc
      ((C⁻¹).toEuclideanLin).adjoint = ((C⁻¹)ᵀ).toEuclideanLin := by
        simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (C⁻¹)).symm
      _ = (C⁻¹).toEuclideanLin := by
        rw [hCinvSymm]
  have hCross :
      inner ℝ ((C⁻¹).toEuclideanLin μ) d =
        inner ℝ (Matrix.toEuclideanLin C⁻¹ d) μ := by
    calc
      inner ℝ ((C⁻¹).toEuclideanLin μ) d
          = inner ℝ μ (((C⁻¹).toEuclideanLin).adjoint d) := by
              simpa using
                (((C⁻¹).toEuclideanLin).adjoint_inner_right μ d).symm
      _ = inner ℝ μ ((C⁻¹).toEuclideanLin d) := by
            rw [hCinvAdj]
      _ = inner ℝ ((C⁻¹).toEuclideanLin d) μ := by
            rw [real_inner_comm]
      _ = inner ℝ (Matrix.toEuclideanLin C⁻¹ d) μ := rfl
  -- Expand the residual square, rewrite the mixed term, and regroup into quadratic form.
  rw [negLogLikelihood_def, QuadraticOptimization.quadraticFunctional_def, map_sub,
    inner_sub_left, inner_sub_right, inner_sub_right, hCross]
  rw [inner_neg_left]
  ring

/-- A candidate mean is a maximum-likelihood estimator exactly when it minimizes the negative
log-likelihood on `Set.univ`. -/
def IsMeanMLE (d : EuclideanSpace ℝ n) (C : Matrix n n ℝ) (μ : EuclideanSpace ℝ n) : Prop :=
  IsMinOn (negLogLikelihood C d) Set.univ μ

/-- The defining characterization of `GaussianMean.IsMeanMLE`. -/
theorem isMeanMLE_iff (d : EuclideanSpace ℝ n) (C : Matrix n n ℝ) (μ : EuclideanSpace ℝ n) :
    IsMeanMLE d C μ ↔ IsMinOn (negLogLikelihood C d) Set.univ μ := by
  -- This is just the defining proposition of `IsMeanMLE`.
  rfl

/-- Helper for Example 4.16: applying the covariance matrix after its inverse action returns the
original Euclidean vector. -/
lemma precisionAction_leftInverse
    (C : Matrix n n ℝ) (d : EuclideanSpace ℝ n) (hC : C.PosDef) :
    ((C⁻¹)⁻¹).toEuclideanLin ((C⁻¹).toEuclideanLin d) = d := by
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
  -- Rewrite the double inverse back to `C`, compose the two matrix actions, and cancel.
  calc
    ((C⁻¹)⁻¹).toEuclideanLin ((C⁻¹).toEuclideanLin d)
        = C.toEuclideanLin ((C⁻¹).toEuclideanLin d) := by
            rw [Matrix.nonsing_inv_nonsing_inv C hCdet]
    _ = Matrix.toEuclideanLin (C * C⁻¹) d := by
          simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    _ = Matrix.toEuclideanLin (1 : Matrix n n ℝ) d := by
          rw [Matrix.mul_nonsing_inv C hCdet]
    _ = d := by
          simp

/-- If `C` is positive definite, then the observed vector `d` is a Gaussian mean maximum-
likelihood estimator for the data `d`. -/
theorem isMeanMLE_observation
    (d : EuclideanSpace ℝ n) (C : Matrix n n ℝ) (hC : C.PosDef) :
    IsMeanMLE d C d := by
  -- Rewrite the MLE objective into the Chapter 3 quadratic normal form.
  rw [isMeanMLE_iff, negLogLikelihood_eq_quadraticFunctional C d hC]
  -- The positive-definite quadratic minimizer theorem gives the optimizer explicitly.
  simpa [LinearMap.map_neg, precisionAction_leftInverse C d hC] using
    (QuadraticOptimization.isMinOn_quadraticFunctional_of_posDef
      ((1 / 2 : ℝ) * inner ℝ ((C⁻¹).toEuclideanLin d) d)
      (-Matrix.toEuclideanLin C⁻¹ d)
      C⁻¹
      hC.inv)

/-- If `C` is positive definite, then every Gaussian mean maximum-likelihood estimator for the
data `d` is equal to the observed vector `d`. -/
theorem eq_observation_of_isMeanMLE
    (d : EuclideanSpace ℝ n) (C : Matrix n n ℝ) (hC : C.PosDef)
    {μ : EuclideanSpace ℝ n} (hμ : IsMeanMLE d C μ) :
    μ = d := by
  -- Reduce uniqueness of the MLE to uniqueness of the quadratic minimizer.
  rw [isMeanMLE_iff, negLogLikelihood_eq_quadraticFunctional C d hC] at hμ
  have hEq :=
    QuadraticOptimization.eq_minimizer_of_isMinOn_quadraticFunctional_of_posDef
      ((1 / 2 : ℝ) * inner ℝ ((C⁻¹).toEuclideanLin d) d)
      (-Matrix.toEuclideanLin C⁻¹ d)
      C⁻¹
      hC.inv
      hμ
  -- Collapse the abstract minimizer expression back to the observed data vector.
  simpa [LinearMap.map_neg, precisionAction_leftInverse C d hC] using hEq

end

end GaussianMean
