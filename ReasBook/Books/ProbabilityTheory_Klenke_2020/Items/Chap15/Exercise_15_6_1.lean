/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory RealInnerProductSpace

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: push forward the law `multivariateGaussian μ C` along the continuous linear map
-- `Matrix.toEuclideanLin A`. The image law is still Gaussian by `HasGaussianLaw.map`, and
-- `integral_id_multivariateGaussian` together with `covariance_eval_multivariateGaussian` and
-- Gaussian measure extensionality identifies its mean and covariance matrix as `A μ` and
-- `A * C * A.transpose`.
/-- Exercise 15.6.1: if `X` has multivariate Gaussian law with mean `μ` and covariance matrix `C`,
then the linear image `A X` has multivariate Gaussian law with mean `A μ` and covariance matrix
`A C Aᵀ`. -/
theorem hasLaw_matrix_image_of_hasLaw_multivariateGaussian
    {P : Measure Ω} {d m : ℕ} {X : Ω → EuclideanSpace ℝ (Fin d)}
    (μ : EuclideanSpace ℝ (Fin d)) (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (A : Matrix (Fin m) (Fin d) ℝ) (hX : HasLaw X (multivariateGaussian μ C) P) :
    HasLaw (fun ω ↦ Matrix.toEuclideanLin A (X ω))
      (multivariateGaussian (Matrix.toEuclideanLin A μ) (A * C * A.transpose)) P := by
  let L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hAC : (A * C * A.transpose).PosSemidef :=
    hC.mul_mul_conjTranspose_same A
  have hA :
      HasLaw L
        (multivariateGaussian (Matrix.toEuclideanLin A μ) (A * C * A.transpose))
        (multivariateGaussian μ C) := by
    refine ⟨by fun_prop, ?_⟩
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id L,
        integral_id_multivariateGaussian]
      simp [L]
    · ext x y
      have hLadj : L.adjoint = (Matrix.toEuclideanLin A.transpose).toContinuousLinearMap := by
        rw [show L = (Matrix.toEuclideanLin A).toContinuousLinearMap by rfl,
          ← LinearMap.adjoint_toContinuousLinearMap (Matrix.toEuclideanLin A)]
        simpa using congrArg LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
      have hx : (L.adjoint x).ofLp = A.transpose.mulVec x.ofLp := by
        rw [hLadj]
        change ((Matrix.toLpLin 2 2 A.transpose) x).ofLp = A.transpose.mulVec x.ofLp
        simp
      have hy : (L.adjoint y).ofLp = A.transpose.mulVec y.ofLp := by
        rw [hLadj]
        change ((Matrix.toLpLin 2 2 A.transpose) y).ofLp = A.transpose.mulVec y.ofLp
        simp
      calc
        covarianceBilin ((multivariateGaussian μ C).map L) x y
            = covarianceBilin (multivariateGaussian μ C) (L.adjoint x) (L.adjoint y) := by
                simpa using covarianceBilin_map IsGaussian.memLp_two_id L x y
        _ = (L.adjoint x).ofLp ⬝ᵥ (C.mulVec (L.adjoint y).ofLp) := by
              rw [covarianceBilin_multivariateGaussian hC]
        _ = A.transpose.mulVec x.ofLp ⬝ᵥ (C.mulVec (A.transpose.mulVec y.ofLp)) := by rw [hx, hy]
        _ = x.ofLp ⬝ᵥ ((A * C * A.transpose).mulVec y.ofLp) := by
              rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec,
                Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
              simp [Matrix.mul_assoc]
        _ =
            covarianceBilin
              (multivariateGaussian (Matrix.toEuclideanLin A μ) (A * C * A.transpose)) x y := by
              rw [covarianceBilin_multivariateGaussian hAC]
  simpa [L, Function.comp] using hA.comp hX
