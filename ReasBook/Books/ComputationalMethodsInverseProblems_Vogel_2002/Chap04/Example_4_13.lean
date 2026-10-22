/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_12.Covariance
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.HasLaw

public section

noncomputable section

open scoped ProbabilityTheory

namespace ProbabilityTheory

/- Example 4.13 (1). The canonical multivariate normal owner is
`multivariateGaussian μ C` on `EuclideanSpace ℝ n`.
This file keeps the textbook density formula and the notation `X ∼ Normal (μ, C)`
as prose only, records the source-facing mean/covariance consequences through
`HasLaw` bridge theorems, and retains the source clause that the parameters `μ`
and `C` characterize the Gaussian distribution. -/
#check multivariateGaussian
#check integral_id_multivariateGaussian

namespace HasLaw

universe u v

/-- Example 4.13 (2). If `X` has law `multivariateGaussian μ C`
under `P`, then its mean is `μ`. -/
theorem integral_eq_of_multivariateGaussian
    {Ω : Type u} {n : Type v} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    {P : MeasureTheory.Measure Ω}
    {X : Ω → EuclideanSpace ℝ n} {μ : EuclideanSpace ℝ n} {C : Matrix n n ℝ}
    (hX : HasLaw X (multivariateGaussian μ C) P) :
    ∫ ω, X ω ∂P = μ := by
  calc
    ∫ ω, X ω ∂P = ∫ x, x ∂multivariateGaussian μ C := by
      simpa using hX.integral_eq
    _ = μ := integral_id_multivariateGaussian

/-- Example 4.13 (3). If `X` has law `multivariateGaussian μ C`
under `P` and `C` is positive semidefinite, then the covariance matrix of `X` is `C`. -/
theorem covarianceMatrix_eq_of_multivariateGaussian
    {Ω : Type u} {n : Type v} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    {P : MeasureTheory.Measure Ω}
    {X : Ω → EuclideanSpace ℝ n} {μ : EuclideanSpace ℝ n} {C : Matrix n n ℝ}
    (hX : HasLaw X (multivariateGaussian μ C) P) (hC : C.PosSemidef) :
    covarianceMatrix P X = C := by
  ext i j
  rw [covarianceMatrix_apply]
  have hi :
      AEMeasurable (fun x : EuclideanSpace ℝ n ↦ x i) (multivariateGaussian μ C) :=
    Measurable.aemeasurable <| by fun_prop
  have hj :
      AEMeasurable (fun x : EuclideanSpace ℝ n ↦ x j) (multivariateGaussian μ C) :=
    Measurable.aemeasurable <| by fun_prop
  have hCov :
      cov[fun ω ↦ X ω i, fun ω ↦ X ω j; P] =
        cov[fun x ↦ x i, fun x ↦ x j; multivariateGaussian μ C] := by
    simpa using hX.covariance_fun_comp hi hj
  exact hCov.trans (covariance_eval_multivariateGaussian hC i j)

end HasLaw

/-- Example 4.13 (4). For positive-semidefinite covariance matrices, the parameters `μ` and `C`
characterize the multivariate Gaussian distribution. -/
theorem multivariateGaussian_ext_iff
    {n : Type u} [Fintype n] [DecidableEq n]
    {μ₁ μ₂ : EuclideanSpace ℝ n} {C₁ C₂ : Matrix n n ℝ}
    (hC₁ : C₁.PosSemidef) (hC₂ : C₂.PosSemidef) :
    multivariateGaussian μ₁ C₁ = multivariateGaussian μ₂ C₂ ↔
      μ₁ = μ₂ ∧ C₁ = C₂ := by
  constructor
  · intro h
    have hμ : μ₁ = μ₂ := by
      simpa [integral_id_multivariateGaussian] using
        congrArg (fun ν ↦ ∫ x, x ∂ν) h
    have hC : C₁ = C₂ := by
      ext i j
      simpa [covariance_eval_multivariateGaussian hC₁ i j,
        covariance_eval_multivariateGaussian hC₂ i j] using
          congrArg (fun ν ↦ cov[fun x ↦ x i, fun x ↦ x j; ν]) h
    exact ⟨hμ, hC⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end ProbabilityTheory
