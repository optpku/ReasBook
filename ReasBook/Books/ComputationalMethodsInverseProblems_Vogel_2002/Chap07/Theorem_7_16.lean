/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Notation_7_7
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Objective
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.OptimalIndex
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Reconstruction
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.Nullspace
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_16.ExpectedError
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

public section

open scoped Asymptotics TsvdEstimation.Notation

namespace TsvdEstimation

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
variable (K : ℕ → H →L[ℝ] F)
variable (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
variable (h_length : ∀ n, (S n).length = ⊤)
variable (fTrue : H) (b c p q σ : ℝ)
variable (η : ℕ → Ω → F)
variable (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
variable (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ)
variable (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
variable (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
variable
  (h_noise_modeVariance :
    ∀ n i,
      ∫ ω,
        (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
          σ ^ 2 / (n : ℝ))
variable (h_singularDecay :
  ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
variable (h_fourierDecay :
  ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
variable (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
variable {mE : ℕ → ℕ}
variable (h_estOptimal :
  ParameterChoice.IsOptimalParameterFamily
    (expectedSqErrorObjective μ K Rtsvd fTrue η)
    𝒵
    mE)

include h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd h_estOptimal

/-- Companion to Theorem 7.16 (1). Under the concrete Chapter 7 positivity,
semistochastic white-noise, and algebraic decay hypotheses for the TSVD
expected squared estimation-error objective, the estimation-optimal
truncation-index family `mE` eventually avoids the boundary values `0` and
`n` of the admissible set `𝒵(n)` because assumption `(7.56)` makes the
nullspace component vanish asymptotically and thereby excludes the boundary
minimizers for large `n`. -/
theorem optimalFamily_eventuallyAvoidsBoundary
    (h_vanishingNullspaceComponent :
      FilterRegularization.HasVanishingNullspaceComponent K fTrue) :
    ∀ᶠ n in Filter.atTop, 0 < mE n ∧ mE n < n := sorry

/-- Theorem 7.16 (1). Under the concrete Chapter 7 positivity, semistochastic
white-noise, and algebraic decay hypotheses for the TSVD expected squared
estimation-error objective on `𝒵(n)`, any estimation-optimal truncation-index
family `mE` eventually agrees with the explicit benchmark floor formula
`optimalIndex b c p q σ` from `(7.63)`; here
assumption `(7.56)` is what rules out boundary minimizers for sufficiently
large `n`. -/
theorem optimalFamily_eq_optimalIndex_eventually
    (h_vanishingNullspaceComponent :
      FilterRegularization.HasVanishingNullspaceComponent K fTrue) :
    mE =ᶠ[Filter.atTop] optimalIndex b c p q σ := sorry

/-- Theorem 7.16 (2). Under the same concrete Chapter 7 positivity,
semistochastic white-noise, algebraic decay, and vanishing-nullspace
hypotheses, any estimation-optimal family `mE` has expected squared TSVD
estimation error asymptotically equivalent to the nullspace term plus the
explicit TSVD benchmark profile `optimalErrorBenchmark K fTrue b c p q σ` from
`(7.64)`. -/
theorem expectedSqErrorAtOptimalFamily_isEquivalent
    (h_vanishingNullspaceComponent :
      FilterRegularization.HasVanishingNullspaceComponent K fTrue) :
    Asymptotics.IsEquivalent Filter.atTop
      (expectedSqErrorAlong μ K Rtsvd fTrue η mE)
      (optimalErrorBenchmark K fTrue b c p q σ) := sorry

/-- thm_7_16. Theorem 7.16 (Minimizer of Estimation Error for TSVD). Main
labeled source-facing entry.

The source theorem is recorded for the chosen estimation-optimal TSVD
truncation-index family `mE`, asserting the eventual floor formula together
with the matching asymptotic expected squared estimation-error profile. The
preceding companion theorems expose the arbitrary-family boundary-avoidance
claim and the two source clauses separately for later proof stages and
downstream reuse, with assumption `(7.56)` entering the minimizer-
identification clause that excludes the boundary cases. -/
theorem estimationOptimalFamily_spec
    (h_vanishingNullspaceComponent :
      FilterRegularization.HasVanishingNullspaceComponent K fTrue) :
    mE =ᶠ[Filter.atTop] optimalIndex b c p q σ ∧
      Asymptotics.IsEquivalent Filter.atTop
        (expectedSqErrorAlong μ K Rtsvd fTrue η mE)
        (optimalErrorBenchmark K fTrue b c p q σ) := sorry

omit h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd h_estOptimal

end

end TsvdEstimation
