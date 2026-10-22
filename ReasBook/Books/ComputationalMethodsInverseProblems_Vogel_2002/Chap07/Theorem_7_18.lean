/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Notation_7_7.OptimalFamily
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Objective
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.OptimalIndex
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Reconstruction
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_18.PredictiveRisk
public import Mathlib.Order.Filter.Extr

public section

open scoped TsvdEstimation.Notation

namespace TsvdEstimation

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Any TSVD predictive-optimal truncation-index family on the Chapter 7
admissible sets `𝒵(n)` agrees eventually with the explicit benchmark
`optimalIndex b c p q σ`. -/
theorem predictiveOptimalFamily_eq_optimalIndex_eventually
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H) (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (mP : ℕ → ℕ)
    (h_p : 1 < p) (h_q : 1 < q)
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_predOptimal :
      ParameterChoice.IsOptimalParameterFamily
        (expectedPredictiveRiskObjective μ K Rtsvd fTrue η)
        𝒵
        mP) :
    mP =ᶠ[Filter.atTop] optimalIndex b c p q σ := sorry

/-- Theorem 7.18 (Minimizer of Predictive Risk for TSVD). For TSVD
regularization, for sufficiently large `n` the minimizer of the expected
predictive risk is identical to the minimizer `mE` of the expected squared norm
of the estimation error from Theorem 7.16, both taken over the admissible set
`𝒵(n)`. -/
theorem predictiveOptimalFamily_eq_estimationOptimalFamily_eventually
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H) (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (mP mE : ℕ → ℕ)
    (h_p : 1 < p) (h_q : 1 < q)
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_predOptimal :
      ParameterChoice.IsOptimalParameterFamily
        (expectedPredictiveRiskObjective μ K Rtsvd fTrue η)
        𝒵
        mP)
    (h_estOptimal :
      ParameterChoice.IsOptimalParameterFamily
        (expectedSqErrorObjective μ K Rtsvd fTrue η)
        𝒵
        mE) :
    mP =ᶠ[Filter.atTop] mE := sorry

end

end TsvdEstimation
