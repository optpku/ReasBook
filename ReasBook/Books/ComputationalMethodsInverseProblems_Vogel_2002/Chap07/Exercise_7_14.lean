/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Objective
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Reconstruction
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_18.PredictiveRisk

public section

open scoped TsvdEstimation.Notation

namespace TsvdEstimation

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable (μ : MeasureTheory.Measure Ω)
variable [MeasureTheory.IsProbabilityMeasure μ]
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
          σ ^ 2)
variable
  (h_singularDecay :
    ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
variable
  (h_fourierDecay :
    ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
variable (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)

include h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd

/-- Exercise 7.14 (1). In the Chapter 7 predictive-risk noise regime where
every left singular mode has variance `σ ^ 2`, for sufficiently large `n` the
lower endpoint `m = 0` does not minimize the TSVD expected predictive-risk
objective on the source admissible set `𝒵(n)`. This is one of the endpoint
exclusions used to prove Theorem 7.18. -/
theorem lowerEndpoint_not_minimizer_eventually :
    ∀ᶠ n in Filter.atTop,
      ¬ IsMinOn
          (expectedPredictiveRiskObjective μ K Rtsvd fTrue η n)
          (𝒵(n))
          0 := sorry

/-- Exercise 7.14 (2). In the Chapter 7 predictive-risk noise regime where
every left singular mode has variance `σ ^ 2`, for sufficiently large `n` the
upper endpoint `m = n` does not minimize the TSVD expected predictive-risk
objective on the source admissible set `𝒵(n)`. This is the second endpoint
exclusion used to prove Theorem 7.18. -/
theorem upperEndpoint_not_minimizer_eventually :
    ∀ᶠ n in Filter.atTop,
      ¬ IsMinOn
          (expectedPredictiveRiskObjective μ K Rtsvd fTrue η n)
          (𝒵(n))
          n := sorry

/-- Companion to Exercise 7.14. The Chapter 7 predictive-risk objective
eventually excludes both boundary points of the admissible set `𝒵(n)` from
being minimizers at the same time. -/
theorem endpoints_not_minimizers_eventually :
    ∀ᶠ n in Filter.atTop,
      ¬ IsMinOn
          (expectedPredictiveRiskObjective μ K Rtsvd fTrue η n)
          (𝒵(n))
          0 ∧
        ¬ IsMinOn
          (expectedPredictiveRiskObjective μ K Rtsvd fTrue η n)
          (𝒵(n))
          n := by
  filter_upwards
    [lowerEndpoint_not_minimizer_eventually
      μ K S h_length fTrue b c p q σ η Rtsvd h_b h_c h_p h_q h_σ h_noise_memLp
      h_noise_meanZero h_noise_modeVariance h_singularDecay h_fourierDecay h_tsvd,
      upperEndpoint_not_minimizer_eventually
        μ K S h_length fTrue b c p q σ η Rtsvd h_b h_c h_p h_q h_σ h_noise_memLp
        h_noise_meanZero h_noise_modeVariance h_singularDecay h_fourierDecay h_tsvd]
    with n h_lower h_upper
  exact ⟨h_lower, h_upper⟩

omit h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd

end

end TsvdEstimation
