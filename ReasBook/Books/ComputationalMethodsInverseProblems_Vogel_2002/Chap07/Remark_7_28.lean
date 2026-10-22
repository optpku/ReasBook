/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_28.CriticalDiscrepancy
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.ExpectedError
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_27.Benchmark
public import Mathlib.Analysis.Asymptotics.Theta

open scoped Asymptotics

public section

/-! Remark 7.28.

Comparing the critical discrepancy benchmark from Theorem 7.27 with the
predictive-risk discussion around `(7.86)`, the source says that the
predictive-risk parameter sequence `α_P` and the discrepancy-principle
sequence `α_discrep` decay at the same rate as `n → ∞`.

The current repository already exposes the discrepancy-side critical theorem
`TikhonovDiscrepancy.isEquivalent_critical`, but the predictive-side critical
theorem is still missing upstream. This file therefore records the reusable
benchmark bridge behind the remark: once a predictive critical benchmark `β_P`
is known to have the same asymptotic rate as the canonical discrepancy
benchmark `β_discrep`, every predictive family asymptotically optimal relative
to `β_P` has the same rate as every discrepancy-principle family `α_discrep`.
-/

namespace TikhonovPredictiveRisk

universe u v w

section

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable (K : ℕ → H →L[ℝ] F)
variable (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
variable (h_length : ∀ n, (S n).length = ⊤)
variable (fTrue : H) (b c p q σ : ℝ)
variable (d η : ℕ → F)
variable (Rtikh : ℕ → ℝ → F →L[ℝ] H)
variable (betaP alphaP alphaDiscrep : ℕ → ℝ)

/-- Helper for Remark 7.28: in the critical regime `p - q = -1`, every
Chapter 7 Tikhonov discrepancy-principle family `α_discrep` has the same
asymptotic rate as the canonical discrepancy benchmark `β_discrep`. -/
private theorem discrepancyFamily_isEquivalent_criticalBenchmark
    (h_standing :
      FilterRegularization.StandingAssumptions
        K S h_length fTrue c p b q d η
        (fun n ↦ Rtikh n (alphaDiscrep n)) alphaDiscrep)
    (h_tikhonov : TikhonovEstimation.IsTikhonovReconstructionFamily K S Rtikh)
    (h_alphaDiscrep :
      TikhonovDiscrepancy.IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_critical : p - q = -1) :
    Asymptotics.IsEquivalent Filter.atTop alphaDiscrep
      (TikhonovDiscrepancy.betaDiscrep b c p σ) := by
  -- Route correction: consume the theorem-local critical bridge rather than
  -- importing the still-broken aggregate `Book.Ch7.Theorem_7_27` file.
  exact
    TikhonovDiscrepancy.discrepancyFamily_isEquivalent_criticalBenchmark_local
      K S h_length fTrue b c p q σ d η Rtikh alphaDiscrep
      h_standing h_tikhonov h_alphaDiscrep h_b h_c h_p h_q h_σ h_critical

/-- Benchmark-level bridge behind Remark 7.28. In the critical regime
`p - q = -1`, if a predictive critical benchmark `β_P` is asymptotically
equivalent to the canonical discrepancy benchmark `β_discrep`, then `β_P` has
the same rate as every Chapter 7 Tikhonov discrepancy-principle family
`α_discrep`. -/
theorem predictiveBenchmark_isEquivalent_critical_discrepancyFamily
    (h_betaP_discrep :
      Asymptotics.IsEquivalent Filter.atTop betaP
        (TikhonovDiscrepancy.betaDiscrep b c p σ))
    (h_standing :
      FilterRegularization.StandingAssumptions
        K S h_length fTrue c p b q d η
        (fun n ↦ Rtikh n (alphaDiscrep n)) alphaDiscrep)
    (h_tikhonov : TikhonovEstimation.IsTikhonovReconstructionFamily K S Rtikh)
    (h_alphaDiscrep :
      TikhonovDiscrepancy.IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_critical : p - q = -1) :
    Asymptotics.IsEquivalent Filter.atTop betaP alphaDiscrep := by
  have h_alphaDiscrep_beta :
      Asymptotics.IsEquivalent Filter.atTop alphaDiscrep
        (TikhonovDiscrepancy.betaDiscrep b c p σ) :=
    -- First bridge the discrepancy family to the canonical critical benchmark.
    discrepancyFamily_isEquivalent_criticalBenchmark
      K S h_length fTrue b c p q σ d η Rtikh alphaDiscrep
      h_standing h_tikhonov h_alphaDiscrep h_b h_c h_p h_q h_σ h_critical
  -- Reverse the discrepancy-side equivalence so the predictive benchmark can
  -- compose directly with it.
  exact h_betaP_discrep.trans h_alphaDiscrep_beta.symm

/-- Benchmark-level `=Θ` form of
`predictiveBenchmark_isEquivalent_critical_discrepancyFamily`. -/
theorem predictiveBenchmark_isTheta_critical_discrepancyFamily
    (h_betaP_discrep :
      Asymptotics.IsEquivalent Filter.atTop betaP
        (TikhonovDiscrepancy.betaDiscrep b c p σ))
    (h_standing :
      FilterRegularization.StandingAssumptions
        K S h_length fTrue c p b q d η
        (fun n ↦ Rtikh n (alphaDiscrep n)) alphaDiscrep)
    (h_tikhonov : TikhonovEstimation.IsTikhonovReconstructionFamily K S Rtikh)
    (h_alphaDiscrep :
      TikhonovDiscrepancy.IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_critical : p - q = -1) :
    betaP =Θ[Filter.atTop] alphaDiscrep := by
  exact
    (predictiveBenchmark_isEquivalent_critical_discrepancyFamily
      K S h_length fTrue b c p q σ d η Rtikh betaP alphaDiscrep
      h_betaP_discrep h_standing h_tikhonov h_alphaDiscrep
      h_b h_c h_p h_q h_σ h_critical).isTheta

/-- Remark 7.28. In the critical regime `p - q = -1`, if `α_P` is
asymptotically optimal relative to a predictive critical benchmark `β_P`, and
that benchmark has the same asymptotic rate as the canonical discrepancy
benchmark `β_discrep`, then `α_P` is asymptotically equivalent to every
discrepancy-principle Tikhonov parameter family `α_discrep`. This keeps the
missing predictive-side input at the benchmark layer rather than assuming in
advance that `α_P` already has the discrepancy benchmark rate. -/
theorem isEquivalent_critical_discrepancyFamily
    (h_alphaP :
      ParameterChoice.IsAsymptoticallyOptimal alphaP betaP)
    (h_betaP_discrep :
      Asymptotics.IsEquivalent Filter.atTop betaP
        (TikhonovDiscrepancy.betaDiscrep b c p σ))
    (h_standing :
      FilterRegularization.StandingAssumptions
        K S h_length fTrue c p b q d η
        (fun n ↦ Rtikh n (alphaDiscrep n)) alphaDiscrep)
    (h_tikhonov : TikhonovEstimation.IsTikhonovReconstructionFamily K S Rtikh)
    (h_alphaDiscrep :
      TikhonovDiscrepancy.IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_critical : p - q = -1) :
    Asymptotics.IsEquivalent Filter.atTop alphaP alphaDiscrep := by
  have h_alphaP_betaP :
      Asymptotics.IsEquivalent Filter.atTop alphaP betaP :=
    ParameterChoice.IsAsymptoticallyOptimal.isEquivalent h_alphaP
  have h_betaP_alphaDiscrep :
      Asymptotics.IsEquivalent Filter.atTop betaP alphaDiscrep :=
    predictiveBenchmark_isEquivalent_critical_discrepancyFamily
      K S h_length fTrue b c p q σ d η Rtikh betaP alphaDiscrep
      h_betaP_discrep h_standing h_tikhonov h_alphaDiscrep
      h_b h_c h_p h_q h_σ h_critical
  exact h_alphaP_betaP.trans h_betaP_alphaDiscrep

/-- Companion form of `isEquivalent_critical_discrepancyFamily`
using the raw `=Θ` asymptotic-rate owner. -/
theorem isTheta_critical_discrepancyFamily
    (h_alphaP :
      ParameterChoice.IsAsymptoticallyOptimal alphaP betaP)
    (h_betaP_discrep :
      Asymptotics.IsEquivalent Filter.atTop betaP
        (TikhonovDiscrepancy.betaDiscrep b c p σ))
    (h_standing :
      FilterRegularization.StandingAssumptions
        K S h_length fTrue c p b q d η
        (fun n ↦ Rtikh n (alphaDiscrep n)) alphaDiscrep)
    (h_tikhonov : TikhonovEstimation.IsTikhonovReconstructionFamily K S Rtikh)
    (h_alphaDiscrep :
      TikhonovDiscrepancy.IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_critical : p - q = -1) :
    alphaP =Θ[Filter.atTop] alphaDiscrep := by
  exact
    (isEquivalent_critical_discrepancyFamily
      K S h_length fTrue b c p q σ d η Rtikh betaP alphaP alphaDiscrep
      h_alphaP h_betaP_discrep h_standing h_tikhonov h_alphaDiscrep
      h_b h_c h_p h_q h_σ h_critical).isTheta

end

end TikhonovPredictiveRisk
