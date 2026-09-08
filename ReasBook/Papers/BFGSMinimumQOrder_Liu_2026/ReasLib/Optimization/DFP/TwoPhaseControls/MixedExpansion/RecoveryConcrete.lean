module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RecoveryDerivative
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RecoveryDerivative

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-- The concrete independent-radius recovery triple is
    represented pointwise by the analytic quotient adapter. -/
theorem independentRadiusRecoveryFactors_eq_analyticRecovery (θ : ℝ × ℝ × ℝ) :
    (fun r : ℝ ↦ independentRadiusRecoveryFactors (θ, r)) =
      AnalyticRecovery.recoveryFactors
        (fun r : ℝ ↦ independentRadiusSecondSpectral (θ, r))
        (fun r : ℝ ↦ independentRadiusSecondGradient (θ, r)) := by
  funext r
  unfold independentRadiusRecoveryFactors AnalyticRecovery.recoveryFactors
  rfl

/-- Corrected component jets at the canonical base give
    the recovered first-radius derivative, with the squared shape denominator accounted
    for explicitly. -/
theorem independentRadiusRecoveryFactors_hasDerivAt_corrected
    (θ : ℝ × ℝ × ℝ) (s₁ s₂ g₁ g₂ : ℝ)
    (hS : HasDerivAt
      (fun r : ℝ ↦ independentRadiusSecondSpectral (θ, r)) (s₁, s₂) 0)
    (hG : HasDerivAt
      (fun r : ℝ ↦ independentRadiusSecondGradient (θ, r)) (g₁, g₂) 0) :
    HasDerivAt (fun r : ℝ ↦ independentRadiusRecoveryFactors (θ, r))
      ((s₁ + 2 * g₁ - 2 * s₂ - g₂) / 2,
        (2 * s₂ + 2 * g₂ - s₁ - 4 * g₁, s₂)) 0 := by
  have hS0 : (fun r : ℝ ↦ independentRadiusSecondSpectral (θ, r)) 0 =
      (2, 1) := independentRadiusSecondSpectral_zero θ
  have hG0 : (fun r : ℝ ↦ independentRadiusSecondGradient (θ, r)) 0 =
      (1, 2) := independentRadiusSecondGradient_zero θ
  have hrec := recoveryFactors_hasDerivAt_of_componentJets
    (fun r : ℝ ↦ independentRadiusSecondSpectral (θ, r))
    (fun r : ℝ ↦ independentRadiusSecondGradient (θ, r))
    s₁ s₂ g₁ g₂ hS.fst hS.snd hG.fst hG.snd hS0 hG0
  rw [independentRadiusRecoveryFactors_eq_analyticRecovery θ]
  exact hrec

end DFP.TwoLeg.Mixed
