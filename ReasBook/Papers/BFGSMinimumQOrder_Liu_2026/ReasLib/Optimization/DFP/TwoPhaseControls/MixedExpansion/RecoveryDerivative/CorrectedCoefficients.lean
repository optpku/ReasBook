module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RecoveryDerivative
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RecoveryDerivative
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This companion records the coefficient transport after correcting the sign in the first-leg
gradient jet.  It is deliberately conditional on the two component jets: the raw second-leg
calculation remains owned by the mixed-expansion target.
-/

/-- Corrected second-factor component jets determine the
    recovery derivative with radius coefficient `b * (6 * J + 5 * P - 276) / 18` and
    shape coefficient `b * (6 * J - P + 300) / 9`. -/
theorem independentRadiusRecoveryFactors_hasDerivAt_of_correctedComponentJets
    (θ : ℝ × ℝ × ℝ)
    (hS : HasDerivAt
      (fun r : ℝ ↦ independentRadiusSecondSpectral (θ, r))
      (θ.1 * (2 * θ.2.2 + θ.2.1 - 12), 8 * θ.1) 0)
    (hG : HasDerivAt
      (fun r : ℝ ↦ independentRadiusSecondGradient (θ, r))
      (0, 4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 6) / 9) 0) :
    HasDerivAt (fun r ↦ independentRadiusRecoveryFactors (θ, r))
      (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 276) / 18,
        (θ.1 * (6 * θ.2.2 - θ.2.1 + 300) / 9, 8 * θ.1)) 0 := by
  have hS₀ : (fun r : ℝ ↦ independentRadiusSecondSpectral (θ, r)) 0 = (2, 1) :=
    independentRadiusSecondSpectral_zero θ
  have hG₀ : (fun r : ℝ ↦ independentRadiusSecondGradient (θ, r)) 0 = (1, 2) :=
    independentRadiusSecondGradient_zero θ
  have hgeneric := recoveryFactors_hasDerivAt_of_componentJets
    (fun r : ℝ ↦ independentRadiusSecondSpectral (θ, r))
    (fun r : ℝ ↦ independentRadiusSecondGradient (θ, r))
    (θ.1 * (2 * θ.2.2 + θ.2.1 - 12)) (8 * θ.1) 0
    (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 6) / 9)
    hS.fst hS.snd hG.fst hG.snd hS₀ hG₀
  have hrepresentation :
      (fun r : ℝ ↦ independentRadiusRecoveryFactors (θ, r)) =
        (fun r : ℝ ↦ AnalyticRecovery.recoveryFactors
          (fun t : ℝ ↦ independentRadiusSecondSpectral (θ, t))
          (fun t : ℝ ↦ independentRadiusSecondGradient (θ, t)) r) := by
    funext r
    rfl
  rw [hrepresentation]
  convert hgeneric using 1
  ring_nf

end DFP.TwoLeg.Mixed
