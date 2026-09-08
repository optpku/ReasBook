module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.Converse
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeQuadraticTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusRecoveryGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.Converse
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeQuadraticTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusRecoveryGerm

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/- This file is the concrete projection adapter between the independent-radius
   recovered factor and a physical amplitude representative. -/

/-- Helper for Appendix Lemma A.6: a physical amplitude equal near zero to the
    recovered independent-radius factor carries its concrete quadratic germ. -/
theorem physicalAmplitudeQuadraticGerm_of_recoveredRadius
    (θ : ℝ × ℝ × ℝ) {amplitude : ℝ → ℝ}
    (hphysical : amplitude =ᶠ[𝓝 0]
      (fun r ↦
        (independentRadiusSecondSpectral (θ, r)).1 *
          (independentRadiusSecondGradient (θ, r)).1 /
          ((independentRadiusSecondSpectral (θ, r)).2 *
            (independentRadiusSecondGradient (θ, r)).2)))
    (hamplitude : ContinuousAt amplitude 0) :
    HasQuadraticGerm amplitude
      1 (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18)
      (-(36 * θ.2.2 ^ 2 * θ.1 ^ 2 - 21 * θ.2.2 * θ.2.1 * θ.1 ^ 2 +
          3636 * θ.2.2 * θ.1 ^ 2 + 4 * θ.2.1 ^ 2 * θ.1 ^ 2 +
          1158 * θ.2.1 * θ.1 ^ 2 - 450 * θ.1 ^ 2 - 486) / 162) := by
  have hfactor := independentRadiusRecoveryFactorQuadraticGerm θ
  exact hfactor.congr_of_eventuallyEq hphysical.symm hamplitude

/-- Helper for Appendix Lemma A.6: the same recovered-radius projection gives the
    explicit third-order remainder after subtracting its quadratic model. -/
theorem physicalAmplitudeRemainder_of_recoveredRadius
    (θ : ℝ × ℝ × ℝ) {amplitude : ℝ → ℝ}
    (hphysical : amplitude =ᶠ[𝓝 0]
      (fun r ↦
        (independentRadiusSecondSpectral (θ, r)).1 *
          (independentRadiusSecondGradient (θ, r)).1 /
          ((independentRadiusSecondSpectral (θ, r)).2 *
            (independentRadiusSecondGradient (θ, r)).2)))
    (hamplitude : ContinuousAt amplitude 0) :
    EqModPow 3
      (fun r ↦ amplitude r -
        quadraticModel 1 (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18)
          (-(36 * θ.2.2 ^ 2 * θ.1 ^ 2 - 21 * θ.2.2 * θ.2.1 * θ.1 ^ 2 +
            3636 * θ.2.2 * θ.1 ^ 2 + 4 * θ.2.1 ^ 2 * θ.1 ^ 2 +
            1158 * θ.2.1 * θ.1 ^ 2 - 450 * θ.1 ^ 2 - 486) / 162) r)
      (fun _ ↦ 0) := by
  have hgerm := physicalAmplitudeQuadraticGerm_of_recoveredRadius
    θ hphysical hamplitude
  exact hgerm.to_quadraticRemainder

end DFP.TwoLeg.Mixed
