module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeFrameTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondGradientGermTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeFrameTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondGradientGermTransport

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-- Appendix Lemma A.6: a pathwise signed-frame certificate transports the physical
amplitude to the explicit three-term independent-radius quadratic germ. -/
theorem physicalAmplitudeTruncatedGerm_of_framePathCertificate
    {K : Set (ℝ × ℝ × ℝ)}
    (certificate : PhysicalAmplitudeFramePathCertificate K) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio) K 3
      (fun n θ ↦
        (![1, 0,
          (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) := by
  exact truncatedGerm_of_uncurryEq_secondGradientLow
    certificate.uncurry_eventuallyEq_secondGradientLow

end DFP.TwoLeg.Mixed
