module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleJetCertificate
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleStationarityFromChart
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ScaleStationarityNeighborhood
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleJetCertificate
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleStationarityFromChart
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ScaleStationarityNeighborhood

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

/-!
# Uniform cubic bound for the transverse derivative of the low second-leg gradient factor

This leaf module assembles an explicit flat scale-chart certificate into the
source-side cubic estimate.  The chart construction remains a separate source
obligation, so this file does not reopen the large second-leg evaluator.
-/

/-- Infrastructure I.16a helper for Lemma 4.15: a flat scale-chart family
packages into the scalar second-scale stationarity certificate. -/
theorem lowGradientTransverseSecondScaleCertificate_of_flatScaleChart
    (hchart : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      HasLowGradientScaleFlatChart z.1 z.2) :
    LowGradientTransverseSecondScaleCertificate where
  scalar_second :=
    lowGradientTransverseFDerivFamily_scalar_secondScale_eventually_of_flatScaleChart hchart

/-- Infrastructure I.16a helper for Lemma 4.15: the flat-chart certificate
gives the eventual bundled second scale jet required by the Taylor estimate. -/
theorem lowGradientTransverseFDerivFamily_secondScaleJet_eventually_zero_of_flatScaleChart
    (hchart : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      HasLowGradientScaleFlatChart z.1 z.2) :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2 (lowGradientTransverseFDerivFamily z) 0 = 0 :=
  (lowGradientTransverseSecondScaleCertificate_of_flatScaleChart hchart).eventually_secondScaleJet

/-- Infrastructure I.16a bridge for Lemma 4.15: a flat scale-chart family
implies the uniform `O(ε³)` transverse derivative bound. -/
theorem lowGradientFactorTransverseFDeriv_norm_bound_of_flatScaleChart
    (hchart : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      HasLowGradientScaleFlatChart z.1 z.2) :
    ∃ C > 0, ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦ (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖
        ≤ C * ‖x.1 ^ (3 : ℕ)‖ :=
  lowGradientFactorTransverseFDeriv_norm_bound_of_secondScaleJet
    (lowGradientTransverseFDerivFamily_secondScaleJet_eventually_zero_of_flatScaleChart hchart)

end DFP.SecondLeg
