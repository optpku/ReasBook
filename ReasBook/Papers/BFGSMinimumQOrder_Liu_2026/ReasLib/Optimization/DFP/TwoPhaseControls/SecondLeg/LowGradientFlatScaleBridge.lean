module

public import
  ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.FirstScaleFlatGerm
public import
  ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicJet
public import
  ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeQuadraticTransport
import all
  ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.FirstScaleFlatGerm
import all
  ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicJet
import all
  ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeQuadraticTransport

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

open DFP.TwoLeg.Mixed

/-- Infrastructure I.16a: an explicit FirstLeg-to-SecondLeg low-coordinate transport
transfers the flat pure-scale germ to the second-leg low-gradient factor. -/
theorem lowGradientFactor_fixedParameter_quadraticGerm_of_firstLegTransport
    (p h : ℝ)
    (htransport : ∀ᶠ ε in 𝓝 (0 : ℝ),
      lowGradientFactor (ε, p, h) = (DFP.FirstLeg.gradientFactors ε p h).1)
    (hcontinuous : ContinuousAt
      (fun ε : ℝ ↦ lowGradientFactor (ε, p, h)) 0) :
    HasQuadraticGerm
      (fun ε : ℝ ↦ lowGradientFactor (ε, p, h))
      1 0 0 := by
  have hfirst := DFP.FirstLeg.gradientFactors_low_flat p h
  have hfg :
      (fun ε : ℝ ↦ (DFP.FirstLeg.gradientFactors ε p h).1) =ᶠ[𝓝 (0 : ℝ)]
        (fun ε : ℝ ↦ lowGradientFactor (ε, p, h)) := by
    filter_upwards [htransport] with ε hε
    exact hε.symm
  exact hfirst.congr_of_eventuallyEq hfg hcontinuous

end DFP.SecondLeg
