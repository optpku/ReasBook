module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ResidualDataChartGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeQuadraticTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm

public section

noncomputable section

namespace DFP.SecondLeg

open DFP.TwoLeg.Mixed
open Filter
open scoped Topology

/-- Helper for Infrastructure I.16a: a transport of the first spectral and gradient factors
identifies the removable low factor with the independent-radius second gradient factor. -/
theorem lowGradientFactor_eq_independentRadiusSecondGradient_of_factorTransport
    (ε p h : ℝ)
    (hSpectral :
      DFP.FirstLeg.spectralFactors ε p h =
        independentRadiusFirstSpectral ((ε, p, h), ε ^ 2))
    (hGradient :
      DFP.FirstLeg.gradientFactors ε p h =
        independentRadiusFirstGradient ((ε, p, h), ε ^ 2)) :
    lowGradientFactor (ε, p, h) =
      (DFP.TwoLeg.Mixed.independentRadiusSecondGradient ((ε, p, h), ε ^ 2)).1 := by
  rw [lowGradientFactor_eq_independentSecondGradientFactors]
  have hdef :
      DFP.TwoLeg.Mixed.independentRadiusSecondGradient ((ε, p, h), ε ^ 2) =
        independentSecondGradientFactors ε (ε ^ 2)
          (independentRadiusFirstSpectral ((ε, p, h), ε ^ 2)).1
          (independentRadiusFirstSpectral ((ε, p, h), ε ^ 2)).2
          (independentRadiusFirstGradient ((ε, p, h), ε ^ 2)).1
          (independentRadiusFirstGradient ((ε, p, h), ε ^ 2)).2 := by
    rw [DFP.TwoLeg.Mixed.independentRadiusSecondGradient.eq_1]
  rw [hdef, ← hSpectral, ← hGradient]

/-- Helper for Infrastructure I.16a: eventual first-factor transport transfers an independent-
radius quadratic germ to the removable low-gradient path. -/
theorem lowGradientFactor_quadraticGerm_of_eventualFactorTransport
    (p h a₀ a₁ a₂ : ℝ)
    (hSpectral : ∀ᶠ ε in 𝓝 (0 : ℝ),
      DFP.FirstLeg.spectralFactors ε p h =
        independentRadiusFirstSpectral ((ε, p, h), ε ^ 2))
    (hGradient : ∀ᶠ ε in 𝓝 (0 : ℝ),
      DFP.FirstLeg.gradientFactors ε p h =
        independentRadiusFirstGradient ((ε, p, h), ε ^ 2))
    (hIndependentGerm : HasQuadraticGerm
      (fun ε : ℝ ↦
        (DFP.TwoLeg.Mixed.independentRadiusSecondGradient ((ε, p, h), ε ^ 2)).1)
      a₀ a₁ a₂)
    (hLowContinuous : ContinuousAt (fun ε : ℝ ↦ lowGradientFactor (ε, p, h)) 0) :
    HasQuadraticGerm (fun ε : ℝ ↦ lowGradientFactor (ε, p, h)) a₀ a₁ a₂ := by
  have htransport : ∀ᶠ ε in 𝓝 (0 : ℝ),
      lowGradientFactor (ε, p, h) =
        (DFP.TwoLeg.Mixed.independentRadiusSecondGradient ((ε, p, h), ε ^ 2)).1 := by
    filter_upwards [hSpectral, hGradient] with ε hεSpectral hεGradient
    exact lowGradientFactor_eq_independentRadiusSecondGradient_of_factorTransport
      ε p h hεSpectral hεGradient
  exact hIndependentGerm.congr_of_eventuallyEq (Filter.EventuallyEq.symm htransport)
    hLowContinuous

end DFP.SecondLeg
