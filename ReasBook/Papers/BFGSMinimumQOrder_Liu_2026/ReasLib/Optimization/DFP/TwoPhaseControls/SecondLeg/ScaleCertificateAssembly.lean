module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleStationarity
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondGradientScaleSubstitution
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleStationarity
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondGradientScaleSubstitution

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

open DFP.TwoLeg.Mixed

/-- Infrastructure I.16a: transport of the first factors and scale regularity assemble the
independent-radius certificate, with its quadratic germ supplied by the analytic substitution. -/
theorem lowGradientIndependentRadiusScaleCertificate_of_transports
    {p h : ℝ}
    (hSpectral : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      DFP.FirstLeg.spectralFactors ε p h =
        independentRadiusFirstSpectral ((ε, p, h), ε ^ 2))
    (hGradient : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      DFP.FirstLeg.gradientFactors ε p h =
        independentRadiusFirstGradient ((ε, p, h), ε ^ 2))
    (hregular : ContDiffAt ℝ 3
      (fun ε : ℝ ↦ lowGradientFactor (ε, p, h)) 0) :
    LowGradientIndependentRadiusScaleCertificate p h := by
  exact
    { spectral_transport := hSpectral
      gradient_transport := hGradient
      independent_germ := independentRadiusSecondGradientLow_scale_quadraticGerm p h
      regularity := hregular }

/-- Infrastructure I.16a: an eventual family of factor transports and scale regularity yields
the scalar second-scale stationarity used by the transverse cubic estimate. -/
theorem lowGradientTransverseFDerivFamily_scalar_secondScale_eventually_of_transports
    (hSpectral : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
        DFP.FirstLeg.spectralFactors ε z.1 z.2 =
          independentRadiusFirstSpectral ((ε, z.1, z.2), ε ^ 2))
    (hGradient : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
        DFP.FirstLeg.gradientFactors ε z.1 z.2 =
          independentRadiusFirstGradient ((ε, z.1, z.2), ε ^ 2))
    (hregular : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      ContDiffAt ℝ 3
        (fun ε : ℝ ↦ lowGradientFactor (ε, z.1, z.2)) 0) :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ), ∀ w : ℝ × ℝ,
      HasDerivAt
        (fun ε : ℝ ↦ deriv
          (fun t : ℝ ↦ (lowGradientTransverseFDerivFamily z t) w) ε)
        0 0 := by
  have hcertificate : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      LowGradientIndependentRadiusScaleCertificate z.1 z.2 := by
    filter_upwards [hSpectral, hGradient, hregular] with z hzSpectral hzGradient hzregular
    exact lowGradientIndependentRadiusScaleCertificate_of_transports
      hzSpectral hzGradient hzregular
  exact
    lowGradientTransverseFDerivFamily_scalar_secondScale_eventually_of_independentRadiusCertificate
      hcertificate

end DFP.SecondLeg
