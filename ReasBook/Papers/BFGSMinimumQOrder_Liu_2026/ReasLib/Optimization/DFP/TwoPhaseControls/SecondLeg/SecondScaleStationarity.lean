module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ScaleQuadraticGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.PublicFactors
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.LowGradientIndependentRadiusBridge
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondGradientGermTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.Converse
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleTransverseTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ScaleComponentGerms
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleStationarityFromChart
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.PublicFactors
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.LowGradientIndependentRadiusBridge
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondGradientGermTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.Converse

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

open DFP.TwoLeg.Mixed

/-! The source calculation is represented by a small certificate.  In particular, the
factor substitution is not unfolded here: the eigenframe normalization is a large construction
whose stable interface is the eventual equality below. -/


/-- Helper for Infrastructure I.16a and Lemma 4.15: a factor-transport certificate records the
eventual independent-radius representative and the regularity needed to read its quadratic jet. -/
structure LowGradientIndependentRadiusScaleCertificate (p h : ℝ) : Prop where
  spectral_transport : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
    DFP.FirstLeg.spectralFactors ε p h =
      independentRadiusFirstSpectral ((ε, p, h), ε ^ 2)
  gradient_transport : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
    DFP.FirstLeg.gradientFactors ε p h =
      independentRadiusFirstGradient ((ε, p, h), ε ^ 2)
  independent_germ : HasQuadraticGerm
    (fun ε : ℝ ↦
      (independentRadiusSecondGradient ((ε, p, h), ε ^ 2)).1)
    1 0 0
  regularity : ContDiffAt ℝ 3
    (fun ε : ℝ ↦ lowGradientFactor (ε, p, h)) 0

/-- Helper for Infrastructure I.16a and Lemma 4.15: the certificate forces the pure second
signed-scale jet of the low second-leg factor to vanish. -/
theorem LowGradientIndependentRadiusScaleCertificate.pureSecondScaleJet
    {p h : ℝ}
    (certificate : LowGradientIndependentRadiusScaleCertificate p h) :
    iteratedFDeriv ℝ 2
      (fun ε : ℝ ↦ lowGradientFactor (ε, p, h)) 0 = 0 := by
  have hcontinuous : ContinuousAt
      (fun ε : ℝ ↦ lowGradientFactor (ε, p, h)) 0 :=
    certificate.regularity.continuousAt
  have hgerm := lowGradientFactor_quadraticGerm_of_eventualFactorTransport
    p h 1 0 0 certificate.spectral_transport certificate.gradient_transport
    certificate.independent_germ hcontinuous
  have hsecond := HasQuadraticGerm.iteratedDeriv_two_eq_of_contDiffAt
    hgerm certificate.regularity
  have hsecondZero : iteratedDeriv 2
      (fun ε : ℝ ↦ lowGradientFactor (ε, p, h)) 0 = 0 := by
    simpa using hsecond
  apply ContinuousMultilinearMap.ext_ring
  simpa only [iteratedDeriv_eq_iteratedFDeriv, zero_apply] using hsecondZero

/-- Helper for Infrastructure I.16a and Lemma 4.15: an eventual family of factor-transport
certificates yields the scalar stationarity input for the transverse cubic estimate. -/
theorem
    lowGradientTransverseFDerivFamily_scalar_secondScale_eventually_of_independentRadiusCertificate
    (hcertificate : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      LowGradientIndependentRadiusScaleCertificate z.1 z.2) :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ), ∀ w : ℝ × ℝ,
      HasDerivAt
        (fun ε : ℝ ↦ deriv
          (fun t : ℝ ↦
            (lowGradientTransverseFDerivFamily z t) w) ε)
        0 0 := by
  have hscale : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2
        (fun ε : ℝ ↦ lowGradientFactor (ε, z)) 0 = 0 := by
    filter_upwards [hcertificate] with z hz
    exact hz.pureSecondScaleJet
  exact lowGradientTransverseFDerivFamily_scalar_secondScale_eventually_of_pureSecondScaleJet
    hscale

/-- Infrastructure I.16a (Lemma 4.15, Claim 2 crux): via the FirstLeg component germ tower, the
pure second signed-scale iterated derivative of the low second-leg gradient factor vanishes
throughout a neighborhood of the positive transverse base point `(2, 1)`. -/
theorem lowGradientFactor_scale_iteratedFDeriv_two_eventually_eq_zero :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2
        (fun ε : ℝ ↦ lowGradientFactor (ε, z)) 0 = 0 := by
  -- eventual side conditions from continuity of the coordinate projections
  have hpos : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ), (0 : ℝ) < z.2 := by
    have hsnd : ContinuousAt (fun z : ℝ × ℝ ↦ z.2) ((2, 1) : ℝ × ℝ) := by fun_prop
    have hbase : (0 : ℝ) < 1 := by norm_num
    exact hsnd.eventually (eventually_gt_nhds hbase)
  have hne : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ), (z.1 + 1) / 3 ≠ 0 := by
    have hval : ContinuousAt (fun z : ℝ × ℝ ↦ (z.1 + 1) / 3) ((2, 1) : ℝ × ℝ) := by
      fun_prop
    have hbase : (((2 : ℝ) + 1) / 3) ≠ 0 := by norm_num
    have hnhds : ∀ᶠ y : ℝ in 𝓝 (((2 : ℝ) + 1) / 3), y ≠ 0 :=
      eventually_ne_nhds hbase
    exact hval.eventually hnhds
  -- eventual analyticity of the slice, giving the required `C³` regularity
  have hanalytic : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      AnalyticAt ℝ lowGradientFactor ((0 : ℝ), z) := by
    have hslice : ContinuousAt (fun z : ℝ × ℝ ↦ ((0 : ℝ), z)) ((2, 1) : ℝ × ℝ) := by
      fun_prop
    exact hslice.eventually lowGradientFactor_analyticAt.eventually_analyticAt
  filter_upwards [hpos, hne, hanalytic] with z hz2 hzne hzf
  have hregular : ContDiffAt ℝ 3 (fun r : ℝ ↦ lowGradientFactor (r, z.1, z.2)) 0 :=
    lowGradientFactor_contDiffAt_scale_of_analytic hzf
  have hsecond : iteratedDeriv 2
      (fun r : ℝ ↦ lowGradientFactor (r, z.1, z.2)) 0 = 0 :=
    lowGradientFactor_scale_iteratedDeriv_two_eq_zero z.1 z.2 hz2 hzne hregular
  exact DFP.Calculus.iteratedFDeriv_two_eq_zero_of_iteratedDeriv_two_eq_zero hsecond

/-- A0 (Lemma 4.15, Claim 2 crux): the pure second signed-scale derivative of the low second-leg
gradient factor vanishes throughout a neighborhood of the positive transverse base point. -/
theorem lowGradientFactor_scale_secondDeriv_eventually_eq_zero :
    ∀ᶠ z : ℝ × ℝ in nhds ((2, 1) : ℝ × ℝ),
      iteratedDeriv 2 (fun r : ℝ ↦ lowGradientFactor (r, z.1, z.2)) 0 = 0 := by
  have hpos : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ), (0 : ℝ) < z.2 := by
    have hsnd : ContinuousAt (fun z : ℝ × ℝ ↦ z.2) ((2, 1) : ℝ × ℝ) := by fun_prop
    have hbase : (0 : ℝ) < 1 := by norm_num
    exact hsnd.eventually (eventually_gt_nhds hbase)
  have hne : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ), (z.1 + 1) / 3 ≠ 0 := by
    have hval : ContinuousAt (fun z : ℝ × ℝ ↦ (z.1 + 1) / 3) ((2, 1) : ℝ × ℝ) := by
      fun_prop
    have hbase : (((2 : ℝ) + 1) / 3) ≠ 0 := by norm_num
    have hnhds : ∀ᶠ y : ℝ in 𝓝 (((2 : ℝ) + 1) / 3), y ≠ 0 :=
      eventually_ne_nhds hbase
    exact hval.eventually hnhds
  have hanalytic : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      AnalyticAt ℝ lowGradientFactor ((0 : ℝ), z) := by
    have hslice : ContinuousAt (fun z : ℝ × ℝ ↦ ((0 : ℝ), z)) ((2, 1) : ℝ × ℝ) := by
      fun_prop
    exact hslice.eventually lowGradientFactor_analyticAt.eventually_analyticAt
  filter_upwards [hpos, hne, hanalytic] with z hz2 hzne hzf
  have hregular : ContDiffAt ℝ 3 (fun r : ℝ ↦ lowGradientFactor (r, z.1, z.2)) 0 :=
    lowGradientFactor_contDiffAt_scale_of_analytic hzf
  exact lowGradientFactor_scale_iteratedDeriv_two_eq_zero z.1 z.2 hz2 hzne hregular

/-- A3 (Lemma 4.15, Claim 2 crux): the scalar second-scale stationarity of the transverse
Fréchet-derivative family, i.e. the `scalar_second` field of the transverse second-scale
certificate. -/
theorem lowGradientTransverseFDerivFamily_scalar_secondScale_eventually :
    ∀ᶠ z : ℝ × ℝ in nhds ((2, 1) : ℝ × ℝ), ∀ w : ℝ × ℝ,
      HasDerivAt
        (fun ε : ℝ ↦ deriv
          (fun t : ℝ ↦ (lowGradientTransverseFDerivFamily z t) w) ε) 0 0 :=
  lowGradientTransverseFDerivFamily_scalar_secondScale_eventually_of_pureSecondScaleJet
    lowGradientFactor_scale_iteratedFDeriv_two_eventually_eq_zero

/-!
# Second scale stationarity of the low second-leg gradient factor (Lemma 4.15 crux)

This leaf module supplies the analytic crux `𝒢₂ = 1 + O(ε³)` for Claim 2 of Lemma 4.15: the
second scale derivative of the low second-leg gradient factor vanishes throughout a neighborhood
of the positive transverse base point, and the corresponding scalar second-scale stationarity of
the transverse Fréchet-derivative family.  It is intentionally kept out of `SecondLeg.lean` so the
certificate chain that imports `SecondLeg.lean` can import this module without a cycle.
-/

end DFP.SecondLeg
