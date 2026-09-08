module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ResidualDataChartGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleTransverseTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ResidualDataChartGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleTransverseTransport

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.Calculus

/-- Infrastructure I.16a: a zero scalar second iterated derivative is equivalent to a
zero order-two Frechet jet for a real scalar path. -/
theorem iteratedFDeriv_two_eq_zero_of_iteratedDeriv_two_eq_zero
    {f : ℝ → ℝ} (hsecond : iteratedDeriv 2 f 0 = 0) :
    iteratedFDeriv ℝ 2 f 0 = 0 := by
  apply ContinuousMultilinearMap.ext_ring
  simpa only [iteratedDeriv_eq_iteratedFDeriv, zero_apply] using hsecond

end DFP.Calculus

namespace DFP.SecondLeg

/-- Infrastructure I.16a: a flat scale-chart certificate packages the component germs and
the vanishing quadratic coefficient of the normalized low-gradient coordinate. -/
structure LowGradientScaleFlatChartCertificate (p h : ℝ) where
  radius : ℝ → ℝ
  metricA : ℝ → ℝ
  metricC : ℝ → ℝ
  metricD : ℝ → ℝ
  gradientQ : ℝ → ℝ
  gradientV : ℝ → ℝ
  a₀ : ℝ
  a₁ : ℝ
  a₂ : ℝ
  c₀ : ℝ
  c₁ : ℝ
  c₂ : ℝ
  d₁ : ℝ
  d₂ : ℝ
  q₁ : ℝ
  q₂ : ℝ
  v₀ : ℝ
  v₁ : ℝ
  v₂ : ℝ
  chart : LowGradientScaleChartCertificate p h radius metricA metricC metricD
    gradientQ gradientV a₀ a₁ a₂ c₀ c₁ c₂ d₁ d₂ q₁ q₂ v₀ v₁ v₂
  q₂_eq_zero : q₂ = 0

/-- Infrastructure I.16a: the proposition that a flat scale chart exists at a transverse
parameter, kept separate from the data-bearing certificate for use under filters. -/
def HasLowGradientScaleFlatChart (p h : ℝ) : Prop :=
  Nonempty (LowGradientScaleFlatChartCertificate p h)

/-- Infrastructure I.16a: analyticity of the low-gradient factor supplies the `C³` regularity
of its signed-scale slice required by a flat chart certificate. -/
theorem lowGradientFactor_contDiffAt_scale_of_analytic
    {p h : ℝ}
    (hf : AnalyticAt ℝ lowGradientFactor ((0 : ℝ), p, h)) :
    ContDiffAt ℝ 3 (fun r : ℝ ↦ lowGradientFactor (r, p, h)) 0 := by
  have hpath : ContDiffAt ℝ 3
      (fun r : ℝ ↦ ((r, p, h) : ℝ × ℝ × ℝ)) 0 := by
    fun_prop
  have hcomp := (hf.contDiffAt (n := 3)).comp 0 hpath
  simpa only [Function.comp_def, lowGradientFactor] using hcomp

/-- Infrastructure I.16a: the flat chart's vanishing quadratic coefficient gives the pure
second signed-scale jet of the low-gradient factor. -/
theorem LowGradientScaleFlatChartCertificate.pureSecondScaleJet
    {p h : ℝ}
    (certificate : LowGradientScaleFlatChartCertificate p h)
    (hf : AnalyticAt ℝ lowGradientFactor ((0 : ℝ), p, h)) :
    iteratedFDeriv ℝ 2
      (fun r : ℝ ↦ lowGradientFactor (r, p, h)) 0 = 0 := by
  have hregular := lowGradientFactor_contDiffAt_scale_of_analytic hf
  have hsecond :=
    lowGradientFactor_scale_iteratedDeriv_two_eq_zero_of_scaleChartCertificate
      certificate.chart hregular certificate.q₂_eq_zero
  exact DFP.Calculus.iteratedFDeriv_two_eq_zero_of_iteratedDeriv_two_eq_zero hsecond

/-- Infrastructure I.16a: an eventual family of flat scale charts transports to the scalar
second-scale stationarity certificate consumed by the transverse cubic estimate. -/
theorem lowGradientTransverseFDerivFamily_scalar_secondScale_eventually_of_flatScaleChart
    (hchart : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      HasLowGradientScaleFlatChart z.1 z.2) :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ), ∀ w : ℝ × ℝ,
      HasDerivAt
        (fun ε : ℝ ↦ deriv
          (fun t : ℝ ↦
            (lowGradientTransverseFDerivFamily z t) w) ε)
        0 0 := by
  have hanalytic : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      AnalyticAt ℝ lowGradientFactor ((0 : ℝ), z) := by
    have hslice : ContinuousAt
        (fun z : ℝ × ℝ ↦ ((0 : ℝ), z))
        ((2, 1) : ℝ × ℝ) := by
      fun_prop
    exact hslice.eventually lowGradientFactor_analyticAt.eventually_analyticAt
  have hchartLocal : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      ∀ᶠ y : ℝ × ℝ in 𝓝 z,
        HasLowGradientScaleFlatChart y.1 y.2 :=
    eventually_eventually_nhds.2 hchart
  have hanalyticLocal : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      ∀ᶠ y : ℝ × ℝ in 𝓝 z,
        AnalyticAt ℝ lowGradientFactor ((0 : ℝ), y) :=
    eventually_eventually_nhds.2 hanalytic
  filter_upwards [hchartLocal, hanalyticLocal, hanalytic] with z hz hza hzf
  have hscale : ∀ᶠ y : ℝ × ℝ in 𝓝 z,
      iteratedFDeriv ℝ 2
        (fun ε : ℝ ↦ lowGradientFactor (ε, y)) 0 = 0 := by
    filter_upwards [hz, hza] with y hy hfy
    obtain ⟨hy⟩ := hy
    exact hy.pureSecondScaleJet hfy
  exact DFP.Calculus.hasDerivAt_deriv_partialFDeriv_of_eventually_scaleSecondJet_zero
    lowGradientFactor z hzf hscale

end DFP.SecondLeg
