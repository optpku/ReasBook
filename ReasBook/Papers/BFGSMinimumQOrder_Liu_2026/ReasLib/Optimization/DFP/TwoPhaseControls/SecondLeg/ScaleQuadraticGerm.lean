module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondOrderJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicJet

public section

noncomputable section

namespace DFP.SecondLeg

open DFP.TwoLeg.Mixed

/-!
# Scale quadratic germ interface for the second-leg low factor

The source calculation identifies the low gradient factor with a normalized two-by-two chart.
This file keeps that identification as an explicit certificate and delegates the quadratic
calculation to the reusable `IndependentRadiusSecondOrderJet` infrastructure.
-/

/-- Helper for Lemma 4.15: a pointwise chart factorization transfers component quadratic germs
to the signed-scale path of the low second-leg gradient factor. -/
theorem lowGradientFactor_scale_quadraticGerm_of_chartFactorization
    (p h : ℝ)
    {radius metricA metricC metricD gradientQ gradientU : ℝ → ℝ}
    {a₂ c₁ c₂ d₁ d₂ q₁ q₂ u₁ u₂ : ℝ}
    (hradius : HasQuadraticGerm radius 0 1 0)
    (hmetricA : HasQuadraticGerm metricA 0 0 a₂)
    (hmetricC : HasQuadraticGerm metricC 0 c₁ c₂)
    (hmetricD : HasQuadraticGerm metricD 1 d₁ d₂)
    (hgradientQ : HasQuadraticGerm gradientQ 1 q₁ q₂)
    (hgradientU : HasQuadraticGerm gradientU 0 u₁ u₂)
    (hpath : ∀ r : ℝ,
      lowGradientChartPath radius metricA metricC metricD gradientQ gradientU r =
        lowGradientFactor (r, p, h)) :
    HasQuadraticGerm (fun r : ℝ => lowGradientFactor (r, p, h))
      1 q₁ (q₂ - c₁ ^ 2 / 2) := by
  have hchart := lowGradientChartPath_quadraticGerm_of_componentGerms
    hradius hmetricA hmetricC hmetricD hgradientQ hgradientU
  apply hchart.congrFunction
  intro r
  exact (hpath r).symm

/-- Helper for Lemma 4.15: when the chart has no linear or quadratic correction in its gradient
coordinate, the low factor has the constant quadratic germ required by the cubic estimate. -/
theorem lowGradientFactor_scale_quadraticGerm_of_flat_chart
    (p h : ℝ)
    {radius metricA metricC metricD gradientQ gradientU : ℝ → ℝ}
    {a₂ d₁ d₂ u₁ u₂ : ℝ}
    (hradius : HasQuadraticGerm radius 0 1 0)
    (hmetricA : HasQuadraticGerm metricA 0 0 a₂)
    (hmetricC : HasQuadraticGerm metricC 0 0 0)
    (hmetricD : HasQuadraticGerm metricD 1 d₁ d₂)
    (hgradientQ : HasQuadraticGerm gradientQ 1 0 0)
    (hgradientU : HasQuadraticGerm gradientU 0 u₁ u₂)
    (hpath : ∀ r : ℝ,
      lowGradientChartPath radius metricA metricC metricD gradientQ gradientU r =
        lowGradientFactor (r, p, h)) :
    HasQuadraticGerm (fun r : ℝ => lowGradientFactor (r, p, h)) 1 0 0 := by
  have hflat := lowGradientFactor_scale_quadraticGerm_of_chartFactorization
    p h hradius hmetricA hmetricC hmetricD hgradientQ hgradientU hpath
  have hzero : (0 : ℝ) - 0 ^ 2 / 2 = 0 := by
    norm_num
  exact hflat.congrCoefficients rfl rfl hzero

/-- Helper for Lemma 4.15: a regular low-factor chart converts the quadratic germ into the
second iterated scale derivative used by Taylor-jet estimates. -/
theorem lowGradientFactor_scale_iteratedDeriv_two_eq_of_chartFactorization
    (p h : ℝ)
    {radius metricA metricC metricD gradientQ gradientU : ℝ → ℝ}
    {a₂ c₁ c₂ d₁ d₂ q₁ q₂ u₁ u₂ : ℝ}
    (hradius : HasQuadraticGerm radius 0 1 0)
    (hmetricA : HasQuadraticGerm metricA 0 0 a₂)
    (hmetricC : HasQuadraticGerm metricC 0 c₁ c₂)
    (hmetricD : HasQuadraticGerm metricD 1 d₁ d₂)
    (hgradientQ : HasQuadraticGerm gradientQ 1 q₁ q₂)
    (hgradientU : HasQuadraticGerm gradientU 0 u₁ u₂)
    (hpath : ∀ r : ℝ,
      lowGradientChartPath radius metricA metricC metricD gradientQ gradientU r =
        lowGradientFactor (r, p, h))
    (hregular : ContDiffAt ℝ 3
      (fun r : ℝ => lowGradientFactor (r, p, h)) 0) :
    iteratedDeriv 2 (fun r : ℝ => lowGradientFactor (r, p, h)) 0 =
      2 * (q₂ - c₁ ^ 2 / 2) := by
  have hgerm := lowGradientFactor_scale_quadraticGerm_of_chartFactorization
    p h hradius hmetricA hmetricC hmetricD hgradientQ hgradientU hpath
  exact HasQuadraticGerm.iteratedDeriv_two_eq_of_contDiffAt hgerm hregular

/-- Helper for Lemma 4.15: the flat chart certificate forces the second scale derivative of the
low factor to vanish. -/
theorem lowGradientFactor_scale_iteratedDeriv_two_eq_zero_of_flat_chart
    (p h : ℝ)
    {radius metricA metricC metricD gradientQ gradientU : ℝ → ℝ}
    {a₂ d₁ d₂ u₁ u₂ : ℝ}
    (hradius : HasQuadraticGerm radius 0 1 0)
    (hmetricA : HasQuadraticGerm metricA 0 0 a₂)
    (hmetricC : HasQuadraticGerm metricC 0 0 0)
    (hmetricD : HasQuadraticGerm metricD 1 d₁ d₂)
    (hgradientQ : HasQuadraticGerm gradientQ 1 0 0)
    (hgradientU : HasQuadraticGerm gradientU 0 u₁ u₂)
    (hpath : ∀ r : ℝ,
      lowGradientChartPath radius metricA metricC metricD gradientQ gradientU r =
        lowGradientFactor (r, p, h))
    (hregular : ContDiffAt ℝ 3
      (fun r : ℝ => lowGradientFactor (r, p, h)) 0) :
    iteratedDeriv 2 (fun r : ℝ => lowGradientFactor (r, p, h)) 0 = 0 := by
  have hderiv := lowGradientFactor_scale_iteratedDeriv_two_eq_of_chartFactorization
    p h hradius hmetricA hmetricC hmetricD hgradientQ hgradientU hpath hregular
  norm_num at hderiv ⊢
  exact hderiv

end DFP.SecondLeg
