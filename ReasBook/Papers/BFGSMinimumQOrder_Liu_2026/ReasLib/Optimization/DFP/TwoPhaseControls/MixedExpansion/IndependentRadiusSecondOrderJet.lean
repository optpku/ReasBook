module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondJetConcrete
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondJetConcrete

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
The concrete second-gradient companion currently exposes its first jet.  This
boundary file records the exact second-order derivative interface still needed
by the physical-drift calculation, without unfolding the large quotient map.
-/

/-- Helper for Appendix Lemma A.6: a second derivative of an abstract scalar
    factor path transports through a pointwise identification of that path. -/
theorem iteratedDeriv_two_of_secondDerivativeTransport
    {f g : ℝ → ℝ} {c : ℝ}
    (hsecond : HasDerivAt (deriv f) c 0)
    (hpath : ∀ r : ℝ, f r = g r) :
    iteratedDeriv 2 g 0 = c := by
  have hfun : f = g := by
    funext r
    exact hpath r
  have hsecondG : HasDerivAt (deriv g) c 0 := by
    rw [← hfun]
    exact hsecond
  simpa only [iteratedDeriv_zero, iteratedDeriv_succ] using hsecondG.deriv

/-- Helper for Appendix Lemma A.6: a factor-level second derivative gives the
    displayed second-radius derivative of the normalized low-gradient coordinate. -/
theorem independentRadiusSecondGradientLow_iteratedDeriv_two_of_factor
    (θ : ℝ × ℝ × ℝ) (F : ℝ → ℝ)
    (hsecond : HasDerivAt (deriv F)
      ((θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 9) 0)
    (hpath : ∀ r : ℝ,
      F r = (independentRadiusSecondGradient (θ, r)).1) :
    iteratedDeriv 2 (fun r ↦ (independentRadiusSecondGradient (θ, r)).1) 0 =
      (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 9 := by
  exact iteratedDeriv_two_of_secondDerivativeTransport hsecond hpath

/-- Helper for Appendix Lemma A.6: a quadratic germ and `C³` regularity transport
    the displayed second-radius derivative through the normalized low-gradient path. -/
theorem independentRadiusSecondGradientLow_iteratedDeriv_two_of_quadraticGerm
    (θ : ℝ × ℝ × ℝ) (F : ℝ → ℝ) (c : ℝ)
    (hGerm : HasQuadraticGerm F 1 0 c)
    (hregular : ContDiffAt ℝ 3 F 0)
    (hpath : ∀ r : ℝ,
      F r = (independentRadiusSecondGradient (θ, r)).1) :
    iteratedDeriv 2 (fun r ↦ (independentRadiusSecondGradient (θ, r)).1) 0 = 2 * c := by
  have hF : iteratedDeriv 2 F 0 = 2 * c :=
    HasQuadraticGerm.iteratedDeriv_two_eq_of_contDiffAt hGerm hregular
  have hfun : F = (fun r ↦ (independentRadiusSecondGradient (θ, r)).1) := by
    funext r
    exact hpath r
  calc
    iteratedDeriv 2 (fun r ↦ (independentRadiusSecondGradient (θ, r)).1) 0 =
        iteratedDeriv 2 F 0 := by rw [← hfun]
    _ = 2 * c := hF

/-- Helper for Appendix Lemma A.6: the low-coordinate chart formed from a metric
    triple and a gradient pair, with the radius factor kept explicit. -/
def lowGradientChartPath
    (radius metricA metricC metricD gradientQ gradientU : ℝ → ℝ) : ℝ → ℝ :=
  fun r ↦
    let low :=
      (metricA r + metricD r -
        Real.sqrt ((metricA r - metricD r) ^ 2 + 4 * (metricC r) ^ 2)) / 2
    let denominator :=
      Real.sqrt ((metricD r - low) ^ 2 + (metricC r) ^ 2)
    ((metricD r - low) * gradientQ r -
      radius r * metricC r * gradientU r) / denominator

/-- Appendix Lemma A.6 companion: component quadratic germs combine into the
    canonical low-gradient quadratic germ.  The quadratic coefficient is
    independent of the metric diagonal jets and equals `q₂ - c₁² / 2`. -/
theorem lowGradientChartPath_quadraticGerm_of_componentGerms
    {radius metricA metricC metricD gradientQ gradientU : ℝ → ℝ}
    {a₂ c₁ c₂ d₁ d₂ q₁ q₂ u₁ u₂ : ℝ}
    (hradius : HasQuadraticGerm radius 0 1 0)
    (hmetricA : HasQuadraticGerm metricA 0 0 a₂)
    (hmetricC : HasQuadraticGerm metricC 0 c₁ c₂)
    (hmetricD : HasQuadraticGerm metricD 1 d₁ d₂)
    (hgradientQ : HasQuadraticGerm gradientQ 1 q₁ q₂)
    (hgradientU : HasQuadraticGerm gradientU 0 u₁ u₂) :
    HasQuadraticGerm (lowGradientChartPath radius metricA metricC metricD
      gradientQ gradientU) 1 q₁ (q₂ - c₁ ^ 2 / 2) := by
  let low : ℝ → ℝ := fun r ↦
    (metricA r + metricD r -
      Real.sqrt ((metricA r - metricD r) ^ 2 + 4 * (metricC r) ^ 2)) / 2
  let rad : ℝ → ℝ := fun r ↦
    (metricA r - metricD r) ^ 2 + 4 * (metricC r) ^ 2
  let denominatorRad : ℝ → ℝ := fun r ↦
    (metricD r - low r) ^ 2 + (metricC r) ^ 2
  let denominator : ℝ → ℝ := fun r ↦ Real.sqrt (denominatorRad r)
  let numerator : ℝ → ℝ := fun r ↦
    (metricD r - low r) * gradientQ r -
      radius r * metricC r * gradientU r
  have hmetricAD := hmetricA.sub hmetricD
  have hmetricCSq := hmetricC.mul hmetricC
  have hradRaw := hmetricAD.mul hmetricAD |>.add (hmetricCSq.constMul 4)
  have hradCoeff : HasQuadraticGerm rad 1 (2 * d₁)
      (d₁ ^ 2 - 2 * a₂ + 2 * d₂ + 4 * c₁ ^ 2) := by
    have h0 : (0 - 1) * (0 - 1) + 4 * (0 * 0) = (1 : ℝ) := by
      ring
    have h1 : (0 - 1) * (0 - d₁) + (0 - d₁) * (0 - 1) +
        4 * (0 * c₁ + c₁ * 0) = 2 * d₁ := by
      ring
    have h2 :
        (0 - 1) * (a₂ - d₂) + (0 - d₁) * (0 - d₁) +
            (a₂ - d₂) * (0 - 1) +
            4 * (0 * c₂ + c₁ * c₁ + c₂ * 0) =
          d₁ ^ 2 - 2 * a₂ + 2 * d₂ + 4 * c₁ ^ 2 := by
      ring
    have hcoeff := hradRaw.congrCoefficients h0 h1 h2
    apply hcoeff.congrFunction
    intro r
    simp only [rad]
    ring
  have hgapRaw := hradCoeff.sqrtOne
  have hgap : HasQuadraticGerm (fun r ↦ Real.sqrt (rad r)) 1 d₁
      (-a₂ + d₂ + 2 * c₁ ^ 2) := by
    apply hgapRaw.congrCoefficients
    · ring
    · ring
    · ring
  have hlowRaw := (hmetricA.add hmetricD).sub hgap
  have hlowScaled := hlowRaw.constMul (1 / 2 : ℝ)
  have hlow : HasQuadraticGerm low 0 0 (a₂ - c₁ ^ 2) := by
    have h0 : (1 / 2 : ℝ) * (0 + 1 - 1) = (0 : ℝ) := by
      ring
    have h1 : (1 / 2 : ℝ) * (0 + d₁ - d₁) = (0 : ℝ) := by
      ring
    have h2 : (1 / 2 : ℝ) *
        (a₂ + d₂ - (-a₂ + d₂ + 2 * c₁ ^ 2)) =
          a₂ - c₁ ^ 2 := by
      ring
    have hcoeff := hlowScaled.congrCoefficients h0 h1 h2
    apply hcoeff.congrFunction
    intro r
    simp only [low]
    ring
  have hmetricDLow := hmetricD.sub hlow
  have hdenominatorRadRaw := hmetricDLow.mul hmetricDLow |>.add hmetricCSq
  have hdenominatorRad : HasQuadraticGerm denominatorRad 1 (2 * d₁)
      (d₁ ^ 2 + 2 * d₂ - 2 * a₂ + 3 * c₁ ^ 2) := by
    have h0 : (1 - 0) * (1 - 0) + 0 * 0 = (1 : ℝ) := by
      ring
    have h1 : (1 - 0) * (d₁ - 0) + (d₁ - 0) * (1 - 0) +
        (0 * c₁ + c₁ * 0) = 2 * d₁ := by
      ring
    have h2 :
        (1 - 0) * (d₂ - (a₂ - c₁ ^ 2)) + (d₁ - 0) * (d₁ - 0) +
            (d₂ - (a₂ - c₁ ^ 2)) * (1 - 0) +
            (0 * c₂ + c₁ * c₁ + c₂ * 0) =
          d₁ ^ 2 + 2 * d₂ - 2 * a₂ + 3 * c₁ ^ 2 := by
      ring
    have hcoeff := hdenominatorRadRaw.congrCoefficients h0 h1 h2
    apply hcoeff.congrFunction
    intro r
    simp only [denominatorRad]
    ring
  have hdenominatorRaw := hdenominatorRad.sqrtOne
  have hdenominator : HasQuadraticGerm denominator 1 d₁
      (d₂ - a₂ + 3 * c₁ ^ 2 / 2) := by
    apply hdenominatorRaw.congrCoefficients
    · ring
    · ring
    · ring
  have hfirstNumerator := (hmetricD.sub hlow).mul hgradientQ
  have hsecondNumerator := (hradius.mul hmetricC).mul hgradientU
  have hnumeratorRaw := hfirstNumerator.sub hsecondNumerator
  have hnumerator : HasQuadraticGerm numerator 1 (d₁ + q₁)
      (d₂ - a₂ + c₁ ^ 2 + q₂ + d₁ * q₁) := by
    apply hnumeratorRaw.congrCoefficients
    · ring
    · ring
    · ring
  have hdenominatorBase : (1 : ℝ) ≠ 0 := by
    norm_num
  have hquotient := hnumerator.div hdenominator hdenominatorBase
  apply hquotient.congrCoefficients
  · ring
  · ring
  · ring

/-- Helper for Appendix Lemma A.6: a pointwise chart factorization transfers the
    component quadratic germ to the normalized second-gradient low coordinate. -/
theorem independentRadiusSecondGradientLow_quadraticGerm_of_chartFactorization
    (θ : ℝ × ℝ × ℝ)
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
        (independentRadiusSecondGradient (θ, r)).1) :
    HasQuadraticGerm
      (fun r ↦ (independentRadiusSecondGradient (θ, r)).1) 1 q₁
        (q₂ - c₁ ^ 2 / 2) := by
  have hchart := lowGradientChartPath_quadraticGerm_of_componentGerms
    hradius hmetricA hmetricC hmetricD hgradientQ hgradientU
  apply hchart.congrFunction
  intro r
  exact (hpath r).symm

end DFP.TwoLeg.Mixed
