module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ScaleQuadraticGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseDerivativeConcrete
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondOrderJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseDerivativeConcrete
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicConcrete

public section

noncomputable section

namespace DFP.SecondLeg

open DFP.TwoLeg.Mixed

/-!
# Public source certificate for the second-leg low-factor germ

The parent source keeps its residual tuple private.  This boundary therefore uses only the
public output metric, output gradient, and frame-coordinate certificate.  A parent proof can
instantiate the six coordinate identities locally, while the chart calculation remains reusable.
-/

/-- Helper for Lemma 4.15: a public certificate identifies the output coordinates with a
signed-scale low chart and records the component quadratic germs used by that chart. -/
structure LowGradientScaleChartCertificate
    (p h : ℝ)
    (radius metricA metricC metricD gradientQ gradientV : ℝ → ℝ)
    (a₀ a₁ a₂ c₀ c₁ c₂ d₁ d₂ q₁ q₂ v₀ v₁ v₂ : ℝ) : Prop where
  radius_germ : HasQuadraticGerm radius 0 1 0
  metricA_germ : HasQuadraticGerm metricA a₀ a₁ a₂
  metricC_germ : HasQuadraticGerm metricC c₀ c₁ c₂
  metricD_germ : HasQuadraticGerm metricD 1 d₁ d₂
  gradientQ_germ : HasQuadraticGerm gradientQ 1 q₁ q₂
  gradientV_germ : HasQuadraticGerm gradientV v₀ v₁ v₂
  radius_identity : ∀ r : ℝ, radius r = r
  metricA_output : ∀ r : ℝ,
    outputMetric r p h 0 0 = r ^ 4 * metricA r
  metricC_output : ∀ r : ℝ,
    outputMetric r p h 0 1 = r ^ 2 * metricC r
  metricD_output : ∀ r : ℝ,
    outputMetric r p h 1 1 = metricD r
  gradientQ_output : ∀ r : ℝ,
    outputGradient r p h 0 = gradientQ r
  gradientV_output : ∀ r : ℝ,
    outputGradient r p h 1 = r ^ 2 * gradientV r
  frame_certificate : ∀ r : ℝ,
    LowGradientTransverseFrameCertificate (r, p, h)

/-- Helper for Lemma 4.15: the public output-coordinate certificate gives the exact generic
low-chart path for the low second-leg gradient factor. -/
theorem lowGradientChartPath_eq_lowGradientFactor_of_scaleChartCertificate
    {p h : ℝ}
    {radius metricA metricC metricD gradientQ gradientV : ℝ → ℝ}
    {a₀ a₁ a₂ c₀ c₁ c₂ d₁ d₂ q₁ q₂ v₀ v₁ v₂ : ℝ}
    (certificate : LowGradientScaleChartCertificate p h radius metricA metricC metricD
      gradientQ gradientV a₀ a₁ a₂ c₀ c₁ c₂ d₁ d₂ q₁ q₂ v₀ v₁ v₂) :
    ∀ r : ℝ,
      lowGradientChartPath radius
          (fun s ↦ s ^ 4 * metricA s) (fun s ↦ s ^ 2 * metricC s)
          metricD gradientQ (fun s ↦ s * gradientV s) r =
        lowGradientFactor (r, p, h) := by
  intro r
  have hframe := certificate.frame_certificate r
  have hquotient := gradientFactors_low_eq_transverseQuotient_of_frame
    (r, p, h) hframe.coordinate hframe.frame_zero hframe.frame_one
  have hmetricA := certificate.metricA_output r
  have hmetricC := certificate.metricC_output r
  have hmetricD := certificate.metricD_output r
  have hgradientQ := certificate.gradientQ_output r
  have hgradientV := certificate.gradientV_output r
  have hradius := certificate.radius_identity r
  change lowGradientChartPath radius
      (fun s ↦ s ^ 4 * metricA s) (fun s ↦ s ^ 2 * metricC s)
      metricD gradientQ (fun s ↦ s * gradientV s) r =
    (gradientFactors r p h).1
  rw [hquotient]
  simp only [lowGradientChartPath, lowGradientTransverseNumerator,
    lowGradientTransverseDenominator, RealSymmetric2.gap_apply,
    RealSymmetric2.low_apply, RealSymmetric2.lowDenom_apply]
  rw [hmetricA, hmetricC, hmetricD, hgradientQ, hgradientV]
  rw [hradius]
  ring_nf

/-- Helper for Lemma 4.15: component germs with a cubic metric scaling transfer to the actual
second-leg low-factor quadratic germ. -/
theorem lowGradientFactor_scale_quadraticGerm_of_scaleChartCertificate
    {p h : ℝ}
    {radius metricA metricC metricD gradientQ gradientV : ℝ → ℝ}
    {a₀ a₁ a₂ c₀ c₁ c₂ d₁ d₂ q₁ q₂ v₀ v₁ v₂ : ℝ}
    (certificate : LowGradientScaleChartCertificate p h radius metricA metricC metricD
      gradientQ gradientV a₀ a₁ a₂ c₀ c₁ c₂ d₁ d₂ q₁ q₂ v₀ v₁ v₂) :
    HasQuadraticGerm (fun r : ℝ ↦ lowGradientFactor (r, p, h)) 1 q₁ q₂ := by
  let X : ℝ → ℝ := fun r ↦ r
  have hX : HasQuadraticGerm X 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp only [X, quadraticModel]
    ring
  have hX2raw := hX.mul hX
  have hX2 : HasQuadraticGerm (fun r ↦ X r ^ 2) 0 0 1 := by
    have hpath : ∀ r : ℝ, X r ^ 2 = X r * X r := by
      intro r
      simp only [pow_two]
    have hraw := hX2raw.congrFunction hpath
    have hconstant : (0 * 0 : ℝ) = 0 := by ring
    have hlinear : (0 * 1 + 1 * 0 : ℝ) = 0 := by ring
    have hquadratic : (0 * 0 + 1 * 1 + 0 * 0 : ℝ) = 1 := by ring
    exact hraw.congrCoefficients hconstant hlinear hquadratic
  have hX4raw := hX2.mul hX2
  have hX4 : HasQuadraticGerm (fun r ↦ X r ^ 4) 0 0 0 := by
    have hpath : ∀ r : ℝ, X r ^ 4 = X r ^ 2 * X r ^ 2 := by
      intro r
      ring
    have hraw := hX4raw.congrFunction hpath
    have hconstant : (0 * 0 : ℝ) = 0 := by ring
    have hlinear : (0 * 0 + 0 * 0 : ℝ) = 0 := by ring
    have hquadratic : (0 * 1 + 0 * 0 + 1 * 0 : ℝ) = 0 := by ring
    exact hraw.congrCoefficients hconstant hlinear hquadratic
  have hmetricAraw := hX4.mul certificate.metricA_germ
  have hmetricA : HasQuadraticGerm
      (fun r ↦ X r ^ 4 * metricA r) 0 0 0 := by
    have hconstant : (0 * a₀ : ℝ) = 0 := by ring
    have hlinear : (0 * a₁ + 0 * a₀ : ℝ) = 0 := by ring
    have hquadratic : (0 * a₂ + 0 * a₁ + 0 * a₀ : ℝ) = 0 := by ring
    exact hmetricAraw.congrCoefficients hconstant hlinear hquadratic
  have hmetricCraw := hX2.mul certificate.metricC_germ
  have hmetricC : HasQuadraticGerm
      (fun r ↦ X r ^ 2 * metricC r) 0 0 c₀ := by
    have hconstant : (0 * c₀ : ℝ) = 0 := by ring
    have hlinear : (0 * c₁ + 0 * c₀ : ℝ) = 0 := by ring
    have hquadratic : (0 * c₂ + 0 * c₁ + 1 * c₀ : ℝ) = c₀ := by ring
    exact hmetricCraw.congrCoefficients hconstant hlinear hquadratic
  have hgradientUraw := hX.mul certificate.gradientV_germ
  have hgradientU : HasQuadraticGerm
      (fun r ↦ X r * gradientV r) 0 v₀ v₁ := by
    have hconstant : (0 * v₀ : ℝ) = 0 := by ring
    have hlinear : (0 * v₁ + 1 * v₀ : ℝ) = v₀ := by ring
    have hquadratic : (0 * v₂ + 1 * v₁ + 0 * v₀ : ℝ) = v₁ := by ring
    exact hgradientUraw.congrCoefficients hconstant hlinear hquadratic
  have hpath := lowGradientChartPath_eq_lowGradientFactor_of_scaleChartCertificate certificate
  have hchart := lowGradientFactor_scale_quadraticGerm_of_chartFactorization
    (p := p) (h := h) certificate.radius_germ hmetricA hmetricC
    certificate.metricD_germ certificate.gradientQ_germ hgradientU hpath
  apply hchart.congrCoefficients
  · rfl
  · rfl
  · ring

/-- Helper for Lemma 4.15: a `C³` scale-chart certificate gives the vanishing second scale
derivative of the low second-leg gradient factor. -/
theorem lowGradientFactor_scale_iteratedDeriv_two_eq_zero_of_scaleChartCertificate
    {p h : ℝ}
    {radius metricA metricC metricD gradientQ gradientV : ℝ → ℝ}
    {a₀ a₁ a₂ c₀ c₁ c₂ d₁ d₂ q₁ q₂ v₀ v₁ v₂ : ℝ}
    (certificate : LowGradientScaleChartCertificate p h radius metricA metricC metricD
      gradientQ gradientV a₀ a₁ a₂ c₀ c₁ c₂ d₁ d₂ q₁ q₂ v₀ v₁ v₂)
    (hregular : ContDiffAt ℝ 3
      (fun r : ℝ ↦ lowGradientFactor (r, p, h)) 0) :
    q₂ = 0 →
    iteratedDeriv 2 (fun r : ℝ ↦ lowGradientFactor (r, p, h)) 0 = 0 := by
  have hgerm := lowGradientFactor_scale_quadraticGerm_of_scaleChartCertificate certificate
  intro hq₂
  have hderiv := HasQuadraticGerm.iteratedDeriv_two_eq_of_contDiffAt hgerm hregular
  simpa [hq₂] using hderiv

/-- Helper for Lemma 4.15: the removable SecondLeg gradient-factor pair is the independent
second-step pair after the scale substitution `b = ε`, `r = ε²`. -/
theorem gradientFactors_eq_independentSecondGradientFactors
    (ε p h : ℝ) :
    gradientFactors ε p h =
      independentSecondGradientFactors ε (ε ^ 2)
        (DFP.FirstLeg.spectralFactors ε p h).1
        (DFP.FirstLeg.spectralFactors ε p h).2
        (DFP.FirstLeg.gradientFactors ε p h).1
        (DFP.FirstLeg.gradientFactors ε p h).2 := by
  unfold gradientFactors independentSecondGradientFactors
  dsimp [independentSecondResiduals, independentSecondGradientResiduals]
  ring_nf

/-- Helper for Lemma 4.15: projecting the normalized pair bridge gives the removable
SecondLeg low factor as the independent second-step low factor. -/
theorem lowGradientFactor_eq_independentSecondGradientFactors
    (ε p h : ℝ) :
    lowGradientFactor (ε, p, h) =
      (independentSecondGradientFactors ε (ε ^ 2)
        (DFP.FirstLeg.spectralFactors ε p h).1
        (DFP.FirstLeg.spectralFactors ε p h).2
        (DFP.FirstLeg.gradientFactors ε p h).1
        (DFP.FirstLeg.gradientFactors ε p h).2).1 := by
  exact congrArg Prod.fst (gradientFactors_eq_independentSecondGradientFactors ε p h)

/-- Helper for Lemma 4.15: the removable SecondLeg spectral-factor pair is the independent
second-step pair after the scale substitution `b = ε`, `r = ε²`. -/
theorem spectralFactors_eq_independentSecondSpectralFactors
    (ε p h : ℝ) :
    spectralFactors ε p h =
      independentSecondSpectralFactors ε (ε ^ 2)
        (DFP.FirstLeg.spectralFactors ε p h).1
        (DFP.FirstLeg.spectralFactors ε p h).2
        (DFP.FirstLeg.gradientFactors ε p h).1
        (DFP.FirstLeg.gradientFactors ε p h).2 := by
  unfold spectralFactors independentSecondSpectralFactors
  dsimp [independentSecondResiduals]
  ring_nf

/-- Helper for Lemma 4.15: the second-leg output metric agrees with the independent
second-step metric under the same scale substitution and first-step factors. -/
theorem outputMetric_eq_independentSecondMetric
    (ε p h : ℝ) :
    outputMetric ε p h =
      independentSecondMetric ε (ε ^ 2)
        (DFP.FirstLeg.spectralFactors ε p h).1
        (DFP.FirstLeg.spectralFactors ε p h).2
        (DFP.FirstLeg.gradientFactors ε p h).1
        (DFP.FirstLeg.gradientFactors ε p h).2 := by
  unfold outputMetric independentSecondMetric
  dsimp [independentSecondResiduals]
  ext i j
  fin_cases i
  · fin_cases j
    · simp
      ring_nf
    · simp
      ring_nf
      simp
  · fin_cases j
    · simp
      ring_nf
      simp
    · simp
      ring_nf

/-- Helper for Lemma 4.15: the second-leg output gradient agrees with the independent
second-step gradient under the same scale substitution and first-step factors. -/
theorem outputGradient_eq_independentSecondGradient
    (ε p h : ℝ) :
    outputGradient ε p h =
      independentSecondGradient ε (ε ^ 2)
        (DFP.FirstLeg.spectralFactors ε p h).1
        (DFP.FirstLeg.spectralFactors ε p h).2
        (DFP.FirstLeg.gradientFactors ε p h).1
        (DFP.FirstLeg.gradientFactors ε p h).2 := by
  unfold outputGradient independentSecondGradient
  dsimp [independentSecondGradientResiduals]
  ext i
  fin_cases i
  · simp
    ring_nf
  · simp
    ring_nf
    simp

end DFP.SecondLeg
