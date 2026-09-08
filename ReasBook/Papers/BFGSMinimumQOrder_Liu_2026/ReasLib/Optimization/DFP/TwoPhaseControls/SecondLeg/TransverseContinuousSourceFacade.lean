module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseSourceCertificate
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseContinuousSourceCertificate
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseScaleTaylorCertificate

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

/-!
# Facade for the transverse source certificates

The older source certificate records frame identities, derivative witnesses, and a coefficient
bound.  The continuous source certificate is the smaller interface consumed by the cubic
factorization estimate.  This file is the integration bridge between those two public layers.
-/

/-- Helper for Infrastructure I.16a companion: an existing source certificate and continuity of
its coefficient maps assemble the continuous source certificate used by the cubic facade. -/
theorem LowGradientTransverseSourceCertificate.toContinuousSourceCertificate
    {A B : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ} {C : ℝ}
    (source : LowGradientTransverseSourceCertificate
      ((0, 2, 1) : ℝ × ℝ × ℝ) A B C)
    (hA : ContinuousAt A ((0, 2, 1) : ℝ × ℝ × ℝ))
    (hB : ContinuousAt B ((0, 2, 1) : ℝ × ℝ × ℝ)) :
    LowGradientTransverseContinuousSourceCertificate A B := by
  have hquotient :
      ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
        (gradientFactors x.1 x.2.1 x.2.2).1 =
          lowGradientTransverseNumerator x / lowGradientTransverseDenominator x := by
    filter_upwards [source.frame] with x hframe
    have hframeAt := hframe x.2
    exact gradientFactors_low_eq_transverseQuotient_of_frame
      x hframeAt.coordinate hframeAt.frame_zero hframeAt.frame_one
  have hnum :
      ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
        fderiv ℝ
            (fun z : ℝ × ℝ ↦ lowGradientTransverseNumerator (x.1, z.1, z.2))
            x.2 = x.1 ^ (3 : ℕ) • A x := by
    filter_upwards [source.numerator] with x hx
    exact hx.fderiv
  have hden :
      ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
        fderiv ℝ
            (fun z : ℝ × ℝ ↦ lowGradientTransverseDenominator (x.1, z.1, z.2))
            x.2 = x.1 ^ (3 : ℕ) • B x := by
    filter_upwards [source.denominator] with x hx
    exact hx.fderiv
  exact
    { quotient_identity := hquotient
      numerator_derivative := hnum
      denominator_derivative := hden
      numerator_coefficient_continuous := hA
      denominator_coefficient_continuous := hB }

/-- Helper for Infrastructure I.16a companion: the legacy source certificate becomes directly
consumable by the continuous cubic norm-bound facade once its coefficient maps are continuous. -/
theorem LowGradientTransverseSourceCertificate.normBound_of_continuousCoefficients
    {A B : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ} {C : ℝ}
    (source : LowGradientTransverseSourceCertificate
      ((0, 2, 1) : ℝ × ℝ × ℝ) A B C)
    (hA : ContinuousAt A ((0, 2, 1) : ℝ × ℝ × ℝ))
    (hB : ContinuousAt B ((0, 2, 1) : ℝ × ℝ × ℝ)) :
    ∃ C > 0, ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖ ≤
        C * ‖x.1 ^ (3 : ℕ)‖ := by
  exact (source.toContinuousSourceCertificate hA hB).normBound

/-- Helper for Infrastructure I.16a companion: the two normalized scale coefficients directly
produce the transverse derivative norm estimate consumed by the second-leg parent. -/
theorem LowGradientTransverseScaleTaylorCertificate.normBound
    (certificate : LowGradientTransverseScaleTaylorCertificate) :
    ∃ C > 0, ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖ ≤
        C * ‖x.1 ^ (3 : ℕ)‖ := by
  obtain ⟨C, hC, hcertificate⟩ :=
    certificate.existsScaleFactorizationCertificate
  exact hcertificate.normBound

end DFP.SecondLeg
