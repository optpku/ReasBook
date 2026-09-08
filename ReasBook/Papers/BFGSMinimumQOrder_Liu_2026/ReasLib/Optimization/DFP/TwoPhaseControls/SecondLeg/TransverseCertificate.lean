module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseDerivativeConcrete

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

/-!
# Neighborhood certificates for the transverse low-gradient factor

The pointwise quotient adapters live in `TransverseDerivativeConcrete`.  This module gives
them a filter-level interface: the source-specific calculation supplies one certificate, and
the downstream cubic estimate can consume its eventual derivative and norm consequences.
-/

/-!
The certificate is deliberately expressed using the numerator and denominator maps rather than
the expanded rational formula.  This keeps the source-specific algebra at the boundary of the
API and makes the derivative factorization reusable by the I.16a proof.
-/

/-- Helper for Infrastructure I.16a: a neighborhood certificate bundles the frame identities,
the cubic numerator and denominator derivative certificates, nonvanishing, and a uniform bound
for the resulting quotient coefficient. -/
structure LowGradientTransverseNeighborhoodCertificate
    (x₀ : ℝ × ℝ × ℝ)
    (A B : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ)
    (C : ℝ) : Prop where
  frame : ∀ᶠ x in 𝓝 x₀,
    ∀ z : ℝ × ℝ,
      LowGradientTransverseFrameCertificate (x.1, z.1, z.2)
  numerator : ∀ᶠ x in 𝓝 x₀,
    HasFDerivAt
      (fun z : ℝ × ℝ ↦ lowGradientTransverseNumerator (x.1, z.1, z.2))
      (x.1 ^ (3 : ℕ) • A x) (x.2.1, x.2.2)
  denominator : ∀ᶠ x in 𝓝 x₀,
    HasFDerivAt
      (fun z : ℝ × ℝ ↦ lowGradientTransverseDenominator (x.1, z.1, z.2))
      (x.1 ^ (3 : ℕ) • B x) (x.2.1, x.2.2)
  denominator_ne : ∀ᶠ x in 𝓝 x₀,
    lowGradientTransverseDenominator x ≠ 0
  coefficient_bound : ∀ᶠ x in 𝓝 x₀,
    ‖transverseQuotientDerivative
        (lowGradientTransverseNumerator x)
        (lowGradientTransverseDenominator x) (A x) (B x)‖ ≤ C
  positive_bound : 0 < C

/-- Infrastructure I.16a: a neighborhood certificate yields the eventual cubic factorization of
the transverse derivative of the low second-leg gradient factor. -/
theorem lowGradientTransverseFDeriv_eq_of_neighborhoodCertificate
    {x₀ : ℝ × ℝ × ℝ}
    {A B : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    {C : ℝ}
    (certificate : LowGradientTransverseNeighborhoodCertificate x₀ A B C) :
    ∀ᶠ x in 𝓝 x₀,
      fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2) =
        x.1 ^ (3 : ℕ) •
          transverseQuotientDerivative
            (lowGradientTransverseNumerator x)
            (lowGradientTransverseDenominator x) (A x) (B x) := by
  filter_upwards [certificate.frame, certificate.numerator,
    certificate.denominator, certificate.denominator_ne] with x hframe hnum hden hden_ne
  exact lowGradientTransverseFDeriv_of_frame_certificates
    hframe hnum hden hden_ne

/-- Infrastructure I.16a: a neighborhood certificate yields the uniform eventual norm bound
needed by the second-leg transverse estimate. -/
theorem lowGradientFactorTransverseFDeriv_norm_bound_of_neighborhoodCertificate
    {x₀ : ℝ × ℝ × ℝ}
    {A B : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    {C : ℝ}
    (certificate : LowGradientTransverseNeighborhoodCertificate x₀ A B C) :
    ∃ C > 0, ∀ᶠ x in 𝓝 x₀,
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖ ≤
        C * ‖x.1 ^ (3 : ℕ)‖ := by
  refine ⟨C, certificate.positive_bound, ?_⟩
  filter_upwards [certificate.frame, certificate.numerator,
    certificate.denominator, certificate.denominator_ne,
    certificate.coefficient_bound] with x hframe hnum hden hden_ne hbound
  exact lowGradientTransverseFDeriv_norm_le_of_frame_certificates
    hframe hnum hden hden_ne hbound

end DFP.SecondLeg
