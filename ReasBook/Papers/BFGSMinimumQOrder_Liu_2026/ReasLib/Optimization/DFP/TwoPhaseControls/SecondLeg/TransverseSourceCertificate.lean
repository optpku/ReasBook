module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCertificate

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

/-!
# Source-facing certificate for the transverse low-gradient estimate

This adapter keeps the owner-side calculation separate from the quotient plumbing.  Its fields
are exactly the eventual facts that a concrete residual calculation must provide.
-/

/-- Helper for Infrastructure I.16a: source-side eventual data for the transverse low-gradient
quotient, with coefficient maps `A` and `B` and a uniform quotient bound. -/
structure LowGradientTransverseSourceCertificate
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

/-- Infrastructure I.16a: source-side numerator, denominator, frame, and coefficient data imply
the uniform cubic transverse derivative bound consumed by downstream estimates. -/
theorem lowGradientFactorTransverseFDeriv_norm_bound_of_sourceCertificate
    {x₀ : ℝ × ℝ × ℝ}
    {A B : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    {C : ℝ}
    (source : LowGradientTransverseSourceCertificate x₀ A B C) :
    ∃ C > 0, ∀ᶠ x in 𝓝 x₀,
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖ ≤
        C * ‖x.1 ^ (3 : ℕ)‖ := by
  exact lowGradientFactorTransverseFDeriv_norm_bound_of_neighborhoodCertificate
    { frame := source.frame
      numerator := source.numerator
      denominator := source.denominator
      denominator_ne := source.denominator_ne
      coefficient_bound := source.coefficient_bound
      positive_bound := source.positive_bound }

end DFP.SecondLeg
