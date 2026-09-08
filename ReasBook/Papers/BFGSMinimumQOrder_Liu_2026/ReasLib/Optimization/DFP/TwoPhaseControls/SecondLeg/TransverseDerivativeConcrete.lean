module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicConcrete
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseDerivative
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.SecondLeg

/-!
# A concrete transverse-derivative adapter

The full rational body of `gradientFactors` is intentionally kept behind the
frame-coordinate quotient interface.  This module records the exact algebraic
bridge needed by the cubic transverse estimate: ε³ certificates for the
numerator and denominator derivatives give an ε³ certificate for the quotient.
-/

/-- Helper for Lemma 4.15: the quotient derivative coefficient associated with scalar numerator
and denominator values and their transverse derivative certificates. -/
def transverseQuotientDerivative
    (numerator denominator : ℝ) (A B : (ℝ × ℝ) →L[ℝ] ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  denominator⁻¹ • A - (numerator / denominator ^ 2) • B

/-- Helper for Lemma 4.15: ε³ derivative certificates for a scalar quotient combine into an
ε³ derivative certificate for the quotient itself. -/
theorem hasFDerivAt_quotient_of_cubic_certificates
    {f q : (ℝ × ℝ) → ℝ} {z : ℝ × ℝ}
    {ε : ℝ} {A B : (ℝ × ℝ) →L[ℝ] ℝ}
    (hnum : HasFDerivAt f (ε ^ (3 : ℕ) • A) z)
    (hden : HasFDerivAt q (ε ^ (3 : ℕ) • B) z)
    (hq : q z ≠ 0) :
    HasFDerivAt (fun y ↦ f y / q y)
      (ε ^ (3 : ℕ) • transverseQuotientDerivative (f z) (q z) A B) z := by
  have hinv := (hasFDerivAt_inv hq).comp z hden
  have hquotient := hnum.mul hinv
  have hmap :
      ε ^ (3 : ℕ) • transverseQuotientDerivative (f z) (q z) A B =
        f z • ContinuousLinearMap.toSpanSingleton ℝ (-(q z ^ 2)⁻¹) ∘SL
            (ε ^ (3 : ℕ) • B) + ((fun x ↦ x⁻¹) ∘ q) z •
              (ε ^ (3 : ℕ) • A) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [transverseQuotientDerivative, div_eq_mul_inv, pow_two]
    ring
  have hfunction : (fun y ↦ f y / q y) = f * (fun x ↦ x⁻¹) ∘ q := by
    funext y
    rfl
  rw [hfunction, hmap]
  exact hquotient

/-- Helper for Lemma 4.15: the fderivative form of the cubic quotient certificate. -/
theorem fderiv_quotient_of_cubic_certificates
    {f q : (ℝ × ℝ) → ℝ} {z : ℝ × ℝ}
    {ε : ℝ} {A B : (ℝ × ℝ) →L[ℝ] ℝ}
    (hnum : HasFDerivAt f (ε ^ (3 : ℕ) • A) z)
    (hden : HasFDerivAt q (ε ^ (3 : ℕ) • B) z)
    (hq : q z ≠ 0) :
    fderiv ℝ (fun y ↦ f y / q y) z =
      ε ^ (3 : ℕ) • transverseQuotientDerivative (f z) (q z) A B := by
  exact (hasFDerivAt_quotient_of_cubic_certificates hnum hden hq).fderiv

/-- Helper for Lemma 4.15: a frame certificate exposes the three coordinate identities needed
to identify the low gradient factor with its transverse numerator quotient. -/
structure LowGradientTransverseFrameCertificate
    (x : ℝ × ℝ × ℝ) : Prop where
  coordinate :
    (frame x.1 x.2.1 x.2.2).transpose *ᵥ
        outputGradient x.1 x.2.1 x.2.2 =
      ![(gradientFactors x.1 x.2.1 x.2.2).1,
        x.1 ^ 2 * (gradientFactors x.1 x.2.1 x.2.2).2]
  frame_zero :
    frame x.1 x.2.1 x.2.2 0 0 =
      (outputMetric x.1 x.2.1 x.2.2 1 1 -
        RealSymmetric2.low (outputMetric x.1 x.2.1 x.2.2 0 0)
          (outputMetric x.1 x.2.1 x.2.2 0 1)
          (outputMetric x.1 x.2.1 x.2.2 1 1)) /
        lowGradientTransverseDenominator x
  frame_one :
    frame x.1 x.2.1 x.2.2 1 0 =
      -outputMetric x.1 x.2.1 x.2.2 0 1 /
        lowGradientTransverseDenominator x

/-- Helper for Lemma 4.15: pointwise frame certificates assemble into a transverse quotient
identity for the low second-leg gradient factor. -/
theorem lowGradientTransverseSlice_eq_quotient_of_frame
    (x : ℝ × ℝ × ℝ)
    (hframe : ∀ z : ℝ × ℝ,
      LowGradientTransverseFrameCertificate (x.1, z.1, z.2)) :
    (fun z : ℝ × ℝ ↦ (gradientFactors x.1 z.1 z.2).1) =
      (fun z : ℝ × ℝ ↦
        lowGradientTransverseNumerator (x.1, z.1, z.2) /
          lowGradientTransverseDenominator (x.1, z.1, z.2)) := by
  funext z
  exact gradientFactors_low_eq_transverseQuotient_of_frame
    (x.1, z.1, z.2) (hframe z).coordinate (hframe z).frame_zero
      (hframe z).frame_one

/-- Lemma 4.15 adapter: frame-coordinate quotient data and ε³ derivative certificates produce
the concrete transverse `fderiv` factorization for the low gradient factor. -/
theorem lowGradientTransverseFDeriv_of_frame_certificates
    {x : ℝ × ℝ × ℝ}
    {A B : (ℝ × ℝ) →L[ℝ] ℝ}
    (hframe : ∀ z : ℝ × ℝ,
      LowGradientTransverseFrameCertificate (x.1, z.1, z.2))
    (hnum : HasFDerivAt
      (fun z : ℝ × ℝ ↦ lowGradientTransverseNumerator (x.1, z.1, z.2))
      (x.1 ^ (3 : ℕ) • A) (x.2.1, x.2.2))
    (hden : HasFDerivAt
      (fun z : ℝ × ℝ ↦ lowGradientTransverseDenominator (x.1, z.1, z.2))
      (x.1 ^ (3 : ℕ) • B) (x.2.1, x.2.2))
    (hden_ne : lowGradientTransverseDenominator x ≠ 0) :
    fderiv ℝ (fun z : ℝ × ℝ ↦ (gradientFactors x.1 z.1 z.2).1)
        (x.2.1, x.2.2) =
      x.1 ^ (3 : ℕ) •
        transverseQuotientDerivative
          (lowGradientTransverseNumerator x)
          (lowGradientTransverseDenominator x) A B := by
  have hquotient := fderiv_quotient_of_cubic_certificates hnum hden hden_ne
  rw [lowGradientTransverseSlice_eq_quotient_of_frame x hframe]
  exact hquotient

/-- Helper for Lemma 4.15: a norm bound on the quotient coefficient turns the concrete ε³
factorization into the pointwise transverse derivative estimate consumed by the generic bridge. -/
theorem lowGradientTransverseFDeriv_norm_le_of_frame_certificates
    {x : ℝ × ℝ × ℝ}
    {A B : (ℝ × ℝ) →L[ℝ] ℝ} {C : ℝ}
    (hframe : ∀ z : ℝ × ℝ,
      LowGradientTransverseFrameCertificate (x.1, z.1, z.2))
    (hnum : HasFDerivAt
      (fun z : ℝ × ℝ ↦ lowGradientTransverseNumerator (x.1, z.1, z.2))
      (x.1 ^ (3 : ℕ) • A) (x.2.1, x.2.2))
    (hden : HasFDerivAt
      (fun z : ℝ × ℝ ↦ lowGradientTransverseDenominator (x.1, z.1, z.2))
      (x.1 ^ (3 : ℕ) • B) (x.2.1, x.2.2))
    (hden_ne : lowGradientTransverseDenominator x ≠ 0)
    (hcoefficient :
      ‖transverseQuotientDerivative
          (lowGradientTransverseNumerator x)
          (lowGradientTransverseDenominator x) A B‖ ≤ C) :
    ‖fderiv ℝ (fun z : ℝ × ℝ ↦ (gradientFactors x.1 z.1 z.2).1)
        (x.2.1, x.2.2)‖ ≤ C * ‖x.1 ^ (3 : ℕ)‖ := by
  rw [lowGradientTransverseFDeriv_of_frame_certificates hframe hnum hden hden_ne,
    norm_smul]
  calc
    ‖x.1 ^ (3 : ℕ)‖ *
          ‖transverseQuotientDerivative
            (lowGradientTransverseNumerator x)
            (lowGradientTransverseDenominator x) A B‖ ≤
        ‖x.1 ^ (3 : ℕ)‖ * C :=
      mul_le_mul_of_nonneg_left hcoefficient (norm_nonneg _)
    _ = C * ‖x.1 ^ (3 : ℕ)‖ := by ring

end DFP.SecondLeg
