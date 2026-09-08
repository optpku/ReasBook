module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseAnalyticity
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseDerivativeConcrete
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseFactorization
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseDerivativeConcrete

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

universe u v w

/-!
# Continuous source certificate for the transverse cubic estimate

The source calculation supplies a local quotient identity and the cubic transverse derivatives
of its explicit numerator and denominator.  Analyticity then supplies the differentiability,
denominator nonvanishing, and local boundedness facts needed by the parent estimate.
-/

/-- Helper for Infrastructure I.16a companion: a germ equality on a product restricts to germ
equalities on every sufficiently nearby slice. -/
theorem eventually_prodSlice_eventuallyEq_of_eventuallyEq
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f g : X × Y → Z} {x₀ : X × Y}
    (hfg : f =ᶠ[𝓝 x₀] g) :
    ∀ᶠ x in 𝓝 x₀,
      (fun y : Y ↦ f (x.1, y)) =ᶠ[𝓝 x.2] (fun y : Y ↦ g (x.1, y)) := by
  obtain ⟨U, hUsub, hUopen, hbaseU⟩ := mem_nhds_iff.mp hfg
  have hUevent : ∀ᶠ x in 𝓝 x₀, x ∈ U :=
    hUopen.mem_nhds hbaseU
  filter_upwards [hUevent] with x hx
  have hsliceContinuous : ContinuousAt (fun y : Y ↦ (x.1, y)) x.2 :=
    continuousAt_const.prodMk continuousAt_id
  have hsliceU : ∀ᶠ y : Y in 𝓝 x.2, (x.1, y) ∈ U :=
    hsliceContinuous.eventually (hUopen.mem_nhds hx)
  filter_upwards [hsliceU] with y hy
  exact hUsub hy

/-- Helper for Infrastructure I.16a companion: explicit cubic formulas for the numerator and
denominator transverse derivatives, with continuous residual coefficient maps. -/
structure LowGradientTransverseContinuousSourceCertificate
    (A B : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ) : Prop where
  quotient_identity :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      (gradientFactors x.1 x.2.1 x.2.2).1 =
        lowGradientTransverseNumerator x / lowGradientTransverseDenominator x
  numerator_derivative :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      fderiv ℝ
          (fun z : ℝ × ℝ ↦ lowGradientTransverseNumerator (x.1, z.1, z.2))
          x.2 =
        x.1 ^ (3 : ℕ) • A x
  denominator_derivative :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      fderiv ℝ
          (fun z : ℝ × ℝ ↦ lowGradientTransverseDenominator (x.1, z.1, z.2))
          x.2 =
        x.1 ^ (3 : ℕ) • B x
  numerator_coefficient_continuous :
    ContinuousAt A ((0, 2, 1) : ℝ × ℝ × ℝ)
  denominator_coefficient_continuous :
    ContinuousAt B ((0, 2, 1) : ℝ × ℝ × ℝ)

/-- Helper for Infrastructure I.16a companion: the analytic numerator is transversely
differentiable at every point in a neighborhood of the canceled base. -/
theorem eventually_lowGradientTransverseNumerator_differentiableAt :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      DifferentiableAt ℝ
        (fun z : ℝ × ℝ ↦ lowGradientTransverseNumerator (x.1, z.1, z.2)) x.2 := by
  filter_upwards [lowGradientTransverseNumerator_analyticAt.eventually_analyticAt] with x hx
  have hslice : DifferentiableAt ℝ (fun z : ℝ × ℝ ↦ (x.1, z)) x.2 := by
    fun_prop
  exact hx.differentiableAt.comp x.2 hslice

/-- Helper for Infrastructure I.16a companion: the analytic denominator is transversely
differentiable at every point in a neighborhood of the canceled base. -/
theorem eventually_lowGradientTransverseDenominator_differentiableAt :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      DifferentiableAt ℝ
        (fun z : ℝ × ℝ ↦ lowGradientTransverseDenominator (x.1, z.1, z.2)) x.2 := by
  filter_upwards [lowGradientTransverseDenominator_analyticAt.eventually_analyticAt] with x hx
  have hslice : DifferentiableAt ℝ (fun z : ℝ × ℝ ↦ (x.1, z)) x.2 := by
    fun_prop
  exact hx.differentiableAt.comp x.2 hslice

/-- Helper for Infrastructure I.16a companion: continuous numerator and denominator cubic
coefficients produce an eventual cubic factorization of the low-gradient transverse derivative. -/
theorem LowGradientTransverseContinuousSourceCertificate.eventually_factorization
    {A B : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    (certificate : LowGradientTransverseContinuousSourceCertificate A B) :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      fderiv ℝ (fun z : ℝ × ℝ ↦ (gradientFactors x.1 z.1 z.2).1) x.2 =
        x.1 ^ (3 : ℕ) •
          transverseQuotientDerivative
            (lowGradientTransverseNumerator x)
            (lowGradientTransverseDenominator x) (A x) (B x) := by
  have hquotient :=
    eventually_prodSlice_eventuallyEq_of_eventuallyEq certificate.quotient_identity
  filter_upwards [hquotient,
    eventually_lowGradientTransverseNumerator_differentiableAt,
    eventually_lowGradientTransverseDenominator_differentiableAt,
    eventually_lowGradientTransverseDenominator_ne_zero,
    certificate.numerator_derivative,
    certificate.denominator_derivative] with x hquotient hnumDiff hdenDiff hdenNe hnum hden
  have hnumHas : HasFDerivAt
      (fun z : ℝ × ℝ ↦ lowGradientTransverseNumerator (x.1, z.1, z.2))
      (x.1 ^ (3 : ℕ) • A x) x.2 := by
    rw [← hnum]
    exact hnumDiff.hasFDerivAt
  have hdenHas : HasFDerivAt
      (fun z : ℝ × ℝ ↦ lowGradientTransverseDenominator (x.1, z.1, z.2))
      (x.1 ^ (3 : ℕ) • B x) x.2 := by
    rw [← hden]
    exact hdenDiff.hasFDerivAt
  rw [hquotient.fderiv_eq]
  exact fderiv_quotient_of_cubic_certificates hnumHas hdenHas hdenNe

/-- Helper for Infrastructure I.16a companion: continuity of the source coefficient maps and
analytic quotient data makes the cubic quotient coefficient continuous at the base point. -/
theorem LowGradientTransverseContinuousSourceCertificate.quotientCoefficient_continuousAt
    {A B : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    (certificate : LowGradientTransverseContinuousSourceCertificate A B) :
    ContinuousAt
      (fun x : ℝ × ℝ × ℝ ↦
        transverseQuotientDerivative
          (lowGradientTransverseNumerator x)
          (lowGradientTransverseDenominator x) (A x) (B x))
      ((0, 2, 1) : ℝ × ℝ × ℝ) := by
  have hnum := lowGradientTransverseNumerator_analyticAt.continuousAt
  have hden := lowGradientTransverseDenominator_analyticAt.continuousAt
  have hdenNe : lowGradientTransverseDenominator
      ((0, 2, 1) : ℝ × ℝ × ℝ) ≠ 0 := by
    rw [lowGradientTransverseDenominator_base]
    norm_num
  have hdenPowNe : lowGradientTransverseDenominator
      ((0, 2, 1) : ℝ × ℝ × ℝ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hdenNe
  have hinverse := (hden.inv₀ hdenNe).smul
    certificate.numerator_coefficient_continuous
  have hquotient := (hnum.div (hden.pow 2) hdenPowNe).smul
    certificate.denominator_coefficient_continuous
  unfold transverseQuotientDerivative
  exact hinverse.sub hquotient

/-- Infrastructure I.16a companion: explicit continuous cubic numerator and denominator
derivative formulas imply the transverse norm estimate that closes the parent theorem. -/
theorem LowGradientTransverseContinuousSourceCertificate.normBound
    {A B : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    (certificate : LowGradientTransverseContinuousSourceCertificate A B) :
    ∃ C > 0, ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖ ≤
        C * ‖x.1 ^ (3 : ℕ)‖ := by
  exact lowGradientFactorTransverseFDeriv_norm_bound_of_factorization
    certificate.eventually_factorization certificate.quotientCoefficient_continuousAt

end DFP.SecondLeg
