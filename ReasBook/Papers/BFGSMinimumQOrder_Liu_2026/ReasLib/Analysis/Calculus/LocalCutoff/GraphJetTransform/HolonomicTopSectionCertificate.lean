module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.SectionContraction
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.TopSectionOperator
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicFixedSection
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetRealization

public section

open scoped NNReal Topology

universe u

namespace LocalCutoff.GraphTransform

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-!
This file isolates the reusable fixed-section interface for the top coefficient.
The contraction estimate constructs and uniquely identifies a bounded section;
the derivative equation is kept as an explicit holonomicity input for the
finite-smooth bootstrap.
-/

/-- Infrastructure I.16a: quantitative data for a bounded operator on order-`r`
top sections. -/
structure BoundedTopSectionOperatorData (r : ℕ) where
  operator :
    (BoundedContinuousFunction ℝ ((ℝ [×r]→L[ℝ] X))) →
      (BoundedContinuousFunction ℝ ((ℝ [×r]→L[ℝ] X)))
  contractionFactor : ℝ≥0
  contractionFactor_lt_one : contractionFactor < 1
  dist_apply_le : ∀ f g u,
    dist (operator f u) (operator g u) ≤ contractionFactor * dist f g

/-- Helper for Infrastructure I.16a: a generic bounded-section contraction certificate
specialized to order-`r` multilinear sections supplies the canonical top-section data. -/
noncomputable def BoundedTopSectionOperatorData.ofContractionCertificate
    {r : ℕ}
    {T : (BoundedContinuousFunction ℝ ((ℝ [×r]→L[ℝ] X))) →
      (BoundedContinuousFunction ℝ ((ℝ [×r]→L[ℝ] X)))}
    (certificate : BoundedSectionContractionCertificate T) :
    BoundedTopSectionOperatorData (X := X) r :=
  { operator := T
    contractionFactor := certificate.contractionFactor
    contractionFactor_lt_one := certificate.contractionFactor_lt_one
    dist_apply_le := certificate.dist_apply_le }

/-- Infrastructure I.16a: the canonical fixed top section supplied by the
strict contraction estimate. -/
noncomputable def canonicalFixedTopSection (data : BoundedTopSectionOperatorData (X := X) r) :
    BoundedContinuousFunction ℝ ((ℝ [×r]→L[ℝ] X)) :=
  ContractingWith.fixedPoint data.operator
    (BoundedContinuousFunction.contractingWith_of_dist_apply_le_mul
      data.contractionFactor_lt_one data.dist_apply_le)

/-- Infrastructure I.16a: the canonical top section is fixed by its section
operator. -/
theorem canonicalFixedTopSection_is_fixed
    (data : BoundedTopSectionOperatorData (X := X) r) :
    data.operator (canonicalFixedTopSection data) = canonicalFixedTopSection data := by
  exact (BoundedContinuousFunction.contractingWith_of_dist_apply_le_mul
    data.contractionFactor_lt_one data.dist_apply_le).fixedPoint_isFixedPt

/-- Infrastructure I.16a: a bounded fixed top section is unique under the
pointwise contraction estimate. -/
theorem fixedTopSection_eq_canonical
    (data : BoundedTopSectionOperatorData (X := X) r)
    (a : BoundedContinuousFunction ℝ ((ℝ [×r]→L[ℝ] X)))
    (ha : data.operator a = a) :
    a = canonicalFixedTopSection data := by
  exact (BoundedContinuousFunction.contractingWith_of_dist_apply_le_mul
    data.contractionFactor_lt_one data.dist_apply_le).fixedPoint_unique ha

/-- Infrastructure I.16a: a fixed top section together with its predecessor
derivative equation is the holonomic interface consumed by the successor
regularity theorem. -/
structure HolonomicFixedTopSectionCertificate
    (r : ℕ) (ζ : ℝ → X) where
  data : BoundedTopSectionOperatorData (X := X) (r - 1 + 1)
  fixedSection : BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X))
  fixedSection_is_fixed : data.operator fixedSection = fixedSection
  fixedSection_derivative : ∀ u, HasFDerivAt
    (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1))
    ((fixedSection u).curryLeft) u

/-- Infrastructure I.16a: a predecessor derivative equation for the canonical contracted
section packages directly into a holonomic fixed top-section certificate. -/
noncomputable def canonicalHolonomicFixedTopSectionCertificate
    {r : ℕ} {ζ : ℝ → X}
    (data : BoundedTopSectionOperatorData (X := X) (r - 1 + 1))
    (hderiv : ∀ u, HasFDerivAt
      (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1))
      ((canonicalFixedTopSection data u).curryLeft) u) :
    HolonomicFixedTopSectionCertificate r ζ :=
  { data := data
    fixedSection := canonicalFixedTopSection data
    fixedSection_is_fixed := canonicalFixedTopSection_is_fixed data
    fixedSection_derivative := hderiv }

/-- Infrastructure I.16a: a generic contraction certificate and the predecessor derivative
equation directly produce the canonical holonomic fixed top-section certificate. -/
noncomputable def canonicalHolonomicFixedTopSectionCertificate_of_contraction
    {r : ℕ} {ζ : ℝ → X}
    {T : (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X))) →
      (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))}
    (certificate : BoundedSectionContractionCertificate T)
    (hderiv : ∀ u, HasFDerivAt
      (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1))
      ((canonicalFixedTopSection
        (BoundedTopSectionOperatorData.ofContractionCertificate certificate) u).curryLeft) u) :
    HolonomicFixedTopSectionCertificate r ζ :=
  canonicalHolonomicFixedTopSectionCertificate
    (BoundedTopSectionOperatorData.ofContractionCertificate certificate) hderiv

/-- Infrastructure I.16a: the holonomic fixed top section is the next
iterated derivative of the underlying graph. -/
theorem HolonomicFixedTopSectionCertificate.fixedSection_eq_iteratedFDeriv
    {r : ℕ} {ζ : ℝ → X}
    (certificate : HolonomicFixedTopSectionCertificate r ζ)
    (hr : 1 ≤ r) (hprev : ContDiff ℝ (r - 1) ζ) :
    ∀ u, certificate.fixedSection u = iteratedFDeriv ℝ (r - 1 + 1) ζ u := by
  have hresult := LocalCutoff.GraphTransform.contDiff_succ_and_topSection_eq_iteratedFDeriv
    hr hprev certificate.fixedSection certificate.fixedSection.continuous
      certificate.fixedSection_derivative
  exact hresult.2

/-- Infrastructure I.16a: the certificate simultaneously supplies the
successor smoothness and the iterated-derivative transport for its fixed section. -/
theorem HolonomicFixedTopSectionCertificate.contDiff_succ_and_fixedSection_eq_iteratedFDeriv
    {r : ℕ} {ζ : ℝ → X}
    (certificate : HolonomicFixedTopSectionCertificate r ζ)
    (hr : 1 ≤ r) (hprev : ContDiff ℝ (r - 1) ζ) :
    ContDiff ℝ r ζ ∧
      ∀ u, certificate.fixedSection u = iteratedFDeriv ℝ (r - 1 + 1) ζ u := by
  exact LocalCutoff.GraphTransform.contDiff_succ_and_topSection_eq_iteratedFDeriv
    hr hprev certificate.fixedSection certificate.fixedSection.continuous
      certificate.fixedSection_derivative

end LocalCutoff.GraphTransform
