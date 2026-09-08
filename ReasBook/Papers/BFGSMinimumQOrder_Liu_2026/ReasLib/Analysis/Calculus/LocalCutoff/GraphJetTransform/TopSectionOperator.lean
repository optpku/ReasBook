module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.SectionContraction
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicFixedSection

public section

open scoped NNReal Topology

universe u v

namespace LocalCutoff.GraphTransform

/-!
This file supplies the small interface shared by orderwise graph-jet operators.
The operator calculation remains source-specific; this module only packages its
pointwise contraction and the holonomic predecessor equation.
-/

variable {α : Type u} {β : Type v}

/-- Helper for Infrastructure I.16a: a bounded-section operator certificate records the
strict factor and the pointwise distance estimate needed by the sup-metric contraction. -/
structure BoundedSectionContractionCertificate
    [TopologicalSpace α] [Nonempty α]
    [NormedAddCommGroup β] [CompleteSpace β]
    (T : (BoundedContinuousFunction α β) → (BoundedContinuousFunction α β)) : Type max u v where
  contractionFactor : ℝ≥0
  contractionFactor_lt_one : contractionFactor < 1
  dist_apply_le : ∀ f g x,
    dist (T f x) (T g x) ≤ contractionFactor * dist f g

/-- Helper for Infrastructure I.16a: a pointwise bounded-section certificate yields the
canonical `ContractingWith` structure used by Mathlib's fixed-point API. -/
theorem BoundedSectionContractionCertificate.contractingWith
    [TopologicalSpace α] [Nonempty α]
    [NormedAddCommGroup β] [CompleteSpace β]
    {T : (BoundedContinuousFunction α β) → (BoundedContinuousFunction α β)}
    (certificate : BoundedSectionContractionCertificate T) :
    ContractingWith certificate.contractionFactor T := by
  exact BoundedContinuousFunction.contractingWith_of_dist_apply_le_mul
    certificate.contractionFactor_lt_one certificate.dist_apply_le

/-- Infrastructure I.16a: the contraction certificate gives existence and uniqueness of a
bounded fixed section, without committing to a source-specific formula for the operator. -/
theorem BoundedSectionContractionCertificate.existsUnique_fixedSection
    [TopologicalSpace α] [Nonempty α]
    [NormedAddCommGroup β] [CompleteSpace β]
    {T : (BoundedContinuousFunction α β) → (BoundedContinuousFunction α β)}
    (certificate : BoundedSectionContractionCertificate T) :
    ∃! f, T f = f := by
  exact BoundedContinuousFunction.existsUnique_fixedPoint_of_dist_apply_le_mul
    certificate.contractionFactor_lt_one certificate.dist_apply_le

/-- Helper for Infrastructure I.16a: a holonomic top section packages continuity and the
predecessor Taylor coefficient's pointwise derivative equation. -/
structure HolonomicTopSectionData
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ζ : ℝ → X) (r : ℕ) : Type u where
  value : ℝ → (ℝ [×(r - 1 + 1)]→L[ℝ] X)
  continuous_value : Continuous value
  derivative : ∀ u, HasFDerivAt
    (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1))
    ((value u).curryLeft) u

/-- Infrastructure I.16a: holonomic predecessor data upgrades a graph by one smoothness
order and identifies the new section with the corresponding iterated derivative. -/
theorem HolonomicTopSectionData.contDiff_succ_and_eq_iteratedFDeriv
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ζ : ℝ → X} {r : ℕ}
    (hr : 1 ≤ r)
    (hprev : ContDiff ℝ (r - 1) ζ)
    (data : HolonomicTopSectionData ζ r) :
    ContDiff ℝ r ζ ∧
      ∀ u, data.value u = iteratedFDeriv ℝ (r - 1 + 1) ζ u := by
  exact contDiff_succ_and_topSection_eq_iteratedFDeriv hr hprev data.value
    data.continuous_value data.derivative

end LocalCutoff.GraphTransform
