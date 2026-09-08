module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiniteSmooth
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicFixedSection
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.TopSectionOperator
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicTopSectionCertificate

public section

noncomputable section

open scoped NNReal Topology
open Filter Set

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-!
# Structured finite-smooth certificates for metric graph transforms

`MetricFiniteSmooth` already exposes a proposition-valued existential certificate.  This
companion keeps the same mathematical assumptions, but packages the section at each order as
an object.  The package is useful to downstream fixed-jet constructions, where the section and
its derivative equation must be consumed separately.
-/

/-- The holonomic top section and its predecessor derivative equation at one order. -/
structure MetricHolonomicTopSectionCertificate
    (ζ : ℝ → X) (r : ℕ) : Type u where
  value : ℝ → (ℝ [×(r - 1 + 1)]→L[ℝ] X)
  continuous_value : Continuous value
  derivative : ∀ u, HasFDerivAt
    (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1))
    ((value u).curryLeft) u

/-- A finite-smooth metric certificate consists of quantitative bunching and one holonomic
top-section certificate for every positive order up to the declared order. -/
structure MetricFiniteSmoothCertificate
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) : Type u where
  bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
    (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
      (d.lower : ℝ)⁻¹ ^ r < 1
  topSection : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      MetricHolonomicTopSectionCertificate (ζ : ℝ → X) r

/-!
The next certificate isolates the only genuinely order-dependent input in the metric
finite-smooth bootstrap.  The operator itself is intentionally abstract: the source-specific
jet calculation supplies it, while the contraction and fixed-section plumbing is shared.
-/

/-- Helper for Infrastructure I.16a: a top-section operator certificate records a strict
contraction on bounded continuous sections together with the holonomicity of its fixed section. -/
structure MetricTopSectionOperatorCertificate
    (d : MetricGraphTransformData X)
  (ζ : SmallLipschitzGraph X d.radius d.slope)
    (r : ℕ) : Type u where
  operator :
    (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X))) →
      (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))
  contractionFactor : ℝ≥0
  contractionFactor_lt_one : contractionFactor < 1
  dist_apply_le : ∀ f g u,
    dist (operator f u) (operator g u) ≤ contractionFactor * dist f g
  fixedSection : BoundedContinuousFunction ℝ
    ((ℝ [×(r - 1 + 1)]→L[ℝ] X))
  fixedSection_is_fixed : operator fixedSection = fixedSection
  fixedSection_holonomic :
    MetricHolonomicTopSectionCertificate (ζ : ℝ → X) r

/-- Helper for Infrastructure I.16a: a generic bounded-section contraction certificate and
an explicitly holonomic fixed section specialize to the metric graph certificate. -/
noncomputable def metricTopSectionOperatorCertificate_of_boundedSectionContraction
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    {r : ℕ}
    {T : (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X))) →
      (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))}
    (data : LocalCutoff.GraphTransform.BoundedSectionContractionCertificate T)
    (fixedSection : BoundedContinuousFunction ℝ
      ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))
    (hfixed : T fixedSection = fixedSection)
    (holonomic : MetricHolonomicTopSectionCertificate (ζ : ℝ → X) r) :
    MetricTopSectionOperatorCertificate d ζ r :=
  { operator := T
    contractionFactor := data.contractionFactor
    contractionFactor_lt_one := data.contractionFactor_lt_one
    dist_apply_le := data.dist_apply_le
    fixedSection := fixedSection
    fixedSection_is_fixed := hfixed
    fixedSection_holonomic := holonomic }

/-!
The following adapter is the direct bridge from the graph-jet fixed-section interface to the
metric certificate consumed by the finite-smooth bootstrap.  It keeps the source-specific
operator construction and the predecessor derivative equation in one certificate, while
exposing the metric contraction fields in the form used by the orderwise assembly theorem.
-/

/-- Helper for Infrastructure I.16a: a holonomic graph-jet fixed-section certificate supplies
the corresponding metric top-section operator certificate. -/
noncomputable def metricTopSectionOperatorCertificate_of_holonomicFixedTopSection
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    {r : ℕ}
    (certificate :
      LocalCutoff.GraphTransform.HolonomicFixedTopSectionCertificate r (ζ : ℝ → X)) :
    MetricTopSectionOperatorCertificate d ζ r :=
  { operator := certificate.data.operator
    contractionFactor := certificate.data.contractionFactor
    contractionFactor_lt_one := certificate.data.contractionFactor_lt_one
    dist_apply_le := certificate.data.dist_apply_le
    fixedSection := certificate.fixedSection
    fixedSection_is_fixed := certificate.fixedSection_is_fixed
    fixedSection_holonomic :=
      { value := fun u ↦ certificate.fixedSection u
        continuous_value := certificate.fixedSection.continuous
        derivative := certificate.fixedSection_derivative } }

/-- Helper for Infrastructure I.16a: the fixed section recorded in an operator certificate is
the unique fixed point supplied by its strict contraction. -/
theorem MetricTopSectionOperatorCertificate.fixedSection_unique
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    {r : ℕ}
    (certificate : MetricTopSectionOperatorCertificate d ζ r)
    (a : BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))
    (ha : certificate.operator a = a) :
    a = certificate.fixedSection := by
  let hcontract : ContractingWith certificate.contractionFactor certificate.operator :=
    BoundedContinuousFunction.contractingWith_of_dist_apply_le_mul
      certificate.contractionFactor_lt_one certificate.dist_apply_le
  have ha_canonical := hcontract.fixedPoint_unique ha
  have hfixed_canonical := hcontract.fixedPoint_unique certificate.fixedSection_is_fixed
  exact ha_canonical.trans hfixed_canonical.symm

/-- Infrastructure I.16a: orderwise section-operator certificates assemble into the
holonomic certificate consumed by the finite-smooth metric bootstrap.  The fixed sections are
obtained canonically from the existing bounded-section contraction theorem. -/
theorem metricFixedGraph_holonomicCertificate_of_operatorCertificates
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (operators : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      MetricTopSectionOperatorCertificate d ζ r) :
    MetricFixedGraphHolonomicCertificate d ζ := by
  refine ⟨fun r hr hrν ↦ ?_⟩
  let certificate := operators r hr hrν
  exact ⟨certificate.fixedSection_holonomic.value,
    certificate.fixedSection_holonomic.continuous_value,
    certificate.fixedSection_holonomic.derivative⟩

/-- Infrastructure I.16a: quantitative bunching and orderwise section operators assemble into a
structured finite-smooth certificate without exposing the fixed-section construction. -/
noncomputable def metricFiniteSmoothCertificate_of_operatorCertificates
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    (operators : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      MetricTopSectionOperatorCertificate d ζ r) :
    MetricFiniteSmoothCertificate d ζ :=
  { bunching := h_bunching
    topSection := fun r hr hrν ↦ (operators r hr hrν).fixedSection_holonomic }

/-- Infrastructure I.16a: a complete family of section-operator certificates directly yields
the finite smoothness of the metric fixed graph. -/
theorem metricFixedGraph_contDiff_of_operatorCertificates
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    (operators : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      MetricTopSectionOperatorCertificate d ζ r) :
    ContDiff ℝ d.nu (ζ : ℝ → X) := by
  have hcertificate : MetricFiniteSmoothCertificate d ζ :=
    metricFiniteSmoothCertificate_of_operatorCertificates h_bunching operators
  apply metricFixedGraph_contDiff_of_holonomicCertificate d ζ
  refine ⟨fun r hr hrν ↦ ?_⟩
  let c := hcertificate.topSection r hr hrν
  exact ⟨c.value, c.continuous_value, c.derivative⟩

/-- Infrastructure I.16a: a family of holonomic graph-jet fixed-section certificates gives the
metric finite-smoothness conclusion through the shared contraction and successor bootstrap. -/
theorem metricFixedGraph_contDiff_of_holonomicFixedTopSectionCertificates
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    (certificates : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      LocalCutoff.GraphTransform.HolonomicFixedTopSectionCertificate r (ζ : ℝ → X)) :
    ContDiff ℝ d.nu (ζ : ℝ → X) := by
  apply metricFixedGraph_contDiff_of_operatorCertificates h_bunching
  intro r hr hrν
  exact metricTopSectionOperatorCertificate_of_holonomicFixedTopSection
    (certificates r hr hrν)

/-- Infrastructure I.16a: contraction data and predecessor derivative equations for the canonical
fixed sections directly yield the finite-smooth metric graph. -/
theorem metricFixedGraph_contDiff_of_canonicalTopSectionOperators
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    (operators : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      LocalCutoff.GraphTransform.BoundedTopSectionOperatorData
        (X := X) (r - 1 + 1))
    (hderiv : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu, ∀ u,
      HasFDerivAt
        (fun y ↦ (ftaylorSeries ℝ (ζ : ℝ → X) y) (r - 1))
        ((LocalCutoff.GraphTransform.canonicalFixedTopSection
          (operators r hr hrν) u).curryLeft) u) :
    ContDiff ℝ d.nu (ζ : ℝ → X) := by
  apply metricFixedGraph_contDiff_of_holonomicFixedTopSectionCertificates h_bunching
  intro r hr hrν
  exact LocalCutoff.GraphTransform.canonicalHolonomicFixedTopSectionCertificate
    (operators r hr hrν) (hderiv r hr hrν)

/-- Convert the structured certificate to the existential interface in `MetricFiniteSmooth`. -/
theorem MetricFiniteSmoothCertificate.toHolonomicCertificate
    [CompleteSpace X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (certificate : MetricFiniteSmoothCertificate d ζ) :
    MetricFixedGraphHolonomicCertificate d ζ := by
  refine ⟨fun r hr hrν ↦ ?_⟩
  let c := certificate.topSection r hr hrν
  exact ⟨c.value, c.continuous_value, c.derivative⟩

/-- Helper for Infrastructure I.16a: an existential holonomic fixed-graph
certificate and the finite-order bunching inequalities form a structured
finite-smooth certificate. -/
noncomputable def MetricFiniteSmoothCertificate.ofHolonomicCertificate
    [CompleteSpace X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    (certificate : MetricFixedGraphHolonomicCertificate d ζ) :
    MetricFiniteSmoothCertificate d ζ :=
  { bunching := h_bunching
    topSection := fun r hr hrν ↦
      let witness := Classical.choose (certificate.topSection r hr hrν)
      { value := witness
        continuous_value := (Classical.choose_spec (certificate.topSection r hr hrν)).1
        derivative := (Classical.choose_spec (certificate.topSection r hr hrν)).2 } }

/-- The structured certificate yields finite smoothness through the existing holonomic bridge. -/
theorem metricFixedGraph_contDiff_of_finiteSmoothCertificate
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (certificate : MetricFiniteSmoothCertificate d ζ) :
    ContDiff ℝ d.nu (ζ : ℝ → X) := by
  exact metricFixedGraph_contDiff_of_holonomicCertificate d ζ
    certificate.toHolonomicCertificate

/-- The order-by-order induction also identifies every certified top section with the next
iterated derivative of the fixed graph. -/
theorem metricFixedGraph_contDiff_and_topSections_eq_iteratedFDeriv
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (certificate : MetricFiniteSmoothCertificate d ζ) :
    ContDiff ℝ d.nu (ζ : ℝ → X) ∧
      ∀ (r : ℕ) (hr : 1 ≤ r) (hrν : r ≤ d.nu) (u : ℝ),
        (certificate.topSection r hr hrν).value u =
          iteratedFDeriv ℝ (r - 1 + 1) (ζ : ℝ → X) u := by
  have hall : ∀ r : ℕ, r ≤ d.nu → ContDiff ℝ r (ζ : ℝ → X) := by
    intro r hrν
    induction r with
    | zero =>
        exact contDiff_zero.mpr ζ.1.continuous
    | succ r hprevious =>
        have hr_pos : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
        have hr_le : r ≤ d.nu := (Nat.le_succ r).trans hrν
        have hprev : ContDiff ℝ r (ζ : ℝ → X) := hprevious hr_le
        let c := certificate.topSection (r + 1) hr_pos hrν
        exact LocalCutoff.GraphTransform.contDiff_succ_of_holonomic_topSection
          hr_pos hprev c.value c.continuous_value c.derivative
  have hcont : ContDiff ℝ d.nu (ζ : ℝ → X) := hall d.nu le_rfl
  refine ⟨hcont, ?_⟩
  intro r hr hrν u
  have hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X) :=
    hall (r - 1) ((Nat.sub_le r 1).trans hrν)
  let c := certificate.topSection r hr hrν
  exact (LocalCutoff.GraphTransform.contDiff_succ_and_topSection_eq_iteratedFDeriv
    hr hprev c.value c.continuous_value c.derivative).2 u

end LocalInvariantGraph
