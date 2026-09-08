module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionDataAdapter
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderwiseCertificateAssembly

public section

noncomputable section

open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-!
This module is the source-facing boundary for the finite-order top-section
construction.  A source calculation supplies the candidate operator, its
pointwise contraction estimate, a fixed section, and the predecessor derivative
equation.  The bunching inequalities only certify that the supplied estimate is
strict; they do not manufacture any of these source-specific fields.
-/

/-- Infrastructure I.16a: a source-facing finite-order package records the
candidate top-section operators, their metric contraction estimates, fixed
sections, and predecessor Taylor derivative equations. -/
structure MetricSourceTopSectionAssembly
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) : Type u where
  bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
    (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
      (d.lower : ℝ)⁻¹ ^ r < 1
  candidateOperator : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
    (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X))) →
      (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))
  pointwiseContraction : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu,
    ∀ f g u,
      dist ((candidateOperator r hr hrν) f u) ((candidateOperator r hr hrν) g u) ≤
        (metricTopSectionBunchingFactor d r : ℝ) * dist f g
  fixedSection : ∀ r : ℕ, ∀ _hr : 1 ≤ r, ∀ _hrν : r ≤ d.nu,
    BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X))
  fixedSection_is_fixed : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu,
    (candidateOperator r hr hrν) (fixedSection r hr hrν) = fixedSection r hr hrν
  predecessorDerivative : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu, ∀ u,
    HasFDerivAt
      (fun y ↦ (ftaylorSeries ℝ (ζ : ℝ → X) y) (r - 1))
      ((fixedSection r hr hrν u).curryLeft) u

/-- Helper for Infrastructure I.16a: the source bunching inequality makes the
metric factor of one candidate operator a strict NNReal contraction factor. -/
theorem MetricSourceTopSectionAssembly.factor_lt_one
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricSourceTopSectionAssembly d ζ)
    (r : ℕ) (hr : 1 ≤ r) (hrν : r ≤ d.nu) :
    metricTopSectionBunchingFactor d r < 1 := by
  exact metricTopSectionBunchingFactor_lt_one_of_bunching
    (assembly.bunching r hr hrν)

/-- Helper for Infrastructure I.16a: a candidate operator and its source
contraction estimate become the bounded top-section operator datum consumed by
the metric certificate API. -/
noncomputable def MetricSourceTopSectionAssembly.candidateOperatorData
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricSourceTopSectionAssembly d ζ)
    (r : ℕ) (hr : 1 ≤ r) (hrν : r ≤ d.nu) :
    LocalCutoff.GraphTransform.BoundedTopSectionOperatorData
      (X := X) (r - 1 + 1) :=
  { operator := assembly.candidateOperator r hr hrν
    contractionFactor := metricTopSectionBunchingFactor d r
    contractionFactor_lt_one := assembly.factor_lt_one r hr hrν
    dist_apply_le := assembly.pointwiseContraction r hr hrν }

/-- Helper for Infrastructure I.16a: a supplied fixed section and predecessor
HasFDerivAt equation form the holonomic top-section data used by the successor
regularity theorem. -/
noncomputable def MetricSourceTopSectionAssembly.predecessorData
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricSourceTopSectionAssembly d ζ)
    (r : ℕ) (hr : 1 ≤ r) (hrν : r ≤ d.nu) :
    LocalCutoff.GraphTransform.HolonomicTopSectionData (ζ : ℝ → X) r :=
  { value := fun u ↦ assembly.fixedSection r hr hrν u
    continuous_value := (assembly.fixedSection r hr hrν).continuous
    derivative := assembly.predecessorDerivative r hr hrν }

/-- Helper for Infrastructure I.16a: each source package is converted into the
metric contraction-and-holonomicity data required by orderwise assembly. -/
noncomputable def MetricSourceTopSectionAssembly.orderData
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricSourceTopSectionAssembly d ζ) :
    ∀ r : ℕ, 1 ≤ r → r ≤ d.nu → MetricContractionAndHolonomicData d ζ r :=
  fun r hr hrν ↦ metricContractionAndHolonomicData_of_topSectionData
    (assembly.candidateOperatorData r hr hrν)
    (assembly.fixedSection r hr hrν)
    (assembly.fixedSection_is_fixed r hr hrν)
    (assembly.predecessorData r hr hrν)

/-- Helper for Infrastructure I.16a: the source package exposes the explicit
metric top-section operator certificates needed by fixed-jet consumers. -/
noncomputable def MetricSourceTopSectionAssembly.operatorCertificates
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricSourceTopSectionAssembly d ζ) :
    ∀ r : ℕ, 1 ≤ r → r ≤ d.nu → MetricTopSectionOperatorCertificate d ζ r :=
  fun r hr hrν ↦ metricTopSectionOperatorCertificate_of_topSectionData
    (assembly.candidateOperatorData r hr hrν)
    (assembly.fixedSection r hr hrν)
    (assembly.fixedSection_is_fixed r hr hrν)
    (assembly.predecessorData r hr hrν)

/-- Infrastructure I.16a: the source-facing top-section package becomes the
orderwise finite-smooth certificate while retaining every source obligation. -/
noncomputable def MetricSourceTopSectionAssembly.toOrderwiseAssembly
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricSourceTopSectionAssembly d ζ) :
    MetricOrderwiseCertificateAssembly d ζ :=
  { bunching := assembly.bunching
    orderData := assembly.orderData }

/-- Infrastructure I.16a: a source-facing top-section package yields the
structured finite-smooth certificate consumed by the metric bootstrap. -/
noncomputable def MetricSourceTopSectionAssembly.toFiniteSmoothCertificate
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricSourceTopSectionAssembly d ζ) :
    MetricFiniteSmoothCertificate d ζ :=
  assembly.toOrderwiseAssembly.toFiniteSmoothCertificate

/-- Infrastructure I.16a: the source-facing top-section package exposes the
holonomic fixed-graph certificate independently of the bunching conclusion. -/
theorem MetricSourceTopSectionAssembly.toHolonomicCertificate
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricSourceTopSectionAssembly d ζ) :
    MetricFixedGraphHolonomicCertificate d ζ := by
  exact assembly.toOrderwiseAssembly.toHolonomicCertificate

/-- Infrastructure I.16a: the complete source-facing top-section package gives
finite smoothness of the metric fixed graph.  Bare bunching alone is not enough. -/
theorem MetricSourceTopSectionAssembly.contDiff
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricSourceTopSectionAssembly d ζ) :
    ContDiff ℝ d.nu (ζ : ℝ → X) := by
  exact assembly.toOrderwiseAssembly.contDiff

/-- Infrastructure I.16a: the source-facing assembly simultaneously gives
finite smoothness and identifies every supplied fixed top section with the
corresponding iterated derivative of the metric fixed graph. -/
theorem MetricSourceTopSectionAssembly.contDiff_and_fixedSection_eq_iteratedFDeriv
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricSourceTopSectionAssembly d ζ) :
    ContDiff ℝ d.nu (ζ : ℝ → X) ∧
      ∀ (r : ℕ) (hr : 1 ≤ r) (hrν : r ≤ d.nu) (u : ℝ),
        assembly.fixedSection r hr hrν u =
          iteratedFDeriv ℝ (r - 1 + 1) (ζ : ℝ → X) u := by
  have hcont : ContDiff ℝ d.nu (ζ : ℝ → X) := assembly.contDiff
  refine ⟨hcont, ?_⟩
  intro r hr hrν u
  have hprevNat : r - 1 ≤ d.nu := (Nat.sub_le r 1).trans hrν
  have hprevOrder : ((r - 1 : ℕ) : WithTop ENat) ≤ (d.nu : WithTop ENat) := by
    exact_mod_cast hprevNat
  have hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X) := hcont.of_le hprevOrder
  exact (assembly.predecessorData r hr hrν).contDiff_succ_and_eq_iteratedFDeriv
    hr hprev |>.2 u

end LocalInvariantGraph
