module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiniteSmoothCertificate
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionHolonomicAssembly
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.TopSectionOperator

public section

noncomputable section

open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Helper for Infrastructure I.16a: generic holonomic predecessor data is the metric
top-section certificate required by the finite-smooth bootstrap. -/
noncomputable def metricHolonomicTopSectionCertificate_of_data
    {ζ : ℝ → X}
    {r : ℕ}
    (data : LocalCutoff.GraphTransform.HolonomicTopSectionData (ζ : ℝ → X) r) :
    MetricHolonomicTopSectionCertificate (ζ : ℝ → X) r :=
  { value := data.value
    continuous_value := data.continuous_value
    derivative := data.derivative }

/-- Helper for Infrastructure I.16a: one order's operator, contraction estimate, fixed section,
and predecessor derivative data are kept together as a dependent package. -/
structure MetricContractionAndHolonomicData
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (r : ℕ) : Type u where
  operator :
    (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X))) →
      (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))
  contraction :
    LocalCutoff.GraphTransform.BoundedSectionContractionCertificate operator
  fixedSection : BoundedContinuousFunction ℝ
    ((ℝ [×(r - 1 + 1)]→L[ℝ] X))
  fixedSection_is_fixed : operator fixedSection = fixedSection
  predecessor : LocalCutoff.GraphTransform.HolonomicTopSectionData (ζ : ℝ → X) r

/-- Helper for Infrastructure I.16a: the order-`r` metric bunching factor is the contraction
factor expected for a top-section operator after the predecessor derivative transport. -/
def metricTopSectionBunchingFactor
    (d : MetricGraphTransformData X) (r : ℕ) : ℝ≥0 :=
  metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope * d.lower⁻¹ ^ r

/-- Helper for Infrastructure I.16a: coercing the NNReal top-section factor gives the real
bunching expression used by `MetricFiniteSmooth`. -/
theorem metricTopSectionBunchingFactor_coe
    (d : MetricGraphTransformData X) (r : ℕ) :
    (metricTopSectionBunchingFactor d r : ℝ) =
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r := by
  simp only [metricTopSectionBunchingFactor, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_inv]

/-- Infrastructure I.16a: the original real bunching inequality implies strictness of the
nonnegative factor used by the bounded-section contraction certificate. -/
theorem metricTopSectionBunchingFactor_lt_one_of_bunching
    {d : MetricGraphTransformData X} {r : ℕ}
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
    (d.lower : ℝ)⁻¹ ^ r < 1) :
    metricTopSectionBunchingFactor d r < 1 := by
  apply (NNReal.coe_lt_coe).mp
  rw [metricTopSectionBunchingFactor_coe]
  exact h_bunching

/-- Helper for Infrastructure I.16a: a real strict bunching inequality is equivalent to the
corresponding strict inequality for the nonnegative factor used by contraction certificates. -/
theorem metricTopSectionBunchingFactor_lt_one_of_real
    {d : MetricGraphTransformData X} {r : ℕ}
    (h_bunching : (metricTopSectionBunchingFactor d r : ℝ) < 1) :
    metricTopSectionBunchingFactor d r < 1 := by
  exact_mod_cast h_bunching

/-- Infrastructure I.16a: a source-facing pointwise estimate at the metric bunching factor
becomes the generic bounded-section contraction certificate consumed by the facade. -/
noncomputable def boundedSectionContractionCertificate_of_metricBunching
    [CompleteSpace X]
    {d : MetricGraphTransformData X}
    {r : ℕ}
    {T : (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X))) →
      (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))}
    (h_bunching : (metricTopSectionBunchingFactor d r : ℝ) < 1)
    (hpoint : ∀ f g u,
      dist (T f u) (T g u) ≤ (metricTopSectionBunchingFactor d r : ℝ) * dist f g) :
  LocalCutoff.GraphTransform.BoundedSectionContractionCertificate T :=
  { contractionFactor := metricTopSectionBunchingFactor d r
    contractionFactor_lt_one := metricTopSectionBunchingFactor_lt_one_of_real h_bunching
    dist_apply_le := hpoint }

/-- Helper for Infrastructure I.16a: a generic pointwise contraction certificate, a fixed
section, and predecessor derivative data form one metric top-section operator certificate. -/
noncomputable def metricTopSectionOperatorCertificate_of_contraction_and_data
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    {r : ℕ}
    {T : (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X))) →
      (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))}
    (contraction : LocalCutoff.GraphTransform.BoundedSectionContractionCertificate T)
    (fixedSection : BoundedContinuousFunction ℝ
      ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))
    (hfixed : T fixedSection = fixedSection)
    (data : LocalCutoff.GraphTransform.HolonomicTopSectionData (ζ : ℝ → X) r) :
    MetricTopSectionOperatorCertificate d ζ r :=
  metricTopSectionOperatorCertificate_of_boundedSectionContraction contraction
    fixedSection hfixed (metricHolonomicTopSectionCertificate_of_data data)

/-- Infrastructure I.16a: a bunched pointwise top-section estimate and explicit predecessor
data directly produce the metric operator certificate for one order. -/
noncomputable def metricTopSectionOperatorCertificate_of_metricBunching
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    {r : ℕ}
    {T : (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X))) →
      (BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))}
    (h_bunching : (metricTopSectionBunchingFactor d r : ℝ) < 1)
    (hpoint : ∀ f g u,
      dist (T f u) (T g u) ≤ (metricTopSectionBunchingFactor d r : ℝ) * dist f g)
    (fixedSection : BoundedContinuousFunction ℝ
      ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))
    (hfixed : T fixedSection = fixedSection)
    (data : LocalCutoff.GraphTransform.HolonomicTopSectionData (ζ : ℝ → X) r) :
    MetricTopSectionOperatorCertificate d ζ r :=
  metricTopSectionOperatorCertificate_of_contraction_and_data
    (boundedSectionContractionCertificate_of_metricBunching h_bunching hpoint)
    fixedSection hfixed data

/-- Helper for Infrastructure I.16a: order-one data consists of a continuous first section and
the explicit predecessor Taylor derivative equation.  No differentiability is inferred from a
Lipschitz fixed-point equation. -/
structure OrderOneHolonomicSectionData
    (ζ : ℝ → X) : Type u where
  value : ℝ → (ℝ [×1]→L[ℝ] X)
  continuous_value : Continuous value
  derivative : ∀ u, HasFDerivAt
    (fun y ↦ (ftaylorSeries ℝ ζ y) 0)
    ((value u).curryLeft) u

/-- Infrastructure I.16a: explicit order-one derivative data is converted to the predecessor
Taylor-section interface used uniformly at every positive order. -/
noncomputable def holonomicTopSectionData_of_orderOne
    {ζ : ℝ → X}
    (data : OrderOneHolonomicSectionData ζ) :
    LocalCutoff.GraphTransform.HolonomicTopSectionData ζ 1 :=
  { value := data.value
    continuous_value := data.continuous_value
    derivative := data.derivative }

/-- Infrastructure I.16a: an order-one section certificate can be consumed directly by the
metric top-section operator adapter once its pointwise contraction estimate is available. -/
noncomputable def metricTopSectionOperatorCertificate_of_orderOneData
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    {T : (BoundedContinuousFunction ℝ ((ℝ [×1]→L[ℝ] X))) →
      (BoundedContinuousFunction ℝ ((ℝ [×1]→L[ℝ] X)))}
    (h_bunching : (metricTopSectionBunchingFactor d 1 : ℝ) < 1)
    (hpoint : ∀ f g u,
      dist (T f u) (T g u) ≤ (metricTopSectionBunchingFactor d 1 : ℝ) * dist f g)
    (fixedSection : BoundedContinuousFunction ℝ ((ℝ [×1]→L[ℝ] X)))
    (hfixed : T fixedSection = fixedSection)
    (data : OrderOneHolonomicSectionData (ζ : ℝ → X)) :
    MetricTopSectionOperatorCertificate d ζ 1 :=
  metricTopSectionOperatorCertificate_of_metricBunching h_bunching hpoint fixedSection hfixed
    (holonomicTopSectionData_of_orderOne data)

/-- Infrastructure I.16a: a family of generic contraction certificates and explicit predecessor
data assembles into the metric finite-smooth certificate consumed by the regularity bridge. -/
noncomputable def metricFiniteSmoothCertificate_of_contraction_and_data
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    (packages : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      MetricContractionAndHolonomicData d ζ r) :
    MetricFiniteSmoothCertificate d ζ :=
  metricFiniteSmoothCertificate_of_operatorCertificates h_bunching
    (fun r hr hrν ↦
      let package := packages r hr hrν
      metricTopSectionOperatorCertificate_of_contraction_and_data
        package.contraction package.fixedSection package.fixedSection_is_fixed
        package.predecessor)

/-!
The same orderwise package is also useful when a downstream argument needs the
holonomic certificate itself rather than the final `ContDiff` conclusion.  Keep
this projection separate so callers do not have to reconstruct the operator
certificates by hand.
-/

/-- Helper for Infrastructure I.16a: contraction-and-holonomic data assemble directly into the
metric fixed-graph certificate used by finite-smooth regularity arguments. -/
theorem metricFixedGraph_holonomicCertificate_of_contraction_and_data
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (packages : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      MetricContractionAndHolonomicData d ζ r) :
    MetricFixedGraphHolonomicCertificate d ζ := by
  apply metricFixedGraph_holonomicCertificate_of_operatorCertificates
  intro r hr hrν
  let package := packages r hr hrν
  exact metricTopSectionOperatorCertificate_of_contraction_and_data
    package.contraction package.fixedSection package.fixedSection_is_fixed
    package.predecessor

/-- Infrastructure I.16a: the preceding contraction-and-data package directly yields finite
smoothness of the metric fixed graph. -/
theorem metricFixedGraph_contDiff_of_contraction_and_data
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    (packages : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      MetricContractionAndHolonomicData d ζ r) :
    ContDiff ℝ d.nu (ζ : ℝ → X) := by
  exact metricFixedGraph_contDiff_of_finiteSmoothCertificate
    (metricFiniteSmoothCertificate_of_contraction_and_data h_bunching packages)

end LocalInvariantGraph
