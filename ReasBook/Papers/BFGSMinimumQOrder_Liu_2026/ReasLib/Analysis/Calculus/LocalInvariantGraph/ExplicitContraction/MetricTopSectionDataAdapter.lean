module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionFacade
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiniteSmoothCertificate
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicTopSectionCertificate

public section

noncomputable section

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Infrastructure I.16a: a bounded top-section operator datum is converted to
the contraction certificate consumed by the metric facade. -/
noncomputable def boundedSectionContractionCertificate_of_topSectionData
    [CompleteSpace X]
    {r : ℕ}
    (data : LocalCutoff.GraphTransform.BoundedTopSectionOperatorData (X := X) r) :
    LocalCutoff.GraphTransform.BoundedSectionContractionCertificate data.operator :=
  { contractionFactor := data.contractionFactor
    contractionFactor_lt_one := data.contractionFactor_lt_one
    dist_apply_le := data.dist_apply_le }

/-- Infrastructure I.16a: bounded top-section operator data, a fixed section,
and explicit predecessor holonomicity form one metric order certificate. -/
noncomputable def metricTopSectionOperatorCertificate_of_topSectionData
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    {r : ℕ}
    (data : LocalCutoff.GraphTransform.BoundedTopSectionOperatorData
      (X := X) (r - 1 + 1))
    (fixedSection : BoundedContinuousFunction ℝ
      ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))
    (hfixed : data.operator fixedSection = fixedSection)
    (predecessor : LocalCutoff.GraphTransform.HolonomicTopSectionData
      (ζ : ℝ → X) r) :
    MetricTopSectionOperatorCertificate d ζ r :=
  metricTopSectionOperatorCertificate_of_contraction_and_data
    (boundedSectionContractionCertificate_of_topSectionData data)
    fixedSection hfixed predecessor

/-- Infrastructure I.16a: one source-facing order package combines operator
data, its fixed section, and the predecessor derivative equation. -/
noncomputable def metricContractionAndHolonomicData_of_topSectionData
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    {r : ℕ}
    (data : LocalCutoff.GraphTransform.BoundedTopSectionOperatorData
      (X := X) (r - 1 + 1))
    (fixedSection : BoundedContinuousFunction ℝ
      ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))
    (hfixed : data.operator fixedSection = fixedSection)
    (predecessor : LocalCutoff.GraphTransform.HolonomicTopSectionData
      (ζ : ℝ → X) r) :
    MetricContractionAndHolonomicData d ζ r :=
  { operator := data.operator
    contraction := boundedSectionContractionCertificate_of_topSectionData data
    fixedSection := fixedSection
    fixedSection_is_fixed := hfixed
    predecessor := predecessor }

/-- Infrastructure I.16a: a family of bounded top-section data and explicit
fixed-section/holonomicity fields assembles into the metric finite-smooth certificate. -/
noncomputable def metricFiniteSmoothCertificate_of_topSectionData
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    (data : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      LocalCutoff.GraphTransform.BoundedTopSectionOperatorData
        (X := X) (r - 1 + 1))
    (fixedSection : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu,
      BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))
    (hfixed : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu,
      (data r hr hrν).operator (fixedSection r hr hrν) = fixedSection r hr hrν)
    (predecessor : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu,
      LocalCutoff.GraphTransform.HolonomicTopSectionData (ζ : ℝ → X) r) :
    MetricFiniteSmoothCertificate d ζ :=
  metricFiniteSmoothCertificate_of_contraction_and_data h_bunching
    (fun r hr hrν ↦ metricContractionAndHolonomicData_of_topSectionData
      (data r hr hrν) (fixedSection r hr hrν) (hfixed r hr hrν)
      (predecessor r hr hrν))

/-- Infrastructure I.16a: the source-facing top-section family directly yields
the `ContDiff` conclusion after all operator and holonomicity certificates are supplied. -/
theorem metricFixedGraph_contDiff_of_topSectionData
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    (data : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      LocalCutoff.GraphTransform.BoundedTopSectionOperatorData
        (X := X) (r - 1 + 1))
    (fixedSection : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu,
      BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))
    (hfixed : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu,
      (data r hr hrν).operator (fixedSection r hr hrν) = fixedSection r hr hrν)
    (predecessor : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu,
      LocalCutoff.GraphTransform.HolonomicTopSectionData (ζ : ℝ → X) r) :
    ContDiff ℝ d.nu (ζ : ℝ → X) := by
  exact metricFixedGraph_contDiff_of_finiteSmoothCertificate
    (metricFiniteSmoothCertificate_of_topSectionData h_bunching data fixedSection hfixed
      predecessor)

/-- Infrastructure I.16a: the same source-facing top-section family also exposes
the orderwise holonomic certificate needed by fixed-jet realization.  This is a
projection bridge; all operator estimates and predecessor derivative equations
remain explicit in the inputs. -/
theorem metricFixedGraph_holonomicCertificate_of_topSectionData
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (data : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      LocalCutoff.GraphTransform.BoundedTopSectionOperatorData
        (X := X) (r - 1 + 1))
    (fixedSection : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu,
      BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X)))
    (hfixed : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu,
      (data r hr hrν).operator (fixedSection r hr hrν) = fixedSection r hr hrν)
    (predecessor : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu,
      LocalCutoff.GraphTransform.HolonomicTopSectionData (ζ : ℝ → X) r) :
    MetricFixedGraphHolonomicCertificate d ζ := by
  apply metricFixedGraph_holonomicCertificate_of_contraction_and_data
  intro r hr hrν
  exact metricContractionAndHolonomicData_of_topSectionData
    (data r hr hrν) (fixedSection r hr hrν) (hfixed r hr hrν)
    (predecessor r hr hrν)

end LocalInvariantGraph
