module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderwiseCertificateAssembly
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicTopSectionCertificate

public section

noncomputable section

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-!
This module is the canonical-section boundary for the finite-smooth metric bootstrap.
Source calculations need only provide a contracted top-section operator and the derivative
equation for its canonical fixed section.  The fixed section itself is then selected by the
bounded-section contraction API, so downstream certificates do not duplicate that choice.
-/

/-- Infrastructure I.16a: source-facing orderwise data consists of a bounded contraction
operator at each order together with the predecessor derivative equation for its canonical
fixed section.  The strict contraction selects the section; the derivative equation remains
an explicit source obligation. -/
structure MetricCanonicalOrderwiseCertificate
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) : Type u where
  operators : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
    LocalCutoff.GraphTransform.BoundedTopSectionOperatorData
      (X := X) (r - 1 + 1)
  predecessorDerivative : ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ hrν : r ≤ d.nu, ∀ u,
    HasFDerivAt
      (fun y ↦ (ftaylorSeries ℝ (ζ : ℝ → X) y) (r - 1))
      ((LocalCutoff.GraphTransform.canonicalFixedTopSection
        (operators r hr hrν) u).curryLeft) u

/-- Helper for Infrastructure I.16a: canonical contracted sections and their predecessor
derivative equations assemble into the orderwise metric contraction-and-holonomicity package. -/
noncomputable def MetricCanonicalOrderwiseCertificate.orderData
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (certificate : MetricCanonicalOrderwiseCertificate d ζ) :
    ∀ r : ℕ, 1 ≤ r → r ≤ d.nu → MetricContractionAndHolonomicData d ζ r :=
  fun r hr hrν ↦
    let data := certificate.operators r hr hrν
    let fixed := LocalCutoff.GraphTransform.canonicalFixedTopSection data
    { operator := data.operator
      contraction :=
        { contractionFactor := data.contractionFactor
          contractionFactor_lt_one := data.contractionFactor_lt_one
          dist_apply_le := data.dist_apply_le }
      fixedSection := fixed
      fixedSection_is_fixed :=
        LocalCutoff.GraphTransform.canonicalFixedTopSection_is_fixed data
      predecessor :=
        { value := fun u ↦ fixed u
          continuous_value := fixed.continuous
          derivative := certificate.predecessorDerivative r hr hrν }
    }

/-- Helper for Infrastructure I.16a: each canonical contracted operator yields the holonomic
fixed-top-section certificate consumed by graph-jet realization. -/
noncomputable def MetricCanonicalOrderwiseCertificate.holonomicTopSectionCertificates
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (certificate : MetricCanonicalOrderwiseCertificate d ζ) :
    ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      LocalCutoff.GraphTransform.HolonomicFixedTopSectionCertificate r (ζ : ℝ → X) :=
  fun r hr hrν ↦ LocalCutoff.GraphTransform.canonicalHolonomicFixedTopSectionCertificate
    (certificate.operators r hr hrν)
    (certificate.predecessorDerivative r hr hrν)

/-- Infrastructure I.16a: canonical orderwise operator data directly produces the holonomic
fixed-graph certificate, while retaining the source predecessor equations in the result. -/
theorem MetricCanonicalOrderwiseCertificate.toHolonomicCertificate
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (certificate : MetricCanonicalOrderwiseCertificate d ζ) :
    MetricFixedGraphHolonomicCertificate d ζ := by
  exact metricFixedGraph_holonomicCertificate_of_contraction_and_data certificate.orderData

/-- Helper for Infrastructure I.16a: adding the finite-order bunching inequalities turns
canonical orderwise operator data into the structured metric regularity assembly. -/
noncomputable def MetricCanonicalOrderwiseCertificate.toOrderwiseAssembly
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (certificate : MetricCanonicalOrderwiseCertificate d ζ)
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1) :
    MetricOrderwiseCertificateAssembly d ζ :=
  { bunching := h_bunching
    orderData := certificate.orderData }

/-- Infrastructure I.16a: canonical orderwise contraction and predecessor data, together with
the explicit bunching inequalities, yield finite smoothness of the metric fixed graph. -/
theorem MetricCanonicalOrderwiseCertificate.contDiff
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (certificate : MetricCanonicalOrderwiseCertificate d ζ)
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1) :
    ContDiff ℝ d.nu (ζ : ℝ → X) := by
  exact certificate.toOrderwiseAssembly h_bunching |>.contDiff

end LocalInvariantGraph
