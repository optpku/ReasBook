module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionFacade

public section

noncomputable section

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Infrastructure I.16a: all source-specific data required to assemble a
finite-order metric regularity certificate.  In particular, this retains both
the orderwise section contractions and their holonomic predecessor equations;
bare bunching is not treated as a construction principle. -/
structure MetricOrderwiseCertificateAssembly
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) : Type u where
  bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
    (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
      (d.lower : ℝ)⁻¹ ^ r < 1
  orderData : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
    MetricContractionAndHolonomicData d ζ r

/-- Infrastructure I.16a: an orderwise assembly packages into the structured
finite-smooth certificate consumed by downstream regularity arguments. -/
noncomputable def MetricOrderwiseCertificateAssembly.toFiniteSmoothCertificate
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricOrderwiseCertificateAssembly d ζ) :
    MetricFiniteSmoothCertificate d ζ :=
  metricFiniteSmoothCertificate_of_contraction_and_data assembly.bunching assembly.orderData

/-- Infrastructure I.16a: an orderwise assembly projects to the holonomic
fixed-graph certificate independently of the bunching inequalities. -/
theorem MetricOrderwiseCertificateAssembly.toHolonomicCertificate
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricOrderwiseCertificateAssembly d ζ) :
    MetricFixedGraphHolonomicCertificate d ζ := by
  exact metricFixedGraph_holonomicCertificate_of_contraction_and_data assembly.orderData

/-- Infrastructure I.16a: a complete orderwise contraction-and-holonomicity
assembly yields the finite smoothness of the metric fixed graph. -/
theorem MetricOrderwiseCertificateAssembly.contDiff
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricOrderwiseCertificateAssembly d ζ) :
    ContDiff ℝ d.nu (ζ : ℝ → X) := by
  exact metricFixedGraph_contDiff_of_finiteSmoothCertificate
    assembly.toFiniteSmoothCertificate

/-- Infrastructure I.16a: the assembly also identifies the resulting top
sections with the iterated derivatives of the fixed graph. -/
theorem MetricOrderwiseCertificateAssembly.contDiff_and_topSections_eq_iteratedFDeriv
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (assembly : MetricOrderwiseCertificateAssembly d ζ) :
    ContDiff ℝ d.nu (ζ : ℝ → X) ∧
      ∀ (r : ℕ) (hr : 1 ≤ r) (hrν : r ≤ d.nu) (u : ℝ),
        (assembly.toFiniteSmoothCertificate.topSection r hr hrν).value u =
          iteratedFDeriv ℝ (r - 1 + 1) (ζ : ℝ → X) u := by
  exact metricFixedGraph_contDiff_and_topSections_eq_iteratedFDeriv
    assembly.toFiniteSmoothCertificate

end LocalInvariantGraph
