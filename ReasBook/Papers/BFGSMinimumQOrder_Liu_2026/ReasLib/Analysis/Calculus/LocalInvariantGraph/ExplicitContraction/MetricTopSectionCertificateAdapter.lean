module

-- Source-facing adapter for the finite-order metric bootstrap.  The derivative core is kept
-- explicit: bunching and a fixed-point equation alone do not provide the predecessor derivatives.
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionDerivativeBridge
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiniteSmooth
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicTopSection

public section

noncomputable section

open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Infrastructure I.16a: a scalar top-jet derivative supplied by the metric core is packaged as
the multilinear holonomic top-section witness at one positive order. -/
theorem metricFixedGraph_topSectionWitness_of_core
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hcore : MetricTopSectionCore d ζ)
    {r : ℕ} (hr : 1 ≤ r) (hrν : r ≤ d.nu) :
    ∃ a : ℝ → (ℝ [×(r - 1 + 1)]→L[ℝ] X),
      Continuous a ∧
        ∀ u, HasFDerivAt
          (fun y ↦ (ftaylorSeries ℝ (ζ : ℝ → X) y) (r - 1))
          ((a u).curryLeft) u := by
  exact topSectionWitness_at_of_core d ζ hcore hr hrν

/-- Infrastructure I.16a: an explicit metric top-section core supplies both finite smoothness and
the holonomic witness at every order in the declared range. -/
theorem metricFixedGraph_contDiff_and_topSection_of_core
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hcore : MetricTopSectionCore d ζ) :
    ∀ r : ℕ, r ≤ d.nu →
      ContDiff ℝ r (ζ : ℝ → X) ∧
        (1 ≤ r → ∃ a : ℝ → (ℝ [×(r - 1 + 1)]→L[ℝ] X),
          Continuous a ∧
            ∀ u, HasFDerivAt
              (fun y ↦ (ftaylorSeries ℝ (ζ : ℝ → X) y) (r - 1))
              ((a u).curryLeft) u) := by
  intro r hrν
  have hcont : ContDiff ℝ r (ζ : ℝ → X) :=
    contDiff_le_of_core d ζ hcore r hrν
  refine ⟨hcont, ?_⟩
  intro hr
  exact metricFixedGraph_topSectionWitness_of_core d ζ hcore hr hrν

/-- Infrastructure I.16a: the core projection exposes the orderwise top-section field needed by
downstream metric holonomic certificates without reconstructing the finite-smooth induction. -/
theorem metricFixedGraph_topSection_of_core_adapter
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hcore : MetricTopSectionCore d ζ) :
    ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      ∃ a : ℝ → (ℝ [×(r - 1 + 1)]→L[ℝ] X),
        Continuous a ∧
          ∀ u, HasFDerivAt
            (fun y ↦ (ftaylorSeries ℝ (ζ : ℝ → X) y) (r - 1))
            ((a u).curryLeft) u := by
  intro r hr hrν
  exact metricFixedGraph_topSectionWitness_of_core d ζ hcore hr hrν

/-- Helper for Infrastructure I.16a: an orderwise family of fixed graph jet contexts
projects to the existential metric holonomic certificate at every declared order. -/
theorem metricFixedGraph_holonomicCertificate_of_fixedGraphJetContexts
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (contexts : ∀ m : ℕ, m < d.nu →
      ContDiff ℝ m (ζ : ℝ → X) →
        LocalCutoff.GraphTransform.FixedGraphJetContext (m + 1) (ζ : ℝ → X)) :
    MetricFixedGraphHolonomicCertificate d ζ := by
  have hcore : MetricTopSectionCore d ζ :=
    metricTopSectionCore_of_fixedGraphJetContexts d ζ contexts
  refine ⟨?_⟩
  intro r hr hrν
  exact metricFixedGraph_topSectionWitness_of_core d ζ hcore hr hrν

/-- Infrastructure I.16a: the fixed graph jet-context family directly yields finite
smoothness after its explicit predecessor derivative and contraction data have been supplied. -/
theorem metricFixedGraph_contDiff_of_fixedGraphJetContexts
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (contexts : ∀ m : ℕ, m < d.nu →
      ContDiff ℝ m (ζ : ℝ → X) →
        LocalCutoff.GraphTransform.FixedGraphJetContext (m + 1) (ζ : ℝ → X)) :
    ContDiff ℝ d.nu (ζ : ℝ → X) := by
  have hcertificate : MetricFixedGraphHolonomicCertificate d ζ :=
    metricFixedGraph_holonomicCertificate_of_fixedGraphJetContexts d ζ contexts
  exact metricFixedGraph_contDiff_of_holonomicCertificate d ζ hcertificate

end LocalInvariantGraph
