/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Analysis/Calculus/LocalInvariantGraph/ExplicitContraction/MetricHolonomicFixedSectionBridge.lean
-/

module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiniteSmooth
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicTopSectionCertificate

public section

noncomputable section

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Infrastructure I.16a: a family of holonomic graph-jet fixed-section
certificates projects directly to the metric fixed-graph holonomicity
interface; the operator and predecessor obligations remain in the inputs. -/
theorem metricFixedGraph_holonomicCertificate_of_holonomicFixedTopSectionCertificates
    [CompleteSpace X]
    {d : MetricGraphTransformData X}
    {ζ : SmallLipschitzGraph X d.radius d.slope}
    (certificates : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      LocalCutoff.GraphTransform.HolonomicFixedTopSectionCertificate r (ζ : ℝ → X)) :
    MetricFixedGraphHolonomicCertificate d ζ := by
  refine ⟨fun r hr hrν ↦ ?_⟩
  let certificate := certificates r hr hrν
  exact ⟨fun u ↦ certificate.fixedSection u,
    certificate.fixedSection.continuous, certificate.fixedSection_derivative⟩

end LocalInvariantGraph
