module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.GradientNormSmoothness
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowGraph

/-!
# Gradient-norm observables along a slow graph

The normalized boundary and intermediate gradient norms both converge to one
along any graph with the prescribed fifth-order slow-graph asymptotics.
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- The normalized initial-gradient norm is one at the slow-graph base state. -/
@[simp] theorem initialGradientNorm_at_slowGraphBase :
    (observableMap ((0, 2, 1) : ℝ × ℝ × ℝ)).initialGradientNorm = 1 := by
  have hnorms := congrArg Prod.fst (observableMap_gradientNorms 0 2 1)
  simp only [] at hnorms
  rw [hnorms]
  norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- The normalized intermediate-gradient norm is one at the slow-graph base state. -/
@[simp] theorem intermediateGradientNorm_at_slowGraphBase :
    (observableMap ((0, 2, 1) : ℝ × ℝ × ℝ)).intermediateGradientNorm = 1 := by
  have hnorms := congrArg (fun norms ↦ norms.2.1) (observableMap_gradientNorms 0 2 1)
  simp only [] at hnorms
  rw [hnorms]
  rw [DFP.FirstLeg.outputGradient_apply]
  norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]

namespace SlowGraph

/-- The initial and intermediate normalized-gradient norms converge jointly to
`(1, 1)` along a slow graph. -/
theorem gradientNorms_tendsto (graph : SlowGraph) :
    Tendsto (fun ε ↦
      ((observableMap (graph.path ε)).initialGradientNorm,
        (observableMap (graph.path ε)).intermediateGradientNorm))
      (𝓝 0) (𝓝 ((1, 1) : ℝ × ℝ)) := by
  have hInitial :=
    (initialGradientNorm_contDiffAt 0).continuousAt.tendsto.comp graph.path_tendsto
  have hIntermediate :=
    (intermediateGradientNorm_contDiffAt 0).continuousAt.tendsto.comp graph.path_tendsto
  simpa only [Function.comp_apply, initialGradientNorm_at_slowGraphBase,
    intermediateGradientNorm_at_slowGraphBase, nhds_prod_eq] using
    hInitial.prodMk hIntermediate

/-- Every open interval containing one eventually contains both normalized
gradient norms along a slow graph. -/
theorem eventually_gradientNorms_mem_Icc (graph : SlowGraph) {a b : ℝ}
    (ha : a < 1) (hb : 1 < b) :
    ∀ᶠ ε in 𝓝 (0 : ℝ),
      (observableMap (graph.path ε)).initialGradientNorm ∈ Set.Icc a b ∧
        (observableMap (graph.path ε)).intermediateGradientNorm ∈ Set.Icc a b := by
  have hPair := graph.gradientNorms_tendsto
  have hInitial : Tendsto
      (fun ε ↦ (observableMap (graph.path ε)).initialGradientNorm)
      (𝓝 0) (𝓝 1) := by
    simpa only [Function.comp_def] using
      (continuous_fst.tendsto ((1, 1) : ℝ × ℝ)).comp hPair
  have hIntermediate : Tendsto
      (fun ε ↦ (observableMap (graph.path ε)).intermediateGradientNorm)
      (𝓝 0) (𝓝 1) := by
    simpa only [Function.comp_def] using
      (continuous_snd.tendsto ((1, 1) : ℝ × ℝ)).comp hPair
  filter_upwards [hInitial.eventually (Ioo_mem_nhds ha hb),
    hIntermediate.eventually (Ioo_mem_nhds ha hb)] with ε hi hm
  exact ⟨⟨hi.1.le, hi.2.le⟩, ⟨hm.1.le, hm.2.le⟩⟩

end SlowGraph
end DFP.TwoLeg
