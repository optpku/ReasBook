module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowGraph
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Transport along fifth-order graph jets

The main theorem transfers fifth-order agreement of state-space paths through
an arbitrary continuously differentiable observable.  This is the common
analytic step used by scalar and vector observable specializations.
-/

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- The canonical polynomial slow-graph path converges to the canceled base
state. -/
theorem slowGraphJetPath_tendsto :
    Tendsto slowGraphJetPath (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
  have hpath : slowGraphJetPath =
      (fun ε : ℝ ↦
        (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
          1 + 8 * ε ^ 3)) := by
    funext ε
    exact slowGraphJetPath_apply ε
  rw [hpath]
  have hcontinuous : ContinuousAt
      (fun ε : ℝ ↦
        (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
          1 + 8 * ε ^ 3)) 0 := by
    fun_prop
  convert hcontinuous.tendsto using 1
  norm_num

namespace SlowGraph

/-- A strict derivative transports fifth-order agreement with the polynomial
slow graph through a normed-space-valued map. -/
theorem map_sub_map_jet_isBigO_of_hasStrictFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (graph : SlowGraph) {f : ℝ × ℝ × ℝ → E}
    {f' : (ℝ × ℝ × ℝ) →L[ℝ] E}
    (hf : HasStrictFDerivAt f f' ((0, 2, 1) : ℝ × ℝ × ℝ)) :
    (fun ε : ℝ ↦ f (graph.path ε) - f (slowGraphJetPath ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
  have hpairs :
      Tendsto (fun ε ↦ (graph.path ε, slowGraphJetPath ε)) (𝓝 0)
        (𝓝 (((0, 2, 1), (0, 2, 1)) :
          (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ))) := by
    simpa only [nhds_prod_eq] using
      graph.path_tendsto.prodMk slowGraphJetPath_tendsto
  have hcomposed := hf.isBigO_sub.comp_tendsto hpairs
  have hmapDifference :
      (fun ε ↦ f (graph.path ε) - f (slowGraphJetPath ε)) =O[𝓝 0]
        (fun ε ↦ graph.path ε - slowGraphJetPath ε) := by
    simpa only [Function.comp_def] using hcomposed
  exact hmapDifference.trans graph.path_sub_jet_isBigO

/-- A continuously differentiable map transports fifth-order agreement with
the polynomial slow graph through a normed-space-valued observable. -/
theorem map_sub_map_jet_isBigO
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (graph : SlowGraph) {f : ℝ × ℝ × ℝ → E}
    (hf : ContDiffAt ℝ 1 f ((0, 2, 1) : ℝ × ℝ × ℝ)) :
    (fun ε : ℝ ↦ f (graph.path ε) - f (slowGraphJetPath ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
  exact graph.map_sub_map_jet_isBigO_of_hasStrictFDerivAt
    (hf.hasStrictFDerivAt one_ne_zero)

end SlowGraph

end DFP.TwoLeg
