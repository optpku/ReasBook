/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Optimization/DFP/TwoPhaseOrbit/EndpointGradientLimit/Basic.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowGraph

public section

noncomputable section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- The fifth-order slow-graph remainders force the parameter path to converge
to the canceled base state `(0, 2, 1)`. This is the unbundled compatibility
wrapper for `DFP.TwoLeg.SlowGraph.path_tendsto`. -/
theorem slowGraphPath_tendsto (p h : ℝ → ℝ)
    (h_pJet : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    Tendsto (fun ε : ℝ ↦ (ε, p ε, h ε)) (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
  let graph := DFP.TwoLeg.SlowGraph.ofAsymptotics p h h_pJet h_hJet
  have hpath : graph.path = fun ε : ℝ ↦ (ε, p ε, h ε) := by
    funext ε
    rw [DFP.TwoLeg.SlowGraph.path_apply]
    simp only [graph, DFP.TwoLeg.SlowGraph.ofAsymptotics_shape,
      DFP.TwoLeg.SlowGraph.ofAsymptotics_high]
  rw [← hpath]
  exact graph.path_tendsto

end DFP.TwoPhaseOrbit
