module

public import ReasLib.Analysis.Asymptotics.UniformRemainder.Scalar
public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet.SlowGraphRemainder
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet.Transport

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

namespace SlowGraph

/-- On any fifth-order slow graph, the normalized amplitude ratio differs
from its quartic model by a fifth-order remainder. -/
theorem amplitudeRatio_sub_quartic_isBigO (graph : SlowGraph) :
    (fun ε : ℝ ↦
      (observableMap (graph.path ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
  have hstable := graph.map_sub_map_jet_isBigO
    (amplitudeRatio_contDiffAt 1)
  have hEightFive : (fun ε : ℝ ↦ ε ^ 8) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) :=
    (Asymptotics.isLittleO_pow_pow (by norm_num : 5 < 8)).isBigO
  have hgraph := slowGraphAmplitudeRemainderDirect.trans hEightFive
  have hSix : (fun ε : ℝ ↦ (116 / 5) * ε ^ 6) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) :=
    ((Asymptotics.isLittleO_pow_pow (by norm_num : 5 < 6)).isBigO).const_mul_left
      (116 / 5)
  have hSeven : (fun ε : ℝ ↦ -(976 / 5) * ε ^ 7) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) :=
    ((Asymptotics.isLittleO_pow_pow (by norm_num : 5 < 7)).isBigO).const_mul_left
      (-(976 / 5))
  have hsum := hstable.add (hgraph.add (hSix.add hSeven))
  exact hsum.congr_left (fun ε ↦ by ring)

end SlowGraph

/-- Along a graph with the prescribed slow-curve jets, the normalized amplitude-ratio
remainder after its fourth-order term is little-o of `ε ^ 4` at zero. -/
theorem slowCurveAmplitudeDriftLittleO (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4)) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) := by
  let graph := SlowGraph.ofAsymptotics p h h_pJet h_hJet
  have hFifth := graph.amplitudeRatio_sub_quartic_isBigO
  have hLittle := hFifth.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow (by norm_num : 4 < 5))
  simpa only [graph, SlowGraph.path_apply, SlowGraph.ofAsymptotics_shape,
    SlowGraph.ofAsymptotics_high] using hLittle

end DFP.TwoLeg
