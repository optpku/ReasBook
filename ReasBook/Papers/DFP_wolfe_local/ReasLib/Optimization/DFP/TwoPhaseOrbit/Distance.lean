/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet
import all ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet

public section

namespace DFP.TwoPhaseOrbit

/-- The distance to an affine unit-sphere limiting circle is its absolute radial deviation. -/
theorem infDist_limitCircle (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (hG : 0 < G)
    (x : EuclideanSpace ℝ (Fin 2)) :
    Metric.infDist x (limitCircle C G) = |‖x - C‖ - G| := by
  rw [limitCircle.eq_1]
  exact Metric.infDist_affinity_unitSphere x C G hG

end DFP.TwoPhaseOrbit
