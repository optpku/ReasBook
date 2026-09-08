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
