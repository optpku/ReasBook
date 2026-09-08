module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.RealizedObjective.Interpolation
import ReasLib.Optimization.DFP.DecreaseRatio
import Mathlib.Tactic.Abel

public section

namespace DFP.TwoPhaseOrbit

/-- The normalized decrease of the realized objective along an endpoint step is
the translated quadratic contribution plus the endpoint-correction contribution. -/
theorem realizedObjective_decreaseRatio (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ n : ℕ, 0 < orbit.interpolationRadius C G n)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)))
    (k : ℕ) :
    let s := orbit.endpoint (k + 1) - orbit.endpoint k
    let q := -inner ℝ (orbit.endpointGradient k) s
    0 < q →
      (orbit.realizedObjective C G (orbit.endpoint k) -
          orbit.realizedObjective C G (orbit.endpoint (k + 1))) / q =
        1 - ‖s‖ ^ 2 / (2 * q) + inner ℝ (orbit.endpointCorrection C k) s / q := by
  have hgradient : orbit.endpoint k - C =
      orbit.endpointGradient k - orbit.endpointCorrection C k := by
    rw [endpointCorrection_def]
    abel
  exact DFP.decreaseRatio_eq_one_sub_normSq_add_correction
    (orbit.realizedObjective C G) C (orbit.endpoint k) (orbit.endpoint (k + 1))
    (orbit.endpointGradient k) (orbit.endpointCorrection C k)
    (realizedObjective_endpoint orbit C G h_radius h_disjoint k)
    (realizedObjective_endpoint orbit C G h_radius h_disjoint (k + 1))
    hgradient

end DFP.TwoPhaseOrbit
