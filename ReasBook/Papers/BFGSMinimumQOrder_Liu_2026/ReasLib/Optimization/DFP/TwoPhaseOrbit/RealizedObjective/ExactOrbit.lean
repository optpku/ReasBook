/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Optimization/DFP/TwoPhaseOrbit/RealizedObjective/ExactOrbit.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.ExactOrbit
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.RealizedObjective.Interpolation
import Mathlib.Tactic.Abel

/-!
# Exact DFP orbits for realized objectives

Exact two-phase cycles and endpoint gradient interpolation identify the
flattened endpoint data as a classical inverse-form DFP orbit.
-/

public section

namespace DFP.TwoPhaseOrbit

/-- The realized objective, prescribed endpoint step lengths, endpoints,
gradients, and inverse Hessians of an exact two-phase orbit satisfy the
classical inverse-form DFP recurrence. -/
theorem realizedObjective_isOrbit (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j))
    (h_radius : ∀ n : ℕ, 0 < orbit.interpolationRadius C G n)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n))) :
    DFP.IsOrbit (orbit.realizedObjective C G) (orbit.endpointStepLength h_exact)
      orbit.endpoint orbit.endpointGradient orbit.endpointMetric := by
  apply isOrbit_of_exactCycles orbit h_exact
  intro k
  have hk := realizedObjective_hasGradientAt_endpoint orbit C G
    h_radius h_disjoint k
  have heq : orbit.endpoint k - C + orbit.endpointCorrection C k =
      orbit.endpointGradient k := by
    rw [endpointCorrection_def]
    abel
  rw [heq] at hk
  exact hk

end DFP.TwoPhaseOrbit
