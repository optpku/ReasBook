/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Proposition_5_14_The_realized_endpoint_sequence_is_the_exact_classical_DFP_orbit.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.RealizedObjective.ExactOrbit

public section

/- Proposition 5.14 (The realized endpoint sequence is the exact classical DFP orbit):
the realized objective, prescribed positive step lengths, endpoints, gradients,
and inverse Hessians satisfy the classical inverse-form DFP recurrence. -/
#check (DFP.TwoPhaseOrbit.realizedObjective_isOrbit :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_exact : ∀ j, DFP.TwoPhaseOrbit.State.ExactCycle (orbit.state j)),
    (∀ n : ℕ, 0 < orbit.interpolationRadius C G n) →
    Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)) →
    DFP.IsOrbit (orbit.realizedObjective C G) (orbit.endpointStepLength h_exact)
      orbit.endpoint orbit.endpointGradient orbit.endpointMetric)
