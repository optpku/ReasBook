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
