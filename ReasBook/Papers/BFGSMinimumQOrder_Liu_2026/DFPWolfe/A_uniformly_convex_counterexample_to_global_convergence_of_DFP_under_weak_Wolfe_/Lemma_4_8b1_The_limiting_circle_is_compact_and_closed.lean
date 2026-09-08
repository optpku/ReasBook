module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_4_8b_Limiting_circle_and_endpoint_closed_set_candidate_EndpointSet

public section

namespace DFP.TwoPhaseOrbit

/- Lemma 4.8b1 (The limiting circle is compact and closed) -/
#check (DFP.TwoPhaseOrbit.limitCircle_nonempty :
  ∀ (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ), 0 < G →
    (DFP.TwoPhaseOrbit.limitCircle C G).Nonempty)

/- Lemma 4.8b1 (The limiting circle is compact and closed) -/
#check (DFP.TwoPhaseOrbit.isCompact_limitCircle :
  ∀ (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ), 0 < G →
    IsCompact (DFP.TwoPhaseOrbit.limitCircle C G))

/- Lemma 4.8b1 (The limiting circle is compact and closed) -/
#check (DFP.TwoPhaseOrbit.isClosed_limitCircle :
  ∀ (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ), 0 < G →
    IsClosed (DFP.TwoPhaseOrbit.limitCircle C G))

end DFP.TwoPhaseOrbit
