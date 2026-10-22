/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_4_8b1_The_limiting_circle_is_compact_and_closed.lean
-/

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
