/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_5_1_Isolation_radii_and_pairwise_disjoint_interpolation_balls_Isolation.lean
-/

module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_4_8b_Limiting_circle_and_endpoint_closed_set_candidate_EndpointSet
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointIsolation

public section

noncomputable section

namespace DFP.TwoPhaseOrbit

#check (DFP.TwoPhaseOrbit.isolationDistance :
  DFP.TwoPhaseOrbit → EuclideanSpace ℝ (Fin 2) → ℝ → ℕ → ℝ)

#check (DFP.TwoPhaseOrbit.isolationDistance_def :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ),
    orbit.isolationDistance C G k = Metric.infDist (orbit.endpoint k)
      (orbit.closedSetCandidate C G \ {orbit.endpoint k}))

#check (DFP.TwoPhaseOrbit.interpolationRadius :
  DFP.TwoPhaseOrbit → EuclideanSpace ℝ (Fin 2) → ℝ → ℕ → ℝ)

#check (DFP.TwoPhaseOrbit.interpolationRadius_def :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ),
    orbit.interpolationRadius C G k = Metric.infDist (orbit.endpoint k)
      (orbit.closedSetCandidate C G \ {orbit.endpoint k}) / 4)

end DFP.TwoPhaseOrbit
