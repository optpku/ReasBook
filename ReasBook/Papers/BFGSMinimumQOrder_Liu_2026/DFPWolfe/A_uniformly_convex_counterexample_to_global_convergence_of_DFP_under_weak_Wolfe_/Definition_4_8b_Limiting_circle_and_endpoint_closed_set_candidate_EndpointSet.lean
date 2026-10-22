/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Definition_4_8b_Limiting_circle_and_endpoint_closed_set_candidate_EndpointSet.lean
-/

module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_3_19b_Exact_infinite_abstract_two_phase_orbit_Orbit
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet

public section

noncomputable section

namespace DFP.TwoPhaseOrbit

#check (DFP.TwoPhaseOrbit.endpoint :
  DFP.TwoPhaseOrbit → ℕ → EuclideanSpace ℝ (Fin 2))
#check (DFP.TwoPhaseOrbit.endpoint_even :
  ∀ (orbit : DFP.TwoPhaseOrbit) (j : ℕ),
    orbit.endpoint (2 * j) = (orbit.state j).point)
#check (DFP.TwoPhaseOrbit.endpoint_odd :
  ∀ (orbit : DFP.TwoPhaseOrbit) (j : ℕ),
    orbit.endpoint (2 * j + 1) = (orbit.state j).middlePoint)
#check (DFP.TwoPhaseOrbit.limitCircle :
  EuclideanSpace ℝ (Fin 2) → ℝ → Set (EuclideanSpace ℝ (Fin 2)))
#check (DFP.TwoPhaseOrbit.mem_limitCircle :
  ∀ {C x : EuclideanSpace ℝ (Fin 2)} {G : ℝ},
    x ∈ DFP.TwoPhaseOrbit.limitCircle C G ↔
      ∃ v, ‖v‖ = 1 ∧ C + G • v = x)
#check (DFP.TwoPhaseOrbit.limitCircle_eq_sphere :
  ∀ (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ), 0 < G →
    DFP.TwoPhaseOrbit.limitCircle C G = Metric.sphere C G)
#check (DFP.TwoPhaseOrbit.isClosed_limitCircle :
  ∀ (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ), 0 < G →
    IsClosed (DFP.TwoPhaseOrbit.limitCircle C G))
#check (DFP.TwoPhaseOrbit.closedSetCandidate :
  DFP.TwoPhaseOrbit → EuclideanSpace ℝ (Fin 2) → ℝ →
    Set (EuclideanSpace ℝ (Fin 2)))
#check (DFP.TwoPhaseOrbit.mem_closedSetCandidate :
  ∀ {orbit : DFP.TwoPhaseOrbit} {C x : EuclideanSpace ℝ (Fin 2)} {G : ℝ},
    x ∈ orbit.closedSetCandidate C G ↔
      x ∈ DFP.TwoPhaseOrbit.limitCircle C G ∨ ∃ k : ℕ, orbit.endpoint k = x)
#check (DFP.TwoPhaseOrbit.isClosed_closedSetCandidate :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    0 < G →
      (∀ x, MapClusterPt x Filter.atTop orbit.endpoint →
        x ∈ DFP.TwoPhaseOrbit.limitCircle C G) →
      IsClosed (orbit.closedSetCandidate C G))

end DFP.TwoPhaseOrbit
