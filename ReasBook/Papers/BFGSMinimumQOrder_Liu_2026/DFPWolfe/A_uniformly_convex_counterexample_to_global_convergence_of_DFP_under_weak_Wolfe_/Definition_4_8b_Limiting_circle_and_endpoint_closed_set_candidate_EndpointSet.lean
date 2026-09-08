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
