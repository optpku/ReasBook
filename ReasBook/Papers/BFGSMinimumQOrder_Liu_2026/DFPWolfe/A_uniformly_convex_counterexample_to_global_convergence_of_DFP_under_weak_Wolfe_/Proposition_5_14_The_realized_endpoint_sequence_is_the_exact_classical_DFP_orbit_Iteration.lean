/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Proposition_5_14_The_realized_endpoint_sequence_is_the_exact_classical_DFP_orbit_Iteration.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Iteration

public section

-- Source-facing checks for the canonical flattened endpoint data used in Proposition 5.14.
#check (DFP.TwoPhaseOrbit.endpointMetric :
  DFP.TwoPhaseOrbit → ℕ → Matrix (Fin 2) (Fin 2) ℝ)

#check (DFP.TwoPhaseOrbit.endpointMetric_even :
  ∀ (orbit : DFP.TwoPhaseOrbit) (j : ℕ),
    orbit.endpointMetric (2 * j) = (orbit.state j).metric)

#check (DFP.TwoPhaseOrbit.endpointMetric_odd :
  ∀ (orbit : DFP.TwoPhaseOrbit) (j : ℕ),
    orbit.endpointMetric (2 * j + 1) = (orbit.state j).middleMetric)

#check (DFP.TwoPhaseOrbit.endpointStepLength :
  (orbit : DFP.TwoPhaseOrbit) →
    (∀ j, DFP.TwoPhaseOrbit.State.ExactCycle (orbit.state j)) → ℕ → ℝ)

#check (DFP.TwoPhaseOrbit.endpointStepLength_even :
  ∀ (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, DFP.TwoPhaseOrbit.State.ExactCycle (orbit.state j)) (j : ℕ),
    orbit.endpointStepLength h_exact (2 * j) = ((h_exact j).step 0).stepLength)

#check (DFP.TwoPhaseOrbit.endpointStepLength_odd :
  ∀ (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, DFP.TwoPhaseOrbit.State.ExactCycle (orbit.state j)) (j : ℕ),
    orbit.endpointStepLength h_exact (2 * j + 1) = ((h_exact j).step 1).stepLength)
