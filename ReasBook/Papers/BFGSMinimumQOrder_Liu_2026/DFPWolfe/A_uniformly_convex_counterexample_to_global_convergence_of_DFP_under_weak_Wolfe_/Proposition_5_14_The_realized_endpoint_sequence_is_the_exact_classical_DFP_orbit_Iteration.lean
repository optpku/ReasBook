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
