module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Iteration

public section

namespace DFP.TwoPhaseOrbit

/- Lemma 6.6 (Positive definiteness of every DFP matrix): every inverse-Hessian
matrix in the flattened endpoint sequence is positive definite; `Matrix.PosDef`
also includes symmetry. -/
#check (endpointMetric_posDef :
  ∀ (orbit : DFP.TwoPhaseOrbit),
    (∀ j, State.ExactCycle (orbit.state j)) →
      ∀ k : ℕ, (orbit.endpointMetric k).PosDef)

end DFP.TwoPhaseOrbit
