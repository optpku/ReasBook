module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_3_19b_Exact_infinite_abstract_two_phase_orbit_Orbit
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.ExactCycle

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoPhaseOrbit

section

variable (orbit : DFP.TwoPhaseOrbit)
variable (h_exact : ∀ j, State.ExactCycle (orbit.state j))
variable (j : ℕ) (i : Fin 2)

/- Lemma 3.19c (Positive steps and well-definedness of the entire abstract DFP orbit):
every phase has positive step length. -/
#check (DFP.AbstractSecantStep.stepLength_pos ((h_exact j).step i) :
  0 < ((h_exact j).step i).stepLength)

#check (DFP.AbstractSecantStep.displacement_ne_zero ((h_exact j).step i) :
  ((h_exact j).step i).displacement ≠ 0)

#check (DFP.AbstractSecantStep.gradientChange_ne_zero ((h_exact j).step i) :
  ((h_exact j).step i).gradientChange ≠ 0)

#check (DFP.AbstractSecantStep.secantCurvature_pos ((h_exact j).step i) :
  0 < ((h_exact j).step i).secantCurvature)

#check (DFP.AbstractSecantStep.gradientChangeEnergy_pos ((h_exact j).step i) :
  let z := (h_exact j).step i
  0 < z.gradientChange ⬝ᵥ (z.inverseHessian *ᵥ z.gradientChange))

#check (DFP.AbstractSecantStep.preconditionedEnergy_pos ((h_exact j).step i) :
  let z := (h_exact j).step i
  0 < z.preconditionedGradient ⬝ᵥ
    (z.secantMatrix *ᵥ z.preconditionedGradient))

#check (DFP.AbstractSecantStep.inverseHessian_posDef ((h_exact j).step i) :
  ((h_exact j).step i).inverseHessian.PosDef)

#check (DFP.AbstractSecantStep.nextInverseHessian_posDef ((h_exact j).step i) :
  ((h_exact j).step i).nextInverseHessian.PosDef)

#check (DFP.TwoPhaseOrbit.State.ExactCycle.step_zero (h_exact j) :
  (h_exact j).step 0 = State.firstStep (orbit.state j) (h_exact j).valid)

#check (DFP.TwoPhaseOrbit.State.ExactCycle.step_one (h_exact j) :
  (h_exact j).step 1 = State.secondStep (orbit.state j) (h_exact j).valid)

#check (DFP.TwoPhaseOrbit.state_succ orbit j :
  orbit.state (j + 1) = (orbit.state j).next)

end

end DFP.TwoPhaseOrbit
