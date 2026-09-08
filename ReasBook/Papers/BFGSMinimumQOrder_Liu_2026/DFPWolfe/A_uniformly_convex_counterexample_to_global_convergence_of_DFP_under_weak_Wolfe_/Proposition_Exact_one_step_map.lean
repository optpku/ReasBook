module

import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_2a_Positivity_and_well_definedness_of_one_abstract_secant_step
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Proposition_3_6_Exact_one_step_gradient_map
import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Proposition_3_7_Exact_one_step_DFP_matrix_map

open scoped Matrix

public section

/- Proposition (Exact one-step map) (1): the exact gradient update. -/
#check DFP.AbstractSecantStep.nextGradient_formula

/- Proposition (Exact one-step map) (2): writing `v = Hg`, `w = Av`,
`β = vᵀw`, and `γ = wᵀHw`, the next inverse-Hessian matrix has the exact
rank-two DFP update formula. -/
#check DFP.AbstractSecantStep.nextInverseHessian_formula

/- Proposition (Exact one-step map) (3): positivity of `β = (Hg)ᵀA(Hg)`. -/
#check DFP.AbstractSecantStep.preconditionedEnergy_pos

/- Proposition (Exact one-step map) (4): positivity of `γ = (AHg)ᵀH(AHg)`. -/
#check DFP.AbstractSecantStep.secantImageEnergy_pos

/- Proposition (Exact one-step map) (5): the inverse-Hessian update is
independent of the positive scale parameter `τ`. -/
#check DFP.AbstractSecantStep.nextInverseHessian_tau_independent
