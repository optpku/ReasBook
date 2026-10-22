/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Proposition_3_6_Exact_one_step_gradient_map.lean
-/

module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_2a_Positivity_and_well_definedness_of_one_abstract_secant_step

public section

open scoped Matrix

namespace DFP.AbstractSecantStep

/- Proposition 3.6 (Exact one-step gradient map): writing `v = Hg`,
`δ = gᵀv`, `w = Av`, and `β = vᵀw`, the next gradient has the exact update
formula `g₊ = g - (τ * δ / β) • w`. -/
#check (DFP.AbstractSecantStep.nextGradient_formula :
  ∀ {n : Type*} [Fintype n] (z : DFP.AbstractSecantStep n),
    let v := z.preconditionedGradient
    let δ := z.gradient ⬝ᵥ v
    let w := z.secantMatrix *ᵥ v
    let β := v ⬝ᵥ w
    z.nextGradient = z.gradient - (z.tau * δ / β) • w)

end DFP.AbstractSecantStep
