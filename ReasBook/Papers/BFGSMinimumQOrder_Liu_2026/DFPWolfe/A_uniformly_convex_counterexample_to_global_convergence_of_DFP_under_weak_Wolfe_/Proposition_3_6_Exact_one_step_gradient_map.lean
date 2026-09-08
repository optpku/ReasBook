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
