module

public import ReasLib.Optimization.DFP.AbstractSecantStep.ExactUpdate

open scoped Matrix

universe u

/- Proposition 3.7 (Exact one-step DFP matrix map) (1): exact rank-two formula. -/
#check (DFP.AbstractSecantStep.nextInverseHessian_formula :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n),
    let v := z.preconditionedGradient
    let w := z.secantMatrix *ᵥ v
    let β := v ⬝ᵥ w
    let γ := w ⬝ᵥ (z.inverseHessian *ᵥ w)
    z.nextInverseHessian =
      z.inverseHessian -
        γ⁻¹ • Matrix.vecMulVec (z.inverseHessian *ᵥ w) (w ᵥ* z.inverseHessian) +
        β⁻¹ • Matrix.vecMulVec v v)

/- Proposition 3.7 (Exact one-step DFP matrix map) (2): independence of `τ`. -/
#check (DFP.AbstractSecantStep.nextInverseHessian_tau_independent :
  ∀ {n : Type u} [Fintype n] (z₁ z₂ : DFP.AbstractSecantStep n),
    z₁.inverseHessian = z₂.inverseHessian →
    z₁.gradient = z₂.gradient →
    z₁.secantMatrix = z₂.secantMatrix →
    z₁.nextInverseHessian = z₂.nextInverseHessian)
