module

public import ReasLib.Optimization.DFP.AbstractSecantStep.Eigenframe

open scoped Matrix

/- Appendix Lemma A.1 (Entrywise one-step formulas) (1): in coordinates where
`H = Matrix.diagonal ![ell, eta]`, `g = ![g₁, g₂]`, and `A = !![a, c; c, d]`,
the next inverse-Hessian has the displayed symmetric entrywise formula. -/
#check (DFP.AbstractSecantStep.nextInverseHessian_eigenframe :
  ∀ (z : DFP.AbstractSecantStep (Fin 2)) (ell eta g₁ g₂ a c d : ℝ),
    z.inverseHessian = Matrix.diagonal ![ell, eta] →
    z.gradient = ![g₁, g₂] →
    z.secantMatrix = !![a, c; c, d] →
    let v₁ := ell * g₁
    let v₂ := eta * g₂
    let w₁ := a * v₁ + c * v₂
    let w₂ := c * v₁ + d * v₂
    let β := v₁ * w₁ + v₂ * w₂
    let γ := ell * w₁ ^ 2 + eta * w₂ ^ 2
    z.nextInverseHessian =
      !![ell - ell ^ 2 * w₁ ^ 2 / γ + v₁ ^ 2 / β,
          -(ell * eta * w₁ * w₂ / γ) + v₁ * v₂ / β;
        -(ell * eta * w₁ * w₂ / γ) + v₁ * v₂ / β,
          eta - eta ^ 2 * w₂ ^ 2 / γ + v₂ ^ 2 / β])

/- Appendix Lemma A.1 (Entrywise one-step formulas) (2): in the same diagonal
coordinates, the next gradient is obtained from the displayed formulas for
`v`, `w`, `δ`, and `β`. -/
#check (DFP.AbstractSecantStep.nextGradient_eigenframe :
  ∀ (z : DFP.AbstractSecantStep (Fin 2)) (ell eta g₁ g₂ a c d : ℝ),
    z.inverseHessian = Matrix.diagonal ![ell, eta] →
    z.gradient = ![g₁, g₂] →
    z.secantMatrix = !![a, c; c, d] →
    let v₁ := ell * g₁
    let v₂ := eta * g₂
    let w₁ := a * v₁ + c * v₂
    let w₂ := c * v₁ + d * v₂
    let δ := g₁ * v₁ + g₂ * v₂
    let β := v₁ * w₁ + v₂ * w₂
    z.nextGradient =
      ![g₁ - z.tau * δ / β * w₁, g₂ - z.tau * δ / β * w₂])
