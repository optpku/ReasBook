module

public import ReasLib.Optimization.DFP.AbstractSecantStep.ExactUpdate

public section

open scoped Matrix

namespace DFP.AbstractSecantStep

/-- A diagonal inverse Hessian acts coordinatewise on a two-dimensional gradient. -/
private lemma preconditionedGradient_eigenframe (z : AbstractSecantStep (Fin 2))
    (ell eta g₁ g₂ : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![ell, eta])
    (hg : z.gradient = ![g₁, g₂]) :
    z.preconditionedGradient = ![ell * g₁, eta * g₂] := by
  -- Expose the matrix-vector product and evaluate each diagonal coordinate.
  rw [z.preconditionedGradient_def, hH, hg]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- A symmetric two-by-two secant matrix acts by the displayed coordinate formulas. -/
private lemma secantImage_eigenframe (z : AbstractSecantStep (Fin 2))
    (ell eta g₁ g₂ a c d : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![ell, eta])
    (hg : z.gradient = ![g₁, g₂])
    (hA : z.secantMatrix = !![a, c; c, d]) :
    z.secantMatrix *ᵥ z.preconditionedGradient =
      ![a * (ell * g₁) + c * (eta * g₂),
        c * (ell * g₁) + d * (eta * g₂)] := by
  -- Replace the abstract factors by their coordinate forms, then evaluate both rows.
  rw [hA, preconditionedGradient_eigenframe z ell eta g₁ g₂ hH hg]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- In a two-dimensional diagonal eigenframe, the next inverse-Hessian has the
displayed symmetric entrywise formula. -/
theorem nextInverseHessian_eigenframe (z : AbstractSecantStep (Fin 2))
    (ell eta g₁ g₂ a c d : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![ell, eta])
    (hg : z.gradient = ![g₁, g₂])
    (hA : z.secantMatrix = !![a, c; c, d]) :
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
          eta - eta ^ 2 * w₂ ^ 2 / γ + v₂ ^ 2 / β] := by
  -- Rewrite the rank-two update through the coordinate descriptions of `v` and `w`.
  dsimp only
  rw [z.nextInverseHessian_formula,
    secantImage_eigenframe z ell eta g₁ g₂ a c d hH hg hA,
    preconditionedGradient_eigenframe z ell eta g₁ g₂ hH hg, hH]
  -- Check the four matrix entries and normalize each scalar identity.
  ext i j
  fin_cases i
  · fin_cases j
    · simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Matrix.vecMulVec_apply, div_eq_mul_inv]
      ring
    · simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Matrix.vecMulVec_apply, div_eq_mul_inv]
      ring
  · fin_cases j
    · simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Matrix.vecMulVec_apply, div_eq_mul_inv]
      ring
    · simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Matrix.vecMulVec_apply, div_eq_mul_inv]
      ring

/-- In a two-dimensional diagonal eigenframe, the next gradient is obtained
from the coordinate formulas for the preconditioned gradient and its secant image. -/
theorem nextGradient_eigenframe (z : AbstractSecantStep (Fin 2))
    (ell eta g₁ g₂ a c d : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![ell, eta])
    (hg : z.gradient = ![g₁, g₂])
    (hA : z.secantMatrix = !![a, c; c, d]) :
    let v₁ := ell * g₁
    let v₂ := eta * g₂
    let w₁ := a * v₁ + c * v₂
    let w₂ := c * v₁ + d * v₂
    let δ := g₁ * v₁ + g₂ * v₂
    let β := v₁ * w₁ + v₂ * w₂
    z.nextGradient =
      ![g₁ - z.tau * δ / β * w₁, g₂ - z.tau * δ / β * w₂] := by
  -- Rewrite the exact gradient update using the same coordinate descriptions of `v` and `w`.
  dsimp only
  rw [z.nextGradient_formula,
    secantImage_eigenframe z ell eta g₁ g₂ a c d hH hg hA,
    preconditionedGradient_eigenframe z ell eta g₁ g₂ hH hg, hg]
  -- Evaluate the energy pairings coordinatewise and normalize the two results.
  ext i
  fin_cases i
  · simp [dotProduct, Fin.sum_univ_two, div_eq_mul_inv]
  · simp [dotProduct, Fin.sum_univ_two, div_eq_mul_inv]

end DFP.AbstractSecantStep
