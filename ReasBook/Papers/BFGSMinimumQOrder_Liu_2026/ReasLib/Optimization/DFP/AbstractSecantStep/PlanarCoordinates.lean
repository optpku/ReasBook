module

public import ReasLib.Optimization.DFP.AbstractSecantStep.Eigenframe

public section

/-!
# Planar coordinate adapters for abstract DFP steps

This module names the coordinate expressions used by the two-dimensional appendix.  The
underlying update remains the generic `AbstractSecantStep` update; this file only provides a
small, reusable projection interface for the special matrix `A(μ)`.
-/

noncomputable section

universe u

open scoped Matrix

namespace DFP.AbstractSecantStep.Planar

/-- Coordinates for a diagonal inverse Hessian, a gradient, and the control `A(μ)`. -/
structure Coordinates where
  ell : ℝ
  eta : ℝ
  g₁ : ℝ
  g₂ : ℝ
  μ : ℝ

/-- The symmetric secant control `A(μ) = [[1, μ], [μ, 1]]`. -/
def control (μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, μ; μ, 1]

/-- The diagonal inverse-Hessian action on the coordinate gradient. -/
def v (q : Coordinates) : Fin 2 → ℝ :=
  ![q.ell * q.g₁, q.eta * q.g₂]

/-- The secant image of the preconditioned gradient under `A(μ)`. -/
def w (q : Coordinates) : Fin 2 → ℝ :=
  control q.μ *ᵥ v q

/-- The gradient-energy scalar `δ = gᵀv`. -/
def delta (q : Coordinates) : ℝ :=
  q.g₁ * v q 0 + q.g₂ * v q 1

/-- The secant-energy scalar `β = vᵀw`. -/
def beta (q : Coordinates) : ℝ :=
  v q 0 * w q 0 + v q 1 * w q 1

/-- The metric-energy scalar `γ = wᵀHw` in diagonal coordinates. -/
def gamma (q : Coordinates) : ℝ :=
  q.ell * (w q 0) ^ 2 + q.eta * (w q 1) ^ 2

/-- The coordinate formula for the secant image. -/
theorem w_apply (q : Coordinates) :
    w q = ![q.ell * q.g₁ + q.μ * (q.eta * q.g₂),
      q.μ * (q.ell * q.g₁) + q.eta * q.g₂] := by
  ext i
  fin_cases i
  · simp [w, control, v, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [w, control, v, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The control matrix is Hermitian over the real coordinate space. -/
theorem control_isHermitian (μ : ℝ) : (control μ).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [control]

/-- A planar abstract step with these coordinate equations has the displayed next gradient. -/
theorem nextGradient_eq (z : AbstractSecantStep (Fin 2)) (q : Coordinates)
    (hH : z.inverseHessian = Matrix.diagonal ![q.ell, q.eta])
    (hg : z.gradient = ![q.g₁, q.g₂])
    (hA : z.secantMatrix = control q.μ) :
    z.nextGradient =
      ![q.g₁ - z.tau * delta q / beta q * w q 0,
        q.g₂ - z.tau * delta q / beta q * w q 1] := by
  simpa [control, v, w, delta, beta, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
    z.nextGradient_eigenframe q.ell q.eta q.g₁ q.g₂ 1 q.μ 1 hH hg hA

/-- A planar abstract step with these coordinate equations has the displayed next inverse Hessian.
-/
theorem nextInverseHessian_eq (z : AbstractSecantStep (Fin 2)) (q : Coordinates)
    (hH : z.inverseHessian = Matrix.diagonal ![q.ell, q.eta])
    (hg : z.gradient = ![q.g₁, q.g₂])
    (hA : z.secantMatrix = control q.μ) :
    z.nextInverseHessian =
      !![q.ell - q.ell ^ 2 * (w q 0) ^ 2 / gamma q + (v q 0) ^ 2 / beta q,
          -(q.ell * q.eta * (w q 0) * (w q 1) / gamma q) +
            (v q 0) * (v q 1) / beta q;
        -(q.ell * q.eta * (w q 0) * (w q 1) / gamma q) +
            (v q 0) * (v q 1) / beta q,
          q.eta - q.eta ^ 2 * (w q 1) ^ 2 / gamma q + (v q 1) ^ 2 / beta q] := by
  simpa [control, v, w, beta, gamma, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
    z.nextInverseHessian_eigenframe q.ell q.eta q.g₁ q.g₂ 1 q.μ 1 hH hg hA

end DFP.AbstractSecantStep.Planar
