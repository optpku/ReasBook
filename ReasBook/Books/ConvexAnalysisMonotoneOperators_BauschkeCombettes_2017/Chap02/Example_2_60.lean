/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open ContinuousLinearMap
open InnerProductSpace
open scoped Gradient InnerProductSpace

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The least-squares residual associated to a bounded operator `L` and target vector `r`. -/
def leastSquaresResidual (L : H →L[ℝ] K) (r : K) : H → ℝ :=
  fun y ↦ ‖L y - r‖ ^ 2

/-- Evaluating the least-squares residual gives the squared norm of `L y - r`. -/
-- Proof sketch: unfold `leastSquaresResidual`; the statement is the defining equation.
@[simp] theorem leastSquaresResidual_apply (L : H →L[ℝ] K) (r : K) (y : H) :
    leastSquaresResidual L r y = ‖L y - r‖ ^ 2 := by
  -- This is exactly the defining formula of `leastSquaresResidual`.
  rfl

/-- Example 2.60: the least-squares residual `y ↦ ‖L y - r‖^2` is twice Fréchet differentiable on
`H`. The next two companion statements record its gradient and Hessian formulas in mathlib's
Fréchet-derivative language. -/
-- Proof sketch: write `leastSquaresResidual L r` as the squared norm of the affine map
-- `y ↦ L y - r`; smoothness follows from the smoothness of continuous linear maps, subtraction by a
-- constant, and `ContDiff.norm_sq`.
theorem leastSquaresResidual_contDiff (L : H →L[ℝ] K) (r : K) :
    ContDiff ℝ 2 (leastSquaresResidual L r) := by
  -- The residual map is affine, hence `C^2`, and `‖·‖^2` preserves that regularity.
  have hResidual : ContDiff ℝ 2 (fun y : H ↦ L y - r) := by
    simpa using L.contDiff.sub contDiff_const
  simpa [leastSquaresResidual] using (contDiff_norm_sq ℝ).comp hResidual

private theorem hasFDerivAt_residualMap (L : H →L[ℝ] K) (r : K) (x : H) :
    HasFDerivAt (fun y : H ↦ L y - r) L x := by
  simpa using L.hasFDerivAt.sub_const r

variable [CompleteSpace H] [CompleteSpace K]

/-- Example 2.60: the least-squares residual has gradient `2 L† (L x - r)` at every point `x`. -/
-- Proof sketch: differentiate the affine residual map `y ↦ L y - r`, compose with the standard
-- derivative formula for `y ↦ ‖y‖^2`, and rewrite the resulting functional using the adjoint of
-- `L`.
theorem leastSquaresResidual_hasGradientAt (L : H →L[ℝ] K) (r : K) (x : H) :
    HasGradientAt (leastSquaresResidual L r) ((2 : ℝ) • (L.adjoint (L x - r))) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hResidual := hasFDerivAt_residualMap L r x
  convert hResidual.norm_sq using 1
  ext y
  simp [InnerProductSpace.toDual_apply_apply, map_sub, two_smul, L.adjoint_inner_left]

/-- The Fréchet derivative of the least-squares residual is the continuous linear functional
represented by the gradient vector `2 (L† (L x - r))`. -/
theorem leastSquaresResidual_hasFDerivAt (L : H →L[ℝ] K) (r : K) (x : H) :
    HasFDerivAt (leastSquaresResidual L r)
      (InnerProductSpace.toDual ℝ H ((2 : ℝ) • (L.adjoint (L x - r)))) x := by
  simpa [hasGradientAt_iff_hasFDerivAt] using leastSquaresResidual_hasGradientAt L r x

/-- The gradient of the least-squares residual is the affine map
`x ↦ 2 • L† (L x - r)`. -/
theorem gradient_leastSquaresResidual (L : H →L[ℝ] K) (r : K) :
    ∇ (leastSquaresResidual L r) = fun x ↦ (2 : ℝ) • (L.adjoint (L x - r)) := by
  exact gradient_eq (leastSquaresResidual_hasGradientAt L r)

/-- The derivative of the gradient map of the least-squares residual is the constant Hessian
operator `2 L†L`. -/
-- Proof sketch: rewrite the gradient using its explicit affine formula and differentiate its linear
-- part.
theorem leastSquaresResidual_gradient_hasFDerivAt (L : H →L[ℝ] K) (r : K) (x : H) :
    HasFDerivAt (∇ (leastSquaresResidual L r))
      ((2 : ℝ) • (L.adjoint.comp L)) x := by
  rw [gradient_leastSquaresResidual L r]
  have hResidual := hasFDerivAt_residualMap L r x
  have hAffine :
      HasFDerivAt (fun y : H ↦ L.adjoint (L y - r)) (L.adjoint.comp L) x := by
    simpa [Function.comp_def] using L.adjoint.hasFDerivAt.comp x hResidual
  simpa using hAffine.const_smul (2 : ℝ)

/-- The Fréchet derivative of the least-squares gradient map is the constant Hessian operator
`2 L†L`. -/
theorem fderiv_gradient_leastSquaresResidual (L : H →L[ℝ] K) (r : K) (x : H) :
    fderiv ℝ (∇ (leastSquaresResidual L r)) x = (2 : ℝ) • (L.adjoint.comp L) := by
  simpa using (leastSquaresResidual_gradient_hasFDerivAt L r x).fderiv
