/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped Gradient InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The quadratic-affine functional associated with a bounded linear operator `L` and a vector
`u`. -/
def quadratic_affine_functional (L : H →L[ℝ] H) (u : H) : H → ℝ :=
  fun y ↦ ⟪L y, y⟫_ℝ - ⟪y, u⟫_ℝ

-- Proof sketch: unfold `quadratic_affine_functional`.
/-- Evaluating `quadratic_affine_functional L u` gives its defining inner-product formula. -/
@[simp]
theorem quadratic_affine_functional_apply (L : H →L[ℝ] H) (u y : H) :
    quadratic_affine_functional L u y = ⟪L y, y⟫_ℝ - ⟪y, u⟫_ℝ := by
  -- This is exactly the definition of the quadratic-affine functional.
  rfl

-- Proof sketch: combine the explicit derivatives of the quadratic and affine terms.
/-- The quadratic-affine functional associated with `L` and `u` is twice Fréchet differentiable. -/
theorem quadratic_affine_functional_contDiff_two
    (L : H →L[ℝ] H) (u : H) :
    ContDiff ℝ 2 (quadratic_affine_functional L u) := by
  -- Build smoothness directly from the explicit formula as a difference of smooth inner products.
  have h_quad : ContDiff ℝ 2 (fun y : H ↦ ⟪L y, y⟫_ℝ) := by
    simpa using (L.contDiff.inner ℝ (contDiff_id : ContDiff ℝ 2 (fun y : H ↦ y)))
  have h_lin : ContDiff ℝ 2 (fun y : H ↦ ⟪y, u⟫_ℝ) := by
    simpa using ((contDiff_id : ContDiff ℝ 2 (fun y : H ↦ y)).inner ℝ contDiff_const)
  simpa [quadratic_affine_functional] using h_quad.sub h_lin

section

variable [CompleteSpace H]

/-- Helper for Example 2.57: the quadratic part `y ↦ ⟪L y, y⟫` has derivative represented by
`(L + L†) x`. -/
private lemma quadratic_form_hasFDerivAt
    (L : H →L[ℝ] H) (x : H) :
    HasFDerivAt (fun y : H ↦ ⟪L y, y⟫_ℝ)
      (InnerProductSpace.toDual ℝ H ((L + L.adjoint) x)) x := by
  -- Differentiate the two inner-product entries and then rewrite the mixed term using the adjoint.
  have h_quad : HasFDerivAt (fun y : H ↦ ⟪L y, y⟫_ℝ)
      ((fderivInnerCLM ℝ (L x, x)).comp (L.prod (ContinuousLinearMap.id ℝ H))) x := by
    simpa using (L.hasFDerivAt.inner ℝ (ContinuousLinearMap.id ℝ H).hasFDerivAt)
  convert h_quad using 1
  ext h
  simp [fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, InnerProductSpace.toDual_apply_apply,
    ContinuousLinearMap.adjoint_inner_left]
  rw [real_inner_comm x (L h)]

/-- Helper for Example 2.57: the affine linear term `y ↦ ⟪y, u⟫` has derivative represented by
`u`. -/
private lemma inner_right_hasFDerivAt
    (u x : H) :
    HasFDerivAt (fun y : H ↦ ⟪y, u⟫_ℝ)
      (InnerProductSpace.toDual ℝ H u) x := by
  -- Only the first inner-product entry varies, so the derivative is the corresponding linear form.
  have h_lin : HasFDerivAt (fun y : H ↦ ⟪y, u⟫_ℝ)
      ((fderivInnerCLM ℝ (x, u)).comp ((ContinuousLinearMap.id ℝ H).prod 0)) x := by
    simpa using ((ContinuousLinearMap.id ℝ H).hasFDerivAt.inner ℝ (hasFDerivAt_const u x))
  convert h_lin using 1
  ext h
  simp [fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, InnerProductSpace.toDual_apply_apply]
  rw [real_inner_comm u h]

-- Proof sketch: expand `quadratic_affine_functional`, use bilinearity of the inner product, and
-- identify the linear part with the Riesz representative `(L + L.adjoint) x - u`.
/-- Example 2.57: the Fréchet derivative of `y ↦ ⟪L y, y⟫_ℝ - ⟪y, u⟫_ℝ` at `x` is the linear form
represented by `(L + L.adjoint) x - u`. -/
theorem quadratic_affine_functional_hasFDerivAt
    (L : H →L[ℝ] H) (u x : H) :
    HasFDerivAt (quadratic_affine_functional L u)
      (InnerProductSpace.toDual ℝ H (((L + L.adjoint) x) - u)) x := by
  -- Differentiate the quadratic and linear pieces separately, then identify the resulting linear form.
  have h_quad := quadratic_form_hasFDerivAt L x
  have h_lin := inner_right_hasFDerivAt u x
  convert h_quad.sub h_lin using 1
  ext h
  simp [sub_eq_add_neg, add_comm, add_left_comm]

/-- Example 2.57: the quadratic-affine functional `y ↦ ⟪L y, y⟫_ℝ - ⟪y, u⟫_ℝ` has gradient
`(L + L.adjoint) x - u` at every point `x`. -/
theorem quadratic_affine_functional_hasGradientAt
    (L : H →L[ℝ] H) (u x : H) :
    HasGradientAt (quadratic_affine_functional L u)
      ((L + L.adjoint) x - u) x := by
  simpa using (quadratic_affine_functional_hasFDerivAt L u x).hasGradientAt

-- Proof sketch: apply `gradient_eq` to the pointwise gradient formula.
/-- The gradient of `quadratic_affine_functional L u` is the affine map
`x ↦ (L + L.adjoint) x - u`. -/
theorem gradient_quadratic_affine_functional
    (L : H →L[ℝ] H) (u : H) :
    ∇ (quadratic_affine_functional L u) = fun x ↦ (L + L.adjoint) x - u := by
  exact gradient_eq (quadratic_affine_functional_hasGradientAt L u)

-- Proof sketch: the gradient map is affine with constant linear part
-- `L + L.adjoint`, so its Fréchet derivative is that operator at every point.
/-- The gradient map of `quadratic_affine_functional L u` has constant Fréchet derivative
`L + L.adjoint`. -/
theorem gradient_quadratic_affine_functional_hasFDerivAt
    (L : H →L[ℝ] H) (u x : H) :
    HasFDerivAt (∇ (quadratic_affine_functional L u))
      (L + L.adjoint) x := by
  -- Rewrite the gradient as an affine map and differentiate that explicit formula.
  rw [gradient_quadratic_affine_functional L u]
  simpa using ((L + L.adjoint).hasFDerivAt.sub_const u)

-- Proof sketch: take `fderiv` in the preceding `HasFDerivAt` statement.
/-- The Fréchet derivative of the gradient of `quadratic_affine_functional L u` is
`L + L.adjoint`. -/
theorem fderiv_gradient_quadratic_affine_functional
    (L : H →L[ℝ] H) (u x : H) :
    fderiv ℝ (∇ (quadratic_affine_functional L u)) x =
      (L + L.adjoint) := by
  -- The derivative is the linear part identified in the previous theorem.
  simpa using (gradient_quadratic_affine_functional_hasFDerivAt L u x).fderiv

end
