/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace
open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Example 2.67: after transporting the gradient field through the Riesz map,
the symmetry of mixed second derivatives yields symmetry of the Hessian operator. -/
private theorem gradientWithin_fderiv_isSymmetric_aux
    {f : H → ℝ} {U : Set H} {x : H} {A : H →L[ℝ] H}
    (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ᶠ y in nhds x, DifferentiableWithinAt ℝ f U y)
    (hA : HasFDerivWithinAt (gradientWithin f U) A U x) :
    A.IsSymmetric := by
-- Proof sketch: apply `second_derivative_symmetric_of_eventually` to the derivative field
-- `toDualMap ℝ H ∘ gradientWithin f U`; the eventual differentiability hypothesis ensures that
-- this is the actual first derivative of `f` near `x`, and the resulting equality of mixed second
-- derivatives is exactly the symmetry of `A`.
  let f' : H → H →L[ℝ] ℝ := fun y ↦ (toDualMap ℝ H) (gradientWithin f U y)
  -- Near `x`, the transported gradient is the genuine Fréchet derivative of `f`.
  have hf' : ∀ᶠ y in nhds x, HasFDerivAt f (f' y) y := by
    filter_upwards [hU.mem_nhds hx, hf] with y hyU hyf
    have hy_grad : HasGradientWithinAt f (gradientWithin f U y) U y := hyf.hasGradientWithinAt
    have hy_deriv : HasFDerivAt f ((toDual ℝ H) (gradientWithin f U y)) y :=
      hy_grad.hasFDerivWithinAt.hasFDerivAt (hU.mem_nhds hyU)
    simpa [f', toDual_apply_eq_toDualMap_apply] using hy_deriv
  -- The derivative of the transported gradient field is the transported Hessian operator.
  have hA' : HasFDerivAt f' ((toDualMap ℝ H).toContinuousLinearMap.comp A) x := by
    have hA_at : HasFDerivAt (gradientWithin f U) A x := hA.hasFDerivAt (hU.mem_nhds hx)
    simpa [f'] using (toDualMap ℝ H).toContinuousLinearMap.hasFDerivAt.comp x hA_at
  -- Schwarz symmetry for the dual-valued first-derivative field translates back to `A`.
  intro u v
  have hs := second_derivative_symmetric_of_eventually hf' hA' u v
  simpa [f', toDualMap_apply_apply, real_inner_comm] using hs

/-- Example 2.67: if `U` is an open neighborhood of `x` in a real Hilbert space, `f` is
Fréchet differentiable on a neighborhood of `x` inside `U`, and the genuine gradient field
`gradientWithin f U` has Fréchet derivative `A` at `x` within `U`, then the Hessian operator `A`
is self-adjoint. -/
theorem gradientWithin_fderiv_isSelfAdjoint
    {f : H → ℝ} {U : Set H} {x : H} {A : H →L[ℝ] H}
    (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ᶠ y in nhds x, DifferentiableWithinAt ℝ f U y)
    (hA : HasFDerivWithinAt (gradientWithin f U) A U x) :
    IsSelfAdjoint A :=
  (gradientWithin_fderiv_isSymmetric_aux hU hx hf hA).isSelfAdjoint

/-- Textbook symmetry reformulation of `gradientWithin_fderiv_isSelfAdjoint`. -/
theorem gradientWithin_fderiv_isSymmetric
    {f : H → ℝ} {U : Set H} {x : H} {A : H →L[ℝ] H}
    (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ᶠ y in nhds x, DifferentiableWithinAt ℝ f U y)
    (hA : HasFDerivWithinAt (gradientWithin f U) A U x) :
    A.IsSymmetric :=
  (gradientWithin_fderiv_isSelfAdjoint hU hx hf hA).isSymmetric

/-- The Hessian identity corresponding to self-adjointness of the Fréchet derivative of the
gradient field. -/
-- Proof sketch: apply the canonical symmetry theorem
-- `gradientWithin_fderiv_isSelfAdjoint`.
theorem gradientWithin_fderiv_inner_symmetric
    {f : H → ℝ} {U : Set H} {x : H} {A : H →L[ℝ] H}
    (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ᶠ y in nhds x, DifferentiableWithinAt ℝ f U y)
    (hA : HasFDerivWithinAt (gradientWithin f U) A U x) :
    ∀ u v : H, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ := by
  simpa [LinearMap.IsSymmetric] using
    (gradientWithin_fderiv_isSelfAdjoint hU hx hf hA).isSymmetric
