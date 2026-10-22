/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- Corollary 2.15: in a real inner product space, the squared norm of an affine combination plus
the weighted squared distance equals the corresponding affine combination of squared norms. -/
-- Proof sketch: expand `‖α • x + (1 - α) • y‖ ^ 2` using `norm_add_sq_real` and scalar
-- multiplication identities, expand `‖x - y‖ ^ 2` using `norm_sub_sq_real`, and simplify the
-- resulting polynomial identity in `α`.
theorem norm_sq_affine_combination_add_weighted_norm_sub_sq
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (α : ℝ) :
    ‖α • x + (1 - α) • y‖ ^ 2 + α * (1 - α) * ‖x - y‖ ^ 2 =
      α * ‖x‖ ^ 2 + (1 - α) * ‖y‖ ^ 2 := by
  -- Expand the two squared norms by the standard real inner-product identities and normalize the
  -- scalar coefficients in one pass.
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs]
  simp [real_inner_smul_left, real_inner_smul_right]
  nlinarith [sq_abs α, sq_abs (1 - α)]
