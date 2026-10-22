/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: expand `‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2` with `norm_add_sq_real`, rewrite the scalar
-- factors using `real_inner_smul_left` and `real_inner_smul_right`, and simplify the resulting
-- polynomial identity in `α`.
/-- Lemma 2.17 (1): for `α ∈ (0,1)`, the scaled difference between `‖x‖²` and the squared norm of
`(1 - α⁻¹) • x + α⁻¹ • y` equals `(2 * α - 1) * ‖x‖ ^ 2 + 2 * (1 - α) * inner ℝ x y - ‖y‖ ^ 2`. -/
theorem alpha_sq_norm_sq_sub_inv_affine_combination_eq
    (x y : H) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    α ^ 2 * (‖x‖ ^ 2 - ‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2) =
      (2 * α - 1) * ‖x‖ ^ 2 + 2 * (1 - α) * inner ℝ x y - ‖y‖ ^ 2 := by
  have hα0 : α ≠ 0 := ne_of_gt hα.1
  have hnorm :
      ‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2 =
        (1 - α⁻¹) ^ 2 * ‖x‖ ^ 2 + 2 * ((1 - α⁻¹) * α⁻¹ * inner ℝ x y) + (α⁻¹) ^ 2 * ‖y‖ ^ 2 := by
    -- Expand the affine combination exactly once, then rewrite the scalar coefficients.
    rw [norm_add_sq_real]
    have hαabs : |α| = α := abs_of_pos hα.1
    simp [norm_smul, real_inner_smul_left, real_inner_smul_right, pow_two, mul_assoc, hαabs]
    nlinarith [sq_abs (1 - α⁻¹)]
  -- Clear the inverse denominators and normalize the resulting scalar identity.
  rw [hnorm]
  field_simp [hα0]
  ring

-- Proof sketch: this is an immediate rearrangement of the previous identity, moving the
-- `‖x‖ ^ 2`-term into the parenthesized expression.
/-- Lemma 2.17 (2): for `α ∈ (0,1)`, the same scaled norm identity can be rewritten as
`2 * (1 - α) * inner ℝ x y - (‖y‖ ^ 2 + (1 - 2 * α) * ‖x‖ ^ 2)`. -/
theorem alpha_sq_norm_sq_sub_inv_affine_combination_eq_rearranged
    (x y : H) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    α ^ 2 * (‖x‖ ^ 2 - ‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2) =
      2 * (1 - α) * inner ℝ x y - (‖y‖ ^ 2 + (1 - 2 * α) * ‖x‖ ^ 2) := by
  -- Reuse the structural expansion from part (1) and only rearrange the scalar terms.
  calc
    α ^ 2 * (‖x‖ ^ 2 - ‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2)
        = (2 * α - 1) * ‖x‖ ^ 2 + 2 * (1 - α) * inner ℝ x y - ‖y‖ ^ 2 :=
          alpha_sq_norm_sq_sub_inv_affine_combination_eq x y hα
    _ = 2 * (1 - α) * inner ℝ x y - (‖y‖ ^ 2 + (1 - 2 * α) * ‖x‖ ^ 2) := by
      ring

-- Proof sketch: combine the first identity with `norm_sub_sq_real x y` to rewrite
-- `2 * inner ℝ x y` as `‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖x - y‖ ^ 2`, then simplify.
/-- Lemma 2.17 (3): for `α ∈ (0,1)`, the scaled norm identity also equals
`α * (‖x‖ ^ 2 - α⁻¹ * (1 - α) * ‖x - y‖ ^ 2 - ‖y‖ ^ 2)`. -/
theorem alpha_sq_norm_sq_sub_inv_affine_combination_eq_norm_sub
    (x y : H) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    α ^ 2 * (‖x‖ ^ 2 - ‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2) =
      α * (‖x‖ ^ 2 - α⁻¹ * (1 - α) * ‖x - y‖ ^ 2 - ‖y‖ ^ 2) := by
  have hα0 : α ≠ 0 := ne_of_gt hα.1
  -- Substitute the standard norm-subtraction formula into the part (1) identity.
  calc
    α ^ 2 * (‖x‖ ^ 2 - ‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2)
        = (2 * α - 1) * ‖x‖ ^ 2 + 2 * (1 - α) * inner ℝ x y - ‖y‖ ^ 2 :=
          alpha_sq_norm_sq_sub_inv_affine_combination_eq x y hα
    _ = α * (‖x‖ ^ 2 - α⁻¹ * (1 - α) * ‖x - y‖ ^ 2 - ‖y‖ ^ 2) := by
      rw [norm_sub_sq_real]
      field_simp [hα0]
      ring

-- Proof sketch: expand `‖2 • y - x‖ ^ 2` using `norm_sub_sq_real (2 • y) x`, rewrite the scalar
-- terms with `norm_smul` and `real_inner_smul_left`, and simplify.
/-- Lemma 2.17 (4): the difference `‖x‖² - ‖2 • y - x‖²` equals
`4 * (inner ℝ x y - ‖y‖ ^ 2)`. -/
theorem norm_sq_sub_norm_sq_reflection_eq_four_mul
    (x y : H) :
    ‖x‖ ^ 2 - ‖(2 : ℝ) • y - x‖ ^ 2 = 4 * (inner ℝ x y - ‖y‖ ^ 2) := by
  rw [show (2 : ℝ) • y = y + y by simp [two_smul]]
  have hsub : ‖x‖ ^ 2 - ‖(y + y) - x‖ ^ 2 = 2 * inner ℝ (y + y) x - ‖y + y‖ ^ 2 := by
    -- First isolate the reflected norm term using the standard `‖u - v‖²` identity.
    nlinarith [norm_sub_sq_real (y + y) x]
  have hnorm : ‖y + y‖ ^ 2 = 4 * ‖y‖ ^ 2 := by
    -- Then expand the doubled point `y + y`.
    rw [norm_add_sq_real, real_inner_self_eq_norm_sq]
    ring
  -- Assemble the two expansions and commute the inner product once.
  rw [hsub, hnorm, inner_add_left, real_inner_comm y x]
  ring

-- Proof sketch: rewrite `inner ℝ (x - y) y` with `inner_sub_left` and
-- `real_inner_self_eq_norm_sq` to identify it with `inner ℝ x y - ‖y‖ ^ 2`, then use the
-- previous formula.
/-- Lemma 2.17 (5): the same reflection identity can be written as
`4 * inner ℝ (x - y) y`. -/
theorem norm_sq_sub_norm_sq_reflection_eq_four_inner_sub
    (x y : H) :
    ‖x‖ ^ 2 - ‖(2 : ℝ) • y - x‖ ^ 2 = 4 * inner ℝ (x - y) y := by
  -- Rewrite the part (4) formula using the linearity of the inner product in the left slot.
  calc
    ‖x‖ ^ 2 - ‖(2 : ℝ) • y - x‖ ^ 2 = 4 * (inner ℝ x y - ‖y‖ ^ 2) :=
      norm_sq_sub_norm_sq_reflection_eq_four_mul x y
    _ = 4 * inner ℝ (x - y) y := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]

-- Proof sketch: apply `norm_sub_sq_real x y` to replace `2 * inner ℝ x y` by
-- `‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖x - y‖ ^ 2`, then simplify the previous identity.
/-- Lemma 2.17 (6): the reflection identity is also
`2 * (‖x‖ ^ 2 - ‖x - y‖ ^ 2 - ‖y‖ ^ 2)`. -/
theorem norm_sq_sub_norm_sq_reflection_eq_two_mul_norm_sub
    (x y : H) :
    ‖x‖ ^ 2 - ‖(2 : ℝ) • y - x‖ ^ 2 =
      2 * (‖x‖ ^ 2 - ‖x - y‖ ^ 2 - ‖y‖ ^ 2) := by
  -- Substitute the standard expression for `‖x - y‖²` into the part (4) identity.
  calc
    ‖x‖ ^ 2 - ‖(2 : ℝ) • y - x‖ ^ 2 = 4 * (inner ℝ x y - ‖y‖ ^ 2) :=
      norm_sq_sub_norm_sq_reflection_eq_four_mul x y
    _ = 2 * (‖x‖ ^ 2 - ‖x - y‖ ^ 2 - ‖y‖ ^ 2) := by
      rw [norm_sub_sq_real]
      ring
