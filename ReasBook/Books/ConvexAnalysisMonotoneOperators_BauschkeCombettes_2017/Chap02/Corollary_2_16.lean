/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Corollary 2.16: if distinct vectors `x` and `y` in a real Hilbert space have the same norm,
then every nontrivial convex combination `α • x + (1 - α) • y` with `0 < α` and `α < 1` has norm
strictly less than `‖x‖`. -/
theorem norm_convexCombination_lt_of_ne_of_norm_eq {x y : H} {α : ℝ}
    (hxy : x ≠ y) (hnorm : ‖x‖ = ‖y‖) (hα0 : 0 < α) (hα1 : α < 1) :
    ‖α • x + (1 - α) • y‖ < ‖x‖ := by
  -- This is the textbook equal-norm specialization of the canonical strict-convexity estimate
  -- `norm_combo_lt_of_ne`.
  refine norm_combo_lt_of_ne le_rfl ?_ hxy hα0 (sub_pos.mpr hα1) ?_
  · simp [hnorm]
  · ring
