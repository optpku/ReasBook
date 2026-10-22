/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open EuclideanGeometry
open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-
Lemma 2.12 (1): the canonical norm-square expansion in a real inner product space is
`norm_add_sq_real`. -/
recall norm_add_sq_real {F : Type u} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F] (x y : F) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2

/-- Lemma 2.12 (2): textbook form of the parallelogram identity in a real inner product space. -/
theorem parallelogram_identity (x y : H) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  calc
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      simpa using parallelogram_law_with_norm ℝ x y
    _ = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      ring

/-- Lemma 2.12 (3): textbook reformulation of the real polarization identity. -/
theorem polarization_identity (x y : H) :
    4 * ⟪x, y⟫_ℝ = ‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 := by
  have h_add := norm_add_sq_real x y
  have h_sub := norm_sub_sq_real x y
  nlinarith

/-- Lemma 2.12 (4): Apollonius's identity, centered at the canonical midpoint of `x` and `y`. -/
theorem apollonius_identity (x y z : H) :
    ‖x - y‖ ^ 2 =
      2 * ‖z - x‖ ^ 2 + 2 * ‖z - y‖ ^ 2 - 4 * ‖z - midpoint ℝ x y‖ ^ 2 := by
  have h := dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq z x y
  simp [dist_eq_norm, sq] at h
  linarith
