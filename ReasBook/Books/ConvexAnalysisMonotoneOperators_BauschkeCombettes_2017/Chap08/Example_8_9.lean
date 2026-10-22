/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/- Example 8.9: the norm function on a real normed vector space is convex, equivalently,
for all `x y : H` and all `λ ∈ [0,1]`,
`‖λ • x + (1 - λ) • y‖ ≤ λ * ‖x‖ + (1 - λ) * ‖y‖`. -/
recall convexOn_univ_norm

-- Proof sketch: choose a nonzero vector `x` and compare it with `0`. For any positive
-- coefficients `a` and `b` with `a + b = 1`, homogeneity and `‖0‖ = 0` give
-- `‖a • x + b • 0‖ = a * ‖x‖ = a * ‖x‖ + b * ‖0‖`, so the strict inequality required by
-- `StrictConvexOn` fails.
/-- The norm function is not strictly convex on the whole space of a nontrivial real normed vector
space. -/
theorem norm_not_strictConvexOn_univ [Nontrivial H] :
    ¬ StrictConvexOn ℝ (Set.univ : Set H) (norm : H → ℝ) := by
  intro hstrict
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hx_ne : x ≠ 0 := hx
  have hlt :
      ‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (0 : H)‖ <
        (1 / 2 : ℝ) • ‖x‖ + (1 / 2 : ℝ) • ‖(0 : H)‖ :=
    hstrict.2 (by simp) (by simp) hx_ne (by norm_num) (by norm_num) (by norm_num)
  have hleft :
      ‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (0 : H)‖ = (1 / 2 : ℝ) * ‖x‖ := by
    simp [norm_smul]
  have hright :
      (1 / 2 : ℝ) • ‖x‖ + (1 / 2 : ℝ) • ‖(0 : H)‖ = (1 / 2 : ℝ) * ‖x‖ := by
    simp [smul_eq_mul]
  rw [hleft, hright] at hlt
  exact (lt_irrefl _ hlt)

end
