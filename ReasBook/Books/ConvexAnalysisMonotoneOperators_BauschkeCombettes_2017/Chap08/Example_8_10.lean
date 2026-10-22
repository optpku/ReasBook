/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Corollary_2_15

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 8.10: the squared norm is uniformly convex on the whole space with modulus
`r ↦ r ^ 2`. -/
lemma uniformConvexOn_norm_sq :
    UniformConvexOn (Set.univ : Set H) (fun r : ℝ ↦ r ^ 2) (fun x : H ↦ ‖x‖ ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hb_eq : b = 1 - a := by
    linarith
  rw [hb_eq]
  -- Rewrite Corollary 2.15 into the subtraction form required by `UniformConvexOn`.
  have hgap :
      ‖a • x + (1 - a) • y‖ ^ 2 =
        a * ‖x‖ ^ 2 + (1 - a) * ‖y‖ ^ 2 - a * (1 - a) * ‖x - y‖ ^ 2 := by
    linarith [norm_sq_affine_combination_add_weighted_norm_sub_sq x y a]
  exact le_of_eq hgap

/-- Example 8.10: the squared norm function `x ↦ ‖x‖ ^ 2` is strictly convex on the whole space of
a real inner product space. -/
-- Proof sketch: expand `‖t • x + (1 - t) • y‖ ^ 2` using the inner-product identity and rewrite
-- the gap to the weighted average `t * ‖x‖ ^ 2 + (1 - t) * ‖y‖ ^ 2` as
-- `t * (1 - t) * ‖x - y‖ ^ 2`, which is positive when `x ≠ y` and `0 < t < 1`.
theorem strictConvexOn_norm_sq : StrictConvexOn ℝ Set.univ (fun x : H ↦ ‖x‖ ^ 2) := by
  -- Upgrade the exact quadratic gap to strict convexity using positivity of `r ↦ r ^ 2`.
  refine uniformConvexOn_norm_sq.strictConvexOn ?_
  intro r hr
  -- The modulus from the helper is strictly positive away from the origin.
  exact sq_pos_of_ne_zero hr
