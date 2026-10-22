/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

section

variable {C : Set 𝓗} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

private theorem projectionPoint_mem_and_inner_sub_right_nonpos (x : 𝓗) :
    P x ∈ C ∧ ∀ z ∈ C, ⟪z - P x, x - P x⟫_ℝ ≤ 0 := by
  exact
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex).mp rfl

-- Proof sketch: let `P := projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty
-- hC_closed hC_convex)`. Use the variational characterization of metric projections onto nonempty
-- closed convex sets for `P x` tested against `P y` and for `P y` tested against `P x`; adding the
-- two inequalities and rearranging gives the stated bound.
/-- Proposition 4.16: the metric projection onto a nonempty closed convex subset of a real Hilbert
space is firmly nonexpansive: for all `x` and `y`, the canonical projection map
`P := projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)`
satisfies `‖P x - P y‖^2 ≤ ⟪P x - P y, x - y⟫_ℝ`. -/
theorem norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
    (x y : 𝓗) :
    ‖P x - P y‖ ^ (2 : ℕ) ≤ ⟪P x - P y, x - y⟫_ℝ := by
  let p := P x
  let q := P y
  have hp : p ∈ C ∧ ∀ z ∈ C, ⟪z - p, x - p⟫_ℝ ≤ 0 :=
    projectionPoint_mem_and_inner_sub_right_nonpos hC_nonempty hC_closed hC_convex x
  have hq : q ∈ C ∧ ∀ z ∈ C, ⟪z - q, y - q⟫_ℝ ≤ 0 :=
    projectionPoint_mem_and_inner_sub_right_nonpos hC_nonempty hC_closed hC_convex y
  -- Testing each variational inequality at the other projection point gives the two sign controls
  -- from the textbook proof.
  have hxp : 0 ≤ ⟪p - q, x - p⟫_ℝ := by
    have hqp : ⟪q - p, x - p⟫_ℝ ≤ 0 := hp.2 q hq.1
    have hneg :
        ⟪q - p, x - p⟫_ℝ = -⟪p - q, x - p⟫_ℝ := by
      rw [show q - p = -(p - q) by abel_nf, inner_neg_left]
    linarith [hqp, hneg]
  have hyq : ⟪p - q, y - q⟫_ℝ ≤ 0 := by
    simpa using hq.2 p hp.1
  -- Expand `⟪p - q, x - y⟫` into the two cross terms plus `‖p - q‖²`.
  have hsplit :
      ⟪p - q, x - y⟫_ℝ =
        ⟪p - q, x - p⟫_ℝ + ‖p - q‖ ^ (2 : ℕ) - ⟪p - q, y - q⟫_ℝ := by
    have hdecomp : x - y = (x - p) + (p - q) - (y - q) := by
      abel_nf
    calc
      ⟪p - q, x - y⟫_ℝ = ⟪p - q, (x - p) + (p - q) - (y - q)⟫_ℝ := by
        rw [hdecomp]
      _ = ⟪p - q, (x - p) + (p - q)⟫_ℝ - ⟪p - q, y - q⟫_ℝ := by
        rw [inner_sub_right]
      _ = ⟪p - q, x - p⟫_ℝ + ⟪p - q, p - q⟫_ℝ - ⟪p - q, y - q⟫_ℝ := by
        rw [inner_add_right]
      _ = ⟪p - q, x - p⟫_ℝ + ‖p - q‖ ^ (2 : ℕ) - ⟪p - q, y - q⟫_ℝ := by
        rw [real_inner_self_eq_norm_sq]
  -- The two sign controls show that the expanded right-hand side dominates `‖p - q‖²`.
  have hfinal : ‖p - q‖ ^ (2 : ℕ) ≤ ⟪p - q, x - y⟫_ℝ := by
    rw [hsplit]
    linarith
  simpa [p, q] using hfinal

end
