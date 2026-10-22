/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section MonotoneOperators

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: let `u ∈ (∂ f) x` and `v ∈ (∂ f) y`. Use a finite point of `f` to show that both
-- `x` and `y` lie in the effective domain whenever the corresponding subdifferentials are
-- nonempty. Then apply the subgradient inequality for `u` at `y` and for `v` at `x`, and add the
-- two inequalities to obtain `0 ≤ ⟪x - y, u - v⟫_ℝ`.
/-- Example 20.3: for an `]-∞,+∞]`-valued function with nonempty effective domain, the
subdifferential is a monotone set-valued operator. -/
theorem subdifferential_isMonotone
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty) :
    (∂ f).IsMonotone := by
  rw [SetValuedOperator.isMonotone_iff]
  intro x u y v hux hvy
  have hx : x ∈ effectiveDomain f :=
    SubdifferentiableAt.mem_effectiveDomain hdom ⟨u, hux⟩
  have hy : y ∈ effectiveDomain f :=
    SubdifferentiableAt.mem_effectiveDomain hdom ⟨v, hvy⟩
  have hux' :
      ∀ z ∈ effectiveDomain f, ⟪z - x, u⟫_ℝ ≤ (f z : EReal).toReal - (f x : EReal).toReal := by
    simpa [subdifferential_eq_iInter_affine_halfspaces f x hx] using hux
  have hvy' :
      ∀ z ∈ effectiveDomain f, ⟪z - y, v⟫_ℝ ≤ (f z : EReal).toReal - (f y : EReal).toReal := by
    simpa [subdifferential_eq_iInter_affine_halfspaces f y hy] using hvy
  have hxu : ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
    exact hux' y hy
  have hyv : ⟪x - y, v⟫_ℝ ≤ (f x : EReal).toReal - (f y : EReal).toReal := by
    exact hvy' x hx
  have hyx : y - x = -(x - y) := by
    abel_nf
  rw [hyx, inner_neg_left] at hxu
  have hmono : 0 ≤ ⟪x - y, u⟫_ℝ - ⟪x - y, v⟫_ℝ := by
    linarith
  simpa [inner_sub_right] using hmono

end MonotoneOperators

end ERealFunction
