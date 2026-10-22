/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u v

namespace ERealFunction

variable {H : Type u} {K : Type v}
variable [AddCommGroup H] [Module ℝ H]
variable [AddCommGroup K] [Module ℝ K]

/-- The marginal function of `F : H × K → ]-∞,+∞]` is obtained by taking the infimum over the
second variable. -/
noncomputable def marginalFunction (F : H × K → Set.Ioi (⊥ : EReal)) : H → EReal :=
  fun x ↦ sInf (Set.range fun y : K ↦ (F (x, y) : EReal))

-- Proof sketch: unfold the marginal as an infimum over the fiber and apply `sInf_le` to the
-- witness `y`.
/-- The marginal function is bounded above by each value on the corresponding fiber. -/
theorem marginalFunction_le (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) (y : K) :
    marginalFunction F x ≤ (F (x, y) : EReal) := by
  -- Unfold the marginal and use the chosen fiber point as an admissible witness.
  rw [marginalFunction]
  exact sInf_le (Set.mem_range_self y)

/-- Helper for Proposition 8.35: a strict upper bound on the marginal is exceeded by some fiber
value. -/
lemma exists_lt_fiber_of_marginalFunction_lt
    (F : H × K → Set.Ioi (⊥ : EReal)) {x : H} {ξ : EReal}
    (hξ : marginalFunction F x < ξ) :
    ∃ y : K, (F (x, y) : EReal) < ξ := by
  -- Unfold the marginal and extract a fiber value below the chosen upper bound.
  rw [marginalFunction] at hξ
  obtain ⟨z, hzmem, hzlt⟩ := (sInf_lt_iff).1 hξ
  rw [Set.mem_range] at hzmem
  obtain ⟨y, rfl⟩ := hzmem
  exact ⟨y, hzlt⟩

/-- Helper for Proposition 8.35: convexity on `Set.univ` forces every value of the marginal to be
finite. -/
lemma marginalFunction_lt_top
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : ConvexOn F Set.univ) (x : H) :
    marginalFunction F x < ⊤ := by
  -- Dominate the marginal by any fiber value, then use that convexity on `Set.univ` makes every
  -- fiber value finite.
  obtain ⟨p, -⟩ := hF.nonempty
  obtain ⟨_, y₀⟩ := p
  exact lt_of_le_of_lt (marginalFunction_le F x y₀) (hF.subset_effectiveDomain (by simp))

/-- Helper for Proposition 8.35: multiplication by a positive finite `EReal` preserves strict
order. -/
lemma strict_right_mul_lt {a b c : EReal} (hc0 : 0 < c) (hc_top : c ≠ ⊤) (hab : a < b) :
    a * c < b * c := by
  -- Divide both sides by the positive coefficient and use strict monotonicity of division.
  have hdiv : a * c / c < b * c / c := by
    have ha_cancel : a * c / c = a := by
      exact (EReal.div_eq_iff (ne_bot_of_gt hc0) hc_top (ne_of_gt hc0)).2 (by simp)
    have hb_cancel : b * c / c = b := by
      exact (EReal.div_eq_iff (ne_bot_of_gt hc0) hc_top (ne_of_gt hc0)).2 (by simp)
    simpa [ha_cancel, hb_cancel] using hab
  exact (EReal.strictMono_div_right_of_pos hc0 hc_top).lt_iff_lt.mp hdiv

/-- Helper for Proposition 8.35: Jensen's inequality for `F` on `H × K` rewrites to the coordinate
form used in the marginal-function proof. -/
lemma convex_pair_value_le
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : ConvexOn F Set.univ)
    {x₁ x₂ : H} {y₁ y₂ : K} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (F (α • x₁ + (1 - α) • x₂, α • y₁ + (1 - α) • y₂) : EReal) ≤
      (α : EReal) * (F (x₁, y₁) : EReal) +
        (((1 - α : ℝ)) : EReal) * (F (x₂, y₂) : EReal) := by
  -- Rewrite the product-space convex combination into its coordinate form and apply Jensen.
  simpa [Prod.smul_mk] using
    hF.ineq (x := (x₁, y₁)) (y := (x₂, y₂)) (by simp) (by simp) hα0 hα1

-- Proof sketch: handle the endpoint cases `α = 0` and `α = 1` separately. For `0 < α < 1`,
-- choose approximate fiber minimizers at `x₁` and `x₂`, apply the convexity inequality for `F`
-- to the pair `((x₁, y₁), (x₂, y₂))`, and then let the approximation levels decrease to the two
-- marginal values.
/-- Proposition 8.35: the marginal function obtained by infimizing a convex
`]-∞,+∞]`-valued function over the second variable is convex. -/
theorem marginalFunction_convex
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : ConvexOn F Set.univ)
    {x₁ x₂ : H} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    marginalFunction F (α • x₁ + (1 - α) • x₂) ≤
      (α : EReal) * marginalFunction F x₁ +
        (((1 - α : ℝ)) : EReal) * marginalFunction F x₂ := by
  by_cases hα_eq_zero : α = 0
  · -- The left endpoint reduces to the second point of the segment.
    simp [hα_eq_zero]
  by_cases hα_eq_one : α = 1
  · -- The right endpoint reduces to the first point of the segment.
    simp [hα_eq_one]
  -- Route correction: instead of approximating the whole weighted sum at once, reserve separate
  -- budgets above each weighted marginal and choose fiber approximations below those budgets.
  have hα_pos : 0 < α := lt_of_le_of_ne hα0 (by simpa [eq_comm] using hα_eq_zero)
  have hα_lt_one : α < 1 := lt_of_le_of_ne hα1 hα_eq_one
  have h_one_sub_pos : 0 < 1 - α := sub_pos.mpr hα_lt_one
  have hαE_pos : (0 : EReal) < (α : EReal) := by
    exact_mod_cast hα_pos
  have h_one_sub_E_pos : (0 : EReal) < (((1 - α : ℝ)) : EReal) := by
    exact_mod_cast h_one_sub_pos
  have hterm₁_ne_top : (α : EReal) * marginalFunction F x₁ ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inl (by exact_mod_cast hα0),
      Or.inl (EReal.coe_ne_top α), ?_⟩
    exact Or.inr (marginalFunction_lt_top F hF x₁).ne
  have hterm₂_ne_top : (((1 - α : ℝ)) : EReal) * marginalFunction F x₂ ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 - α)),
      Or.inl (by exact_mod_cast h_one_sub_pos.le), Or.inl (EReal.coe_ne_top (1 - α)), ?_⟩
    exact Or.inr (marginalFunction_lt_top F hF x₂).ne
  -- Remove the slack variables by showing the marginal lies below every pair of budgets strictly
  -- above the two weighted marginal terms.
  refine EReal.le_add_of_forall_gt (Or.inr hterm₂_ne_top) (Or.inl hterm₁_ne_top) ?_
  intro a' ha' b' hb'
  -- Turn the two budget inequalities into real upper bounds on the chosen fiber values.
  have hmarg₁_lt_div : marginalFunction F x₁ < a' / (α : EReal) := by
    refine (EReal.lt_div_iff hαE_pos (EReal.coe_ne_top α)).2 ?_
    simpa [mul_comm] using ha'
  have hmarg₂_lt_div : marginalFunction F x₂ < b' / (((1 - α : ℝ)) : EReal) := by
    refine (EReal.lt_div_iff h_one_sub_E_pos (EReal.coe_ne_top (1 - α))).2 ?_
    simpa [mul_comm] using hb'
  obtain ⟨ξ₁, hξ₁_lower, hξ₁_upper⟩ := EReal.exists_between_coe_real hmarg₁_lt_div
  obtain ⟨ξ₂, hξ₂_lower, hξ₂_upper⟩ := EReal.exists_between_coe_real hmarg₂_lt_div
  obtain ⟨y₁, hy₁⟩ := exists_lt_fiber_of_marginalFunction_lt F hξ₁_lower
  obtain ⟨y₂, hy₂⟩ := exists_lt_fiber_of_marginalFunction_lt F hξ₂_lower
  -- Evaluate the marginal at the convex combination of the two approximate minimizers.
  have h_marginal_eval :
      marginalFunction F (α • x₁ + (1 - α) • x₂) ≤
        (F (α • x₁ + (1 - α) • x₂, α • y₁ + (1 - α) • y₂) : EReal) := by
    exact marginalFunction_le F _ _
  have h_convex_eval :
      (F (α • x₁ + (1 - α) • x₂, α • y₁ + (1 - α) • y₂) : EReal) ≤
        (α : EReal) * (F (x₁, y₁) : EReal) +
          (((1 - α : ℝ)) : EReal) * (F (x₂, y₂) : EReal) := by
    exact convex_pair_value_le F hF hα_pos hα_lt_one
  -- The two fiber values stay below the reserved budgets after scaling by the positive weights.
  have h_weight₁ : (α : EReal) * (F (x₁, y₁) : EReal) < (α : EReal) * (ξ₁ : EReal) := by
    have : (F (x₁, y₁) : EReal) * (α : EReal) < (ξ₁ : EReal) * (α : EReal) := by
      exact strict_right_mul_lt hαE_pos (EReal.coe_ne_top α) hy₁
    simpa [mul_comm] using this
  have h_weight₂ : (((1 - α : ℝ)) : EReal) * (F (x₂, y₂) : EReal) <
      (((1 - α : ℝ)) : EReal) * (ξ₂ : EReal) := by
    have : (F (x₂, y₂) : EReal) * (((1 - α : ℝ)) : EReal) <
        (ξ₂ : EReal) * (((1 - α : ℝ)) : EReal) := by
      exact strict_right_mul_lt h_one_sub_E_pos (EReal.coe_ne_top (1 - α)) hy₂
    simpa [mul_comm] using this
  have h_budget₁ : (α : EReal) * (ξ₁ : EReal) < a' := by
    have : (ξ₁ : EReal) * (α : EReal) < a' :=
      (EReal.lt_div_iff hαE_pos (EReal.coe_ne_top α)).1 hξ₁_upper
    simpa [mul_comm] using this
  have h_budget₂ : (((1 - α : ℝ)) : EReal) * (ξ₂ : EReal) < b' := by
    have : (ξ₂ : EReal) * (((1 - α : ℝ)) : EReal) < b' :=
      (EReal.lt_div_iff h_one_sub_E_pos (EReal.coe_ne_top (1 - α))).1 hξ₂_upper
    simpa [mul_comm] using this
  have h_weighted_lt :
      (α : EReal) * (F (x₁, y₁) : EReal) +
          (((1 - α : ℝ)) : EReal) * (F (x₂, y₂) : EReal) <
        a' + b' := by
    exact lt_trans (EReal.add_lt_add h_weight₁ h_weight₂) (EReal.add_lt_add h_budget₁ h_budget₂)
  exact (lt_of_le_of_lt (le_trans h_marginal_eval h_convex_eval) h_weighted_lt).le

end ERealFunction
