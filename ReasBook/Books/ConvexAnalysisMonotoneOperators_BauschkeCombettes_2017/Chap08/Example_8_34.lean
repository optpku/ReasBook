/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Text_8_0_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_25

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

/-- The extended-real reciprocal on the positive half-line, equal to `+∞` on `(-∞, 0]`. -/
-- Proof sketch: split on the sign of `ξ`. For `ξ > 0`, `1 / ξ` is a finite real number, hence
-- strictly above `-∞` after coercion to `EReal`; for `ξ ≤ 0`, the value is `⊤`, and `⊥ < ⊤`.
theorem positiveReciprocal_value_mem_Ioi_bot (ξ : ℝ) :
    (⊥ : EReal) < if 0 < ξ then ((1 / ξ : ℝ) : EReal) else ⊤ := by
  -- The defining case split reduces the claim to the basic order facts for `EReal`.
  by_cases hξ : 0 < ξ
  · simp [hξ, EReal.bot_lt_coe]
  · simp [hξ]

/-- The function that equals `1 / ξ` for `ξ > 0` and `+∞` for `ξ ≤ 0`. -/
noncomputable def positiveReciprocal : ℝ → Set.Ioi (⊥ : EReal) :=
  fun ξ ↦
    ⟨if 0 < ξ then ((1 / ξ : ℝ) : EReal) else ⊤, positiveReciprocal_value_mem_Ioi_bot ξ⟩

-- Proof sketch: unfold `positiveReciprocal` and simplify the defining `if` using `0 < ξ`.
/-- On the positive half-line, `positiveReciprocal` evaluates to `1 / ξ`. -/
@[simp] theorem positiveReciprocal_apply_of_pos {ξ : ℝ} (hξ : 0 < ξ) :
    (positiveReciprocal ξ : EReal) = ((1 / ξ : ℝ) : EReal) := by
  -- The positive branch of the definition is selected by the sign hypothesis.
  simp [positiveReciprocal, hξ]

-- Proof sketch: unfold `positiveReciprocal` and simplify the defining `if` using `¬ 0 < ξ`,
-- obtained from `ξ ≤ 0`.
/-- On the nonpositive half-line, `positiveReciprocal` evaluates to `+∞`. -/
@[simp] theorem positiveReciprocal_apply_of_nonpos {ξ : ℝ} (hξ : ξ ≤ 0) :
    (positiveReciprocal ξ : EReal) = ⊤ := by
  -- The nonpositive branch of the definition is selected by the order hypothesis.
  simp [positiveReciprocal, not_lt.mpr hξ]

/-- Helper for Example 8.34: the square seed takes values strictly above `-∞`. -/
theorem squareFunction_value_mem_Ioi_bot (x : ℝ) :
    (⊥ : EReal) < (((x ^ 2 : ℝ)) : EReal) := by
  -- Real values always sit strictly above `-∞` inside `EReal`.
  exact EReal.bot_lt_coe (x ^ 2)

/-- Helper for Example 8.34: package the real square map as an `]-∞,+∞]`-valued function. -/
noncomputable def squareFunction : ℝ → Set.Ioi (⊥ : EReal) :=
  fun x ↦ ⟨((x ^ 2 : ℝ) : EReal), squareFunction_value_mem_Ioi_bot x⟩

/-- Helper for Example 8.34: coercing `squareFunction x` back to `EReal` yields `x ^ 2`. -/
@[simp] theorem squareFunction_apply (x : ℝ) :
    (squareFunction x : EReal) = ((x ^ 2 : ℝ) : EReal) := rfl

/-- Helper for Example 8.34: the square seed is convex on all of `ℝ` in the Chapter 8 sense. -/
theorem squareFunction_convexOn_univ : ConvexOn squareFunction Set.univ := by
  refine ⟨by simp, ?_, ?_⟩
  · -- Every square value is finite above, so `univ` lies in the effective domain.
    intro x hx
    rw [effectiveDomain, Set.mem_setOf]
    simpa [pow_two, EReal.coe_mul] using (EReal.coe_lt_top (x * x : ℝ))
  · intro x hx y hy α hα₀ hα₁
    -- Rewrite the quadratic gap as `α * (1 - α) * (x - y)^2`, which is nonnegative.
    have hsq :
        (α * x + (1 - α) * y) ^ 2 ≤ α * x ^ 2 + (1 - α) * y ^ 2 := by
      have hgap :
          α * x ^ 2 + (1 - α) * y ^ 2 - (α * x + (1 - α) * y) ^ 2 =
            α * (1 - α) * (x - y) ^ 2 := by
        ring
      have hnonneg : 0 ≤ α * (1 - α) * (x - y) ^ 2 := by
        exact mul_nonneg (mul_nonneg hα₀.le (sub_nonneg.mpr hα₁.le)) (sq_nonneg (x - y))
      nlinarith [hnonneg, hgap]
    have hsqE :
        (((α * x + (1 - α) * y) ^ 2 : ℝ) : EReal) ≤
          (α : EReal) * (((x ^ 2 : ℝ)) : EReal) +
            ((1 - α : ℝ) : EReal) * (((y ^ 2 : ℝ)) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr hsq
    simpa [squareFunction_apply, smul_eq_mul] using hsqE

/-- Helper for Example 8.34: the reciprocal extension is the adjoint of the square seed. -/
theorem positiveReciprocal_eq_adjoint_squareFunction (ξ : ℝ) :
    (positiveReciprocal ξ : EReal) = (adjoint squareFunction ξ : EReal) := by
  by_cases hξ : 0 < ξ
  · -- On the positive branch, both definitions reduce to the same real identity.
    rw [positiveReciprocal_apply_of_pos hξ, adjoint_apply_of_pos squareFunction hξ, squareFunction_apply]
    have hreal : ξ * (1 / ξ) ^ 2 = 1 / ξ := by
      field_simp [hξ.ne']
    simpa [EReal.coe_mul] using congrArg (fun t : ℝ ↦ (t : EReal)) hreal.symm
  · have hξ_nonpos : ξ ≤ 0 := le_of_not_gt hξ
    -- On the nonpositive branch, both functions are defined to be `⊤`.
    rw [positiveReciprocal_apply_of_nonpos hξ_nonpos, adjoint_apply_of_nonpos squareFunction hξ_nonpos]

/-- Helper for Example 8.34: the adjoint is the perspective transform restricted to the slice
`η = 1`. -/
private theorem adjoint_eq_perspective_one_local (φ : ℝ → Set.Ioi (⊥ : EReal)) (ξ : ℝ) :
    (adjoint φ ξ : EReal) = perspective (fun x : ℝ ↦ (φ x : EReal)) (ξ, (1 : ℝ)) := by
  by_cases hξ : 0 < ξ
  · -- On the positive branch, both formulas equal `ξ * φ (1 / ξ)`.
    rw [adjoint_apply_of_pos φ hξ, perspective_apply_of_pos _ hξ]
    simp [one_div, smul_eq_mul]
  · have hξ_nonpos : ξ ≤ 0 := le_of_not_gt hξ
    -- On the nonpositive branch, both formulas reduce to `⊤`.
    rw [adjoint_apply_of_nonpos φ hξ_nonpos, perspective_apply_of_nonpos _ hξ_nonpos]

/-- Helper for Example 8.34: a Chapter 8 `ConvexOn` function on `univ` has convex real-height
epigraph after coercion to `EReal`. -/
private theorem convex_epigraph_coe_of_convexOn_univ_local
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : ConvexOn φ Set.univ) :
    Convex ℝ (epigraph (fun x : ℝ ↦ (φ x : EReal))) := by
  -- Proposition 8.4 turns the epigraph goal into Jensen's inequality on the effective domain.
  refine (convex_epigraph_iff_jensen_on_dom (fun x : ℝ ↦ (φ x : EReal))).2 ?_
  intro x y _hx _hy α hα hα_lt_one
  -- Since the set is `univ`, the Chapter 8 convexity hypothesis applies directly.
  simpa using hφ.ineq (x := x) (y := y) (by simp) (by simp) hα hα_lt_one

/-- Helper for Example 8.34: slicing the convex perspective epigraph along `η = 1` preserves
convexity. -/
private theorem convex_epigraph_perspective_one_slice_local
    (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hpersp :
      Convex ℝ (epigraph (perspective (fun x : ℝ ↦ (φ x : EReal))))) :
    Convex ℝ (epigraph (fun ξ : ℝ ↦ perspective (fun x : ℝ ↦ (φ x : EReal)) (ξ, (1 : ℝ)))) := by
  refine (convex_iff_forall_pos).2 ?_
  intro p hp q hq a b ha hb hab
  rcases p with ⟨ξ₁, η₁⟩
  rcases q with ⟨ξ₂, η₂⟩
  have hp' : (((ξ₁, (1 : ℝ)), η₁)) ∈ epigraph (perspective (fun x : ℝ ↦ (φ x : EReal))) := by
    -- A point in the slice epigraph is also a point in the ambient perspective epigraph.
    simpa [mem_epigraph_iff] using hp
  have hq' : (((ξ₂, (1 : ℝ)), η₂)) ∈ epigraph (perspective (fun x : ℝ ↦ (φ x : EReal))) := by
    -- The second endpoint is lifted to the same ambient epigraph.
    simpa [mem_epigraph_iff] using hq
  have hcombo :
      a • (((ξ₁, (1 : ℝ)), η₁) : (ℝ × ℝ) × ℝ) +
          b • (((ξ₂, (1 : ℝ)), η₂) : (ℝ × ℝ) × ℝ) ∈
        epigraph (perspective (fun x : ℝ ↦ (φ x : EReal))) := by
    -- Convexity of the ambient epigraph transfers the lifted endpoints.
    exact (convex_iff_forall_pos.mp hpersp) hp' hq' ha hb hab
  -- Expanding the convex combination shows that the second coordinate remains fixed at `1`.
  simpa [mem_epigraph_iff, Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, hab]
    using hcombo

/-- Helper for Example 8.34: the adjoint of a Chapter 8 convex function on `univ` has convex
epigraph. -/
private theorem adjoint_convexOn_univ_local
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : ConvexOn φ Set.univ) :
    Convex ℝ (epigraph (fun ξ : ℝ ↦ (adjoint φ ξ : EReal))) := by
  have hφ_convex :
      Convex ℝ (epigraph (fun x : ℝ ↦ (φ x : EReal))) :=
    convex_epigraph_coe_of_convexOn_univ_local φ hφ
  have hpersp_convex :
      Convex ℝ (epigraph (perspective (fun x : ℝ ↦ (φ x : EReal)))) :=
    convex_epigraph_perspective _ hφ_convex
  have hslice_convex :
      Convex ℝ (epigraph (fun ξ : ℝ ↦ perspective (fun x : ℝ ↦ (φ x : EReal)) (ξ, (1 : ℝ)))) :=
    convex_epigraph_perspective_one_slice_local φ hpersp_convex
  -- Re-identify the affine slice with the adjoint definition.
  simpa [adjoint_eq_perspective_one_local] using hslice_convex

/-- Helper for Example 8.34: positive endpoints satisfy Jensen's inequality by the adjoint route. -/
theorem positiveReciprocal_jensen_of_pos {ξ₁ ξ₂ α : ℝ}
    (hξ₁ : 0 < ξ₁) (hξ₂ : 0 < ξ₂) (hα₀ : 0 < α) (hα₁ : α < 1) :
    (positiveReciprocal (α * ξ₁ + (1 - α) * ξ₂) : EReal) ≤
      (α : EReal) * (positiveReciprocal ξ₁ : EReal) +
        (1 - α : EReal) * (positiveReciprocal ξ₂ : EReal) := by
  -- Route correction: rather than differentiating `x ↦ 1 / x`, rewrite it as the adjoint of the
  -- square seed and reuse the convex epigraph machinery from Example 8.33.
  have hadjoint_convex :
      Convex ℝ (epigraph (fun ξ : ℝ ↦ (adjoint squareFunction ξ : EReal))) :=
    adjoint_convexOn_univ_local squareFunction squareFunction_convexOn_univ
  have hdom₁ : ξ₁ ∈ dom (fun ξ : ℝ ↦ (adjoint squareFunction ξ : EReal)) := by
    -- Positive inputs land in the finite branch of the adjoint.
    rw [mem_dom_iff, ← positiveReciprocal_eq_adjoint_squareFunction, positiveReciprocal_apply_of_pos hξ₁]
    exact EReal.coe_lt_top _
  have hdom₂ : ξ₂ ∈ dom (fun ξ : ℝ ↦ (adjoint squareFunction ξ : EReal)) := by
    -- The same finiteness argument applies to the second positive endpoint.
    rw [mem_dom_iff, ← positiveReciprocal_eq_adjoint_squareFunction, positiveReciprocal_apply_of_pos hξ₂]
    exact EReal.coe_lt_top _
  have hJ :
      (adjoint squareFunction (α * ξ₁ + (1 - α) * ξ₂) : EReal) ≤
        (α : EReal) * (adjoint squareFunction ξ₁ : EReal) +
          ((1 - α : ℝ) : EReal) * (adjoint squareFunction ξ₂ : EReal) :=
    (convex_epigraph_iff_jensen_on_dom (fun ξ : ℝ ↦ (adjoint squareFunction ξ : EReal))).1
      hadjoint_convex hdom₁ hdom₂ hα₀ hα₁
  -- Rewrite the adjoint back to `positiveReciprocal`.
  simpa [smul_eq_mul, positiveReciprocal_eq_adjoint_squareFunction] using hJ

-- Proof sketch: if `ξ₁ ≤ 0` or `ξ₂ ≤ 0`, then the right-hand side is `⊤`, so the inequality is
-- immediate. If both are positive, the claim reduces to the convexity of `x ↦ 1 / x` on
-- `(0, +∞)`.
/-- Example 8.34: the function `ξ ↦ 1 / ξ` for `ξ > 0` and `ξ ↦ +∞` for `ξ ≤ 0` satisfies
Jensen's inequality for every `ξ₁`, `ξ₂`, and every `α ∈ [0,1]`. -/
theorem positiveReciprocal_convex (ξ₁ ξ₂ α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    (positiveReciprocal (α * ξ₁ + (1 - α) * ξ₂) : EReal) ≤
      (α : EReal) * (positiveReciprocal ξ₁ : EReal) +
        (1 - α : EReal) * (positiveReciprocal ξ₂ : EReal) := by
  rcases lt_or_eq_of_le hα₁ with hα_lt | rfl
  · rcases eq_or_lt_of_le hα₀ with rfl | hα_pos
    · -- The left endpoint case `α = 0` collapses Jensen's inequality to equality at `ξ₂`.
      simp
    · by_cases hξ₁ : 0 < ξ₁
      · by_cases hξ₂ : 0 < ξ₂
        · -- Both endpoints lie in the effective domain, so the adjoint/Jensen helper applies.
          exact positiveReciprocal_jensen_of_pos hξ₁ hξ₂ hα_pos hα_lt
        · have hξ₂_nonpos : ξ₂ ≤ 0 := le_of_not_gt hξ₂
          have hα_term_ne_bot :
              (α : EReal) * (positiveReciprocal ξ₁ : EReal) ≠ ⊥ :=
            (adjoint_mul_mem_Ioi_bot α hα_pos (positiveReciprocal ξ₁)).ne'
          have hsecond_top :
              (1 - (α : EReal)) * (positiveReciprocal ξ₂ : EReal) = ⊤ := by
            rw [positiveReciprocal_apply_of_nonpos hξ₂_nonpos]
            have hβ_pos : 0 < ((1 - α : ℝ) : EReal) :=
              EReal.coe_pos.mpr (sub_pos.mpr hα_lt)
            simpa [EReal.coe_sub] using EReal.mul_top_of_pos hβ_pos
          -- A nonpositive second endpoint forces the whole right-hand side to be `⊤`.
          rw [hsecond_top, EReal.add_top_of_ne_bot hα_term_ne_bot]
          exact le_top
      · have hξ₁_nonpos : ξ₁ ≤ 0 := le_of_not_gt hξ₁
        have hsecond_ne_bot :
            (1 - (α : EReal)) * (positiveReciprocal ξ₂ : EReal) ≠ ⊥ := by
          have hβ_pos : 0 < 1 - α := sub_pos.mpr hα_lt
          exact (adjoint_mul_mem_Ioi_bot (1 - α) hβ_pos (positiveReciprocal ξ₂)).ne'
        have hfirst_top :
            (α : EReal) * (positiveReciprocal ξ₁ : EReal) = ⊤ := by
          rw [positiveReciprocal_apply_of_nonpos hξ₁_nonpos]
          exact EReal.mul_top_of_pos (EReal.coe_pos.mpr hα_pos)
        -- A nonpositive first endpoint forces the whole right-hand side to be `⊤`.
        rw [hfirst_top, EReal.top_add_of_ne_bot hsecond_ne_bot]
        exact le_top
  · -- The right endpoint case `α = 1` collapses Jensen's inequality to equality at `ξ₁`.
    have harg : 1 * ξ₁ + (1 - 1) * ξ₂ = ξ₁ := by
      ring
    have hone : ((1 : ℝ) : EReal) = 1 := rfl
    rw [harg, hone, one_mul]
    have hcoeff : (1 - 1 : EReal) = 0 := by
      exact EReal.sub_self (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)
    rw [hcoeff, zero_mul, add_zero]

end ERealFunction
