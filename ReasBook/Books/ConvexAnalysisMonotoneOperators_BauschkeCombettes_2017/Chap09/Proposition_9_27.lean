/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- The directional difference quotient of an `]-∞,+∞]`-valued function along the ray
`x + α • y`, viewed as a function of the positive scalar `α`. -/
noncomputable def directionalDifferenceQuotient
    (f : H → Set.Ioi (⊥ : EReal)) (x y : H) : Set.Ioi (0 : ℝ) → EReal :=
  fun α ↦ ((f (x + (α : ℝ) • y) : EReal) - (f x : EReal)) / (α : ℝ)

/-- Helper for Proposition 9.27: a point on the ray segment from `x` to `x + β • y` can be
rewritten as the convex combination dictated by `α / β`. -/
private lemma ray_point_eq_convex_combination_endpoint
    (x y : H) {α β : ℝ} (hβ : 0 < β) :
    x + α • y = (α / β) • (x + β • y) + (1 - α / β) • x := by
  -- Rewrite the ray point so the convexity inequality can be applied with endpoints `x` and
  -- `x + β • y` in the textbook order.
  have hscalar : (α / β) * β = α := by
    field_simp [hβ.ne']
  calc
    x + α • y = x + (((α / β) * β) • y) := by rw [hscalar]
    _ = (1 : ℝ) • x + (α / β) • (β • y) := by simp [smul_smul]
    _ = ((α / β) + (1 - α / β)) • x + (α / β) • (β • y) := by simp
    _ = (α / β) • x + (1 - α / β) • x + (α / β) • (β • y) := by
          rw [add_smul]
    _ = (α / β) • x + ((α / β) • (β • y)) + (1 - α / β) • x := by abel_nf
    _ = (α / β) • (x + β • y) + (1 - α / β) • x := by
          simp [smul_add, add_assoc]

/-- Helper for Proposition 9.27: if `x` and `x + β • y` lie in the effective domain and
`0 < α < β`, then the intermediate ray point `x + α • y` also lies in the effective domain. -/
private lemma ray_point_mem_effectiveDomain_of_lt
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hz : x + β • y ∈ effectiveDomain f) :
    x + α • y ∈ effectiveDomain f := by
  -- The convexity estimate produces an upper bound by a finite convex combination of finite
  -- endpoint values, so the intermediate value is finite as well.
  have hβ : 0 < β := lt_trans hα hαβ
  have hlam0 : 0 < α / β := div_pos hα hβ
  have hlam1 : α / β < 1 := by
    rw [div_lt_iff₀ hβ]
    simpa using hαβ
  have hineq :
      (f (x + α • y) : EReal) ≤
        (α / β : EReal) * (f (x + β • y) : EReal) +
          (1 - α / β : EReal) * (f x : EReal) := by
    -- Rewrite the intermediate point into the convex-combination shape required by `ConvexOn.ineq`.
    rw [ray_point_eq_convex_combination_endpoint x y hβ]
    exact hconv.ineq hz hx hlam0 hlam1
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hz_top : (f (x + β • y) : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hz)
  have hz_bot : (f (x + β • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + β • y) : EReal) from (f (x + β • y)).2)
  have hterm1_ne_top : (α / β : EReal) * (f (x + β • y) : EReal) ≠ ⊤ := by
    rw [← EReal.coe_div, ← EReal.coe_toReal hz_top hz_bot, ← EReal.coe_mul]
    exact ne_of_lt (EReal.coe_lt_top _)
  have hterm2_ne_top : (1 - α / β : EReal) * (f x : EReal) ≠ ⊤ := by
    rw [show (1 - α / β : EReal) = ((1 - α / β : ℝ) : EReal) by
        rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_div, ← EReal.coe_sub],
      ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_mul]
    exact ne_of_lt (EReal.coe_lt_top _)
  have hsum_ne_top :
      (α / β : EReal) * (f (x + β • y) : EReal) +
          (1 - α / β : EReal) * (f x : EReal) ≠ ⊤ := by
    exact EReal.add_ne_top hterm1_ne_top hterm2_ne_top
  have hsum_lt_top :
      (α / β : EReal) * (f (x + β • y) : EReal) +
          (1 - α / β : EReal) * (f x : EReal) < ⊤ :=
    lt_of_le_of_ne le_top hsum_ne_top
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt hineq hsum_lt_top

/-- Helper for Proposition 9.27: if the endpoint on the ray is in the effective domain, then the
directional difference quotient at that scalar is the cast of the corresponding real quotient. -/
private lemma directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x y : H}
    (hx : x ∈ effectiveDomain f) (a : Set.Ioi (0 : ℝ))
    (ha : x + (a : ℝ) • y ∈ effectiveDomain f) :
    directionalDifferenceQuotient f x y a =
      ((((f (x + (a : ℝ) • y) : EReal).toReal - (f x : EReal).toReal) / (a : ℝ) : ℝ) : EReal) := by
  -- Route correction: once both endpoint values are finite, rewrite them as real casts and let
  -- `EReal.coe_sub` / `EReal.coe_div` collapse the quotient to an ordinary real expression.
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hxa_top : (f (x + (a : ℝ) • y) : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp ha)
  have hxa_bot : (f (x + (a : ℝ) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + (a : ℝ) • y) : EReal) from
      (f (x + (a : ℝ) • y)).2)
  rw [directionalDifferenceQuotient, ← EReal.coe_toReal hxa_top hxa_bot,
    ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_sub, ← EReal.coe_div]
  simp

/-- Helper for Proposition 9.27: the convexity upper bound rearranges to the monotonicity
inequality for the real difference quotients. -/
private lemma real_difference_quotient_le_of_convex_bound
    {u v w α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (h : u ≤ (α / β) * v + (1 - α / β) * w) :
    (u - w) / α ≤ (v - w) / β := by
  -- Multiply the convexity inequality by the positive denominator `β` and then isolate the
  -- quotients using the standard ordered-field division lemmas.
  have hβ : 0 < β := lt_trans hα hαβ
  have hmul : β * u ≤ α * v + (β - α) * w := by
    calc
      β * u ≤ β * ((α / β) * v + (1 - α / β) * w) := by
        exact mul_le_mul_of_nonneg_left h (le_of_lt hβ)
      _ = α * v + (β - α) * w := by
        ring_nf
        field_simp [hβ.ne']
        ring
  have htarget : β * (u - w) ≤ α * (v - w) := by
    nlinarith
  have hstep : u - w ≤ (α * (v - w)) / β := by
    exact (le_div_iff₀ hβ).2 (by
      simpa [sub_eq_add_neg, mul_assoc, mul_comm, mul_left_comm] using htarget)
  exact (div_le_iff₀ hα).2 (by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hstep)

-- Proof sketch: for `0 < α < β`, write `x + α • y` as the convex combination
-- `(1 - α / β) • x + (α / β) • (x + β • y)`, apply convexity on `effectiveDomain f`, and then
-- rearrange the resulting inequality to compare the two quotients.
/-- Proposition 9.27: for a proper convex `]-∞,+∞]`-valued function, the directional difference
quotient based at a point of the effective domain is increasing on `ℝ_{++}`. -/
theorem directionalDifferenceQuotient_monotone
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    Monotone (directionalDifferenceQuotient f x y) := by
  intro α β hαβ
  by_cases hEq : α = β
  · -- The equality case is immediate from reflexivity after identifying the two subtype points.
    simp [hEq]
  · have hαβ_real : (α : ℝ) ≤ (β : ℝ) := hαβ
    have hlt : (α : ℝ) < (β : ℝ) := lt_of_le_of_ne hαβ_real (by
      intro hcoe
      apply hEq
      exact Subtype.ext hcoe)
    let z : H := x + (β : ℝ) • y
    let lam : ℝ := (α : ℝ) / (β : ℝ)
    have hlam0 : 0 < lam := by
      dsimp [lam]
      exact div_pos α.2 β.2
    have hlam1 : lam < 1 := by
      dsimp [lam]
      rw [div_lt_iff₀ β.2]
      simpa using hlt
    by_cases hzTop : (f z : EReal) = ⊤
    · -- If the endpoint value is `⊤`, then the larger difference quotient is `⊤`, so the
      -- comparison is automatic.
      have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
      have hβ_pos_ereal : (0 : EReal) < ((β : ℝ) : EReal) := by
        exact_mod_cast β.2
      have hβ_ne_top : ((β : ℝ) : EReal) ≠ ⊤ := ne_of_lt (EReal.coe_lt_top _)
      have hβquot :
          directionalDifferenceQuotient f x y β = ⊤ := by
        -- Unfold the quotient and collapse `⊤ - f x` and `⊤ / β` using positivity of `β`.
        rw [directionalDifferenceQuotient]
        dsimp [z] at hzTop
        rw [hzTop, EReal.top_sub hx_top, EReal.top_div_of_pos_ne_top hβ_pos_ereal hβ_ne_top]
      rw [hβquot]
      exact le_top
    · have hz : z ∈ effectiveDomain f := by
        -- In the finite branch, the endpoint belongs to the effective domain exactly because its
        -- value is not `⊤`.
        rw [mem_effectiveDomain_iff]
        exact lt_of_le_of_ne le_top hzTop
      have hα_dom : x + (α : ℝ) • y ∈ effectiveDomain f := by
        exact ray_point_mem_effectiveDomain_of_lt f hconv hx α.2 hlt (by simpa [z] using hz)
      have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
      have hx_bot : (f x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
      have hz_bot : (f z : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
      have hconv_real :
          (f (x + (α : ℝ) • y) : EReal).toReal ≤
            lam * (f z : EReal).toReal + (1 - lam) * (f x : EReal).toReal := by
        -- Convert the EReal convexity inequality to a real inequality once all three values are
        -- known to be finite.
        have hineq :
            (f (x + (α : ℝ) • y) : EReal) ≤
              (lam : EReal) * (f z : EReal) + (1 - lam : EReal) * (f x : EReal) := by
          dsimp [lam, z]
          rw [ray_point_eq_convex_combination_endpoint x y β.2]
          exact hconv.ineq hz hx hlam0 hlam1
        have hα_bot : (f (x + (α : ℝ) • y) : EReal) ≠ ⊥ := by
          exact ne_of_gt (show (⊥ : EReal) < (f (x + (α : ℝ) • y) : EReal) from
            (f (x + (α : ℝ) • y)).2)
        have hterm1_ne_top : (lam : EReal) * (f z : EReal) ≠ ⊤ := by
          rw [show (lam : EReal) = (((lam : ℝ)) : EReal) by rfl,
            ← EReal.coe_toReal hzTop hz_bot, ← EReal.coe_mul]
          exact ne_of_lt (EReal.coe_lt_top _)
        have hterm1_ne_bot : (lam : EReal) * (f z : EReal) ≠ ⊥ := by
          rw [show (lam : EReal) = (((lam : ℝ)) : EReal) by rfl,
            ← EReal.coe_toReal hzTop hz_bot, ← EReal.coe_mul]
          exact EReal.coe_ne_bot _
        have hterm2_ne_top : (1 - lam : EReal) * (f x : EReal) ≠ ⊤ := by
          rw [show (1 - lam : EReal) = ((1 - lam : ℝ) : EReal) by
                  rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub],
              ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_mul]
          exact ne_of_lt (EReal.coe_lt_top _)
        have hterm2_ne_bot : (1 - lam : EReal) * (f x : EReal) ≠ ⊥ := by
          rw [show (1 - lam : EReal) = ((1 - lam : ℝ) : EReal) by
                  rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub],
              ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_mul]
          exact EReal.coe_ne_bot _
        have hsum_ne_top :
            (lam : EReal) * (f z : EReal) + (1 - lam : EReal) * (f x : EReal) ≠ ⊤ :=
          EReal.add_ne_top hterm1_ne_top hterm2_ne_top
        have hsum_toReal :
            ((lam : EReal) * (f z : EReal) + (1 - lam : EReal) * (f x : EReal)).toReal =
              lam * (f z : EReal).toReal + (1 - lam) * (f x : EReal).toReal := by
          rw [EReal.toReal_add hterm1_ne_top hterm1_ne_bot hterm2_ne_top hterm2_ne_bot,
            EReal.toReal_mul, EReal.toReal_mul, EReal.toReal_coe,
            show (1 - lam : EReal) = ((1 - lam : ℝ) : EReal) by
              rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub],
            EReal.toReal_coe]
        simpa [hsum_toReal] using EReal.toReal_le_toReal hineq hα_bot hsum_ne_top
      have hαquot :=
        directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain f hx α hα_dom
      have hβquot :=
        directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain f hx β (by
          simpa [z] using hz)
      have hreal :
          (((f (x + (α : ℝ) • y) : EReal).toReal - (f x : EReal).toReal) / (α : ℝ)) ≤
            (((f z : EReal).toReal - (f x : EReal).toReal) / (β : ℝ)) := by
        -- This is the algebraic rearrangement of the convexity bound in the source proof.
        exact real_difference_quotient_le_of_convex_bound α.2 hlt hconv_real
      -- Both quotients are finite casts, so the order comparison reduces to the real inequality.
      rw [hαquot, hβquot]
      exact EReal.coe_le_coe_iff.mpr hreal

end ERealFunction
