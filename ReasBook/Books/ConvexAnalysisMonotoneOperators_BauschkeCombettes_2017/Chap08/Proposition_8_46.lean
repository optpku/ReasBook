/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

universe u

namespace ERealFunction

section OrderHelpers

variable {H : Type u}

/-- Helper for Proposition 8.46: a point of the nonpositive zero-sublevel set lies in the
effective domain because a value bounded above by `0` cannot be `⊤`. -/
theorem mem_effectiveDomain_of_mem_lowerLevelSet_zero
    {f : H → Set.Ioi (⊥ : EReal)} {z : H}
    (hz : z ∈ lowerLevelSet (fun x : H ↦ (f x : EReal)) 0) :
    z ∈ effectiveDomain f := by
  -- Rewrite the sublevel membership as an order bound and compare with `⊤`.
  rw [mem_effectiveDomain_iff]
  rw [mem_lowerLevelSet_iff] at hz
  exact lt_of_le_of_lt hz EReal.zero_lt_top

/-- Helper for Proposition 8.46: a convex combination of a nonpositive finite value and a strictly
negative finite value is still strictly negative. -/
lemma ereal_convex_combination_nonpos_lt_zero
    {a b : Set.Ioi (⊥ : EReal)} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (ha : (a : EReal) ≤ 0) (hb : (b : EReal) < 0) :
    (α : EReal) * (a : EReal) + (1 - α : EReal) * (b : EReal) < 0 := by
  -- The first weighted term stays nonpositive because both factors are nonnegative.
  have hα0' : (0 : EReal) < α := by
    exact_mod_cast hα0
  have h1α0' : (0 : EReal) < 1 - α := by
    exact_mod_cast sub_pos.mpr hα1
  have hterm1 : (α : EReal) * (a : EReal) ≤ 0 := by
    exact EReal.mul_nonpos_iff.mpr (Or.inl ⟨le_of_lt hα0', ha⟩)
  -- The second weighted term is strictly negative because the strict negative value gets a
  -- positive coefficient.
  have hterm2 : (1 - α : EReal) * (b : EReal) < 0 := by
    exact EReal.mul_neg_iff.mpr (Or.inl ⟨h1α0', hb⟩)
  have hterm1_ne_bot : (α : EReal) * (a : EReal) ≠ ⊥ := by
    exact (EReal.mul_ne_bot _ _).2
      ⟨Or.inl (by exact_mod_cast (EReal.coe_ne_bot α)), Or.inr (ne_of_gt a.2),
        Or.inl (by exact_mod_cast (EReal.coe_ne_top α)), Or.inl (le_of_lt hα0')⟩
  -- Add the strict and weak bounds to conclude that the whole convex combination is negative.
  have hsum : (1 - α : EReal) * (b : EReal) + (α : EReal) * (a : EReal) < 0 + 0 := by
    exact EReal.add_lt_add_of_lt_of_le hterm2 hterm1 hterm1_ne_bot EReal.zero_ne_top
  simpa [add_comm] using hsum

end OrderHelpers

section Semicontinuous

variable {H : Type u} [NormedAddCommGroup H]

-- Proof sketch: if `x₀` were not in the interior of the `0`-sublevel set, every neighborhood of
-- `x₀` would contain a point where the value is positive; a sequence or net of such points
-- converging to `x₀` would then contradict upper semicontinuity at `x₀` together with `f x₀ < 0`.
/-- Proposition 8.46 (1): if `f` is upper semicontinuous at `x₀` and `f x₀ < 0`, then `x₀`
belongs to the interior of the lower level set `lev≤₀ f`. -/
theorem mem_interior_lowerLevelSet_zero_of_upperSemicontinuousAt
    {f : H → Set.Ioi (⊥ : EReal)} {x₀ : H}
    (husc : UpperSemicontinuousAt (fun x : H ↦ (f x : EReal)) x₀)
    (hx₀ : (f x₀ : EReal) < 0) :
    x₀ ∈ interior (lowerLevelSet (fun x : H ↦ (f x : EReal)) 0) := by
  -- Convert interior membership into a neighborhood statement about the zero-sublevel set.
  rw [mem_interior_iff_mem_nhds]
  -- Upper semicontinuity at the strict negative level `0` gives an eventual strict upper bound.
  have hlt : ∀ᶠ x in 𝓝 x₀, (f x : EReal) < 0 :=
    (upperSemicontinuousAt_iff.mp husc) 0 hx₀
  -- Weaken the strict bound to `≤ 0` to obtain eventual membership in the nonpositive sublevel
  -- set.
  exact Filter.mem_of_superset hlt fun x hx ↦ by
    rw [mem_lowerLevelSet_iff]
    exact le_of_lt hx

end Semicontinuous

section Normed

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Helper for Proposition 8.46: an interior point of the nonpositive zero-sublevel set can be
written as a strict convex combination of the anchor `x₀` and a nearby nonpositive point. -/
lemma exists_extrapolated_point_mem_lowerLevelSet_zero
    {f : H → Set.Ioi (⊥ : EReal)} {x x₀ : H}
    (hx : x ∈ interior (lowerLevelSet (fun z : H ↦ (f z : EReal)) 0))
    (hxx₀ : x ≠ x₀) :
    ∃ y : H, ∃ α : ℝ,
      y ∈ lowerLevelSet (fun z : H ↦ (f z : EReal)) 0 ∧
      0 < α ∧ α < 1 ∧ x = α • y + (1 - α) • x₀ := by
  -- Extract a ball around `x` that stays inside the nonpositive sublevel set.
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx) with ⟨ρ, hρ, hball⟩
  have hdist : 0 < ‖x - x₀‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hxx₀)
  let δ : ℝ := ρ / (2 * ‖x - x₀‖)
  let y : H := x + δ • (x - x₀)
  let α : ℝ := 1 / (1 + δ)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hy_ball : y ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hyx : y - x = δ • (x - x₀) := by
      simp [y, sub_eq_add_neg]
    rw [hyx, norm_smul, Real.norm_of_nonneg (le_of_lt hδ)]
    dsimp [δ]
    have hhalf_lt : ρ / 2 < ρ := by
      linarith
    calc
      ρ / (2 * ‖x - x₀‖) * ‖x - x₀‖ = ρ / 2 := by
        field_simp [hdist.ne']
      _ < ρ := hhalf_lt
  have hy : y ∈ lowerLevelSet (fun z : H ↦ (f z : EReal)) 0 := hball hy_ball
  have hα0 : 0 < α := by
    dsimp [α]
    positivity
  have hαeq : α * (1 + δ) = 1 := by
    dsimp [α]
    field_simp [hδ.ne']
  have hα1 : α < 1 := by
    nlinarith [hα0, hδ, hαeq]
  have hy_shift : y - x₀ = (1 + δ) • (x - x₀) := by
    dsimp [y]
    have hsplit : x + δ • (x - x₀) - x₀ = (x - x₀) + δ • (x - x₀) := by
      abel_nf
    rw [hsplit, ← one_smul ℝ (x - x₀)]
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      (add_smul 1 δ ((1 : ℝ) • (x - x₀))).symm
  refine ⟨y, α, hy, hα0, hα1, ?_⟩
  -- Put `x` on the affine line through `x₀` and the extrapolated point `y`.
  have hline : x = AffineMap.lineMap x₀ y α := by
    rw [AffineMap.lineMap_apply_module']
    rw [hy_shift, smul_smul, hαeq]
    simp
  simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using hline

-- Proof sketch: for `x` in the interior of `lev≤₀ f`, choose a small ball around `x` contained in
-- that level set. Using a point `x₀` with `f x₀ < 0`, express `x` as a strict convex combination
-- of `x₀` and some nearby point `y` with `f y ≤ 0`; convexity on the effective domain then forces
-- `f x < 0`.
/-- Proposition 8.46 (2): if `f` is convex and has a point `x₀` with `f x₀ < 0`, then the
interior of `lev≤₀ f` is contained in the strict lower level set `lev<₀ f`. -/
theorem interior_lowerLevelSet_zero_subset_strictLowerLevelSet_zero_of_convexOn
    {f : H → Set.Ioi (⊥ : EReal)} {x₀ : H}
    (hconv : ConvexOn f (effectiveDomain f))
    (hx₀ : (f x₀ : EReal) < 0) :
    interior (lowerLevelSet (fun x : H ↦ (f x : EReal)) 0) ⊆
      strictLowerLevelSet (fun x : H ↦ (f x : EReal)) 0 := by
  intro x hx
  rw [mem_strictLowerLevelSet_iff]
  by_cases hxx₀ : x = x₀
  · -- The anchor point already has strictly negative value.
    simpa [hxx₀] using hx₀
  · -- Route correction: follow the source geometry by extrapolating past `x` inside the interior
    -- ball, then invoke convexity on the effective domain.
    obtain ⟨y, α, hy, hα0, hα1, hx_eq⟩ :=
      exists_extrapolated_point_mem_lowerLevelSet_zero hx hxx₀
    have hx₀_dom : x₀ ∈ effectiveDomain f := by
      rw [mem_effectiveDomain_iff]
      exact lt_trans hx₀ EReal.zero_lt_top
    have hy_dom : y ∈ effectiveDomain f :=
      mem_effectiveDomain_of_mem_lowerLevelSet_zero hy
    have hy_nonpos : (f y : EReal) ≤ 0 := by
      rw [mem_lowerLevelSet_iff] at hy
      exact hy
    -- Jensen's inequality bounds `f x` by the convex combination of the endpoint values.
    have hineq : (f (α • y + (1 - α) • x₀) : EReal) ≤
        (α : EReal) * (f y : EReal) + (1 - α : EReal) * (f x₀ : EReal) :=
      hconv.ineq hy_dom hx₀_dom hα0 hα1
    -- The nearby point is nonpositive while the anchor is strictly negative, so the convex
    -- combination is strictly negative.
    have hrhs : (α : EReal) * (f y : EReal) + (1 - α : EReal) * (f x₀ : EReal) < 0 :=
      ereal_convex_combination_nonpos_lt_zero hα0 hα1 hy_nonpos hx₀
    simpa [hx_eq] using lt_of_le_of_lt hineq hrhs

end Normed

end ERealFunction
