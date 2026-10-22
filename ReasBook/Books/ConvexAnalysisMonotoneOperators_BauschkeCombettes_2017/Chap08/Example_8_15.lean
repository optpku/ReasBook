/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Text_8_0_1

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction

namespace ERealFunction

/-- The `]-∞,+∞]`-valued extension of `x ↦ ∫ t in α..x, ψ t` that equals `+∞` on `(-∞, α)`. -/
noncomputable def integralIciExtension (ψ : ℝ → ℝ) (α : ℝ) : ℝ → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    if α ≤ x then
      ⟨((∫ t in α..x, ψ t : ℝ) : EReal), EReal.bot_lt_coe _⟩
    else
      ⟨(⊤ : EReal), top_mem_Ioi_bot⟩

/-- On the half-line `[α, +∞)`, `integralIciExtension ψ α` is the interval integral of `ψ`. -/
-- Proof sketch: unfold `integralIciExtension`; the branch condition `α ≤ x` selects the integral
-- branch, and the coercion from the subtype `Set.Ioi (⊥ : EReal)` to `EReal` removes the proof
-- field.
@[simp] theorem integralIciExtension_apply_of_le (ψ : ℝ → ℝ) {α x : ℝ} (h : α ≤ x) :
    (integralIciExtension ψ α x : EReal) = ((∫ t in α..x, ψ t : ℝ) : EReal) := by
  -- The lower-half-line condition selects the integral branch of the definition.
  simp [integralIciExtension, h]

/-- On `(-∞, α)`, `integralIciExtension ψ α` takes the value `+∞`. -/
-- Proof sketch: unfold `integralIciExtension`; the hypothesis `x < α` forces the `else` branch,
-- whose value is definitionally `⊤` after coercing the subtype value back to `EReal`.
@[simp] theorem integralIciExtension_apply_of_lt (ψ : ℝ → ℝ) {α x : ℝ} (h : x < α) :
    (integralIciExtension ψ α x : EReal) = ⊤ := by
  -- The strict inequality rules out the integral branch, so the extension equals `+∞`.
  simp [integralIciExtension, not_le.mpr h]

/-- Helper for Example 8.15: the effective domain of `integralIciExtension ψ α` is exactly the
half-line `[α, +∞)`. -/
@[simp] theorem integralIciExtension_lt_top_iff (ψ : ℝ → ℝ) {α x : ℝ} :
    ((integralIciExtension ψ α x : EReal) < ⊤) ↔ α ≤ x := by
  constructor
  · intro hx
    by_contra hαx
    -- Outside the half-line the extension is `+∞`, contradicting finiteness.
    rw [integralIciExtension_apply_of_lt ψ (lt_of_not_ge hαx)] at hx
    exact lt_irrefl _ hx
  · intro hαx
    -- On `[α, +∞)`, the value is a finite real integral.
    rw [integralIciExtension_apply_of_le ψ hαx]
    exact EReal.coe_lt_top _

/-- Helper for Example 8.15: when `y ≤ x`, the primitive of a monotone function satisfies the
textbook Jensen inequality at the point `t x + (1 - t) y`. -/
private lemma integral_primitive_jensen_le_of_le (ψ : ℝ → ℝ) (α x y t : ℝ)
    (hψ : Monotone ψ) (hyx : y ≤ x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ u in α..(t * x + (1 - t) * y), ψ u ≤
      t * (∫ u in α..x, ψ u) + (1 - t) * (∫ u in α..y, ψ u) := by
  let z := t * x + (1 - t) * y
  have hyz : y ≤ z := by
    -- The convex combination stays to the right of the lower endpoint.
    dsimp [z]
    nlinarith
  have hzx : z ≤ x := by
    -- The same convex combination stays to the left of the upper endpoint.
    dsimp [z]
    nlinarith
  have hz_int : IntervalIntegrable ψ MeasureTheory.volume α z := hψ.intervalIntegrable
  have hx_int : IntervalIntegrable ψ MeasureTheory.volume α x := hψ.intervalIntegrable
  have hy_int : IntervalIntegrable ψ MeasureTheory.volume α y := hψ.intervalIntegrable
  have hyz_int : IntervalIntegrable ψ MeasureTheory.volume y z := hψ.intervalIntegrable
  have hzx_int : IntervalIntegrable ψ MeasureTheory.volume z x := hψ.intervalIntegrable
  have hx_split :
      ∫ u in α..x, ψ u = (∫ u in α..z, ψ u) + ∫ u in z..x, ψ u := by
    -- Split the primitive at the intermediate point `z`.
    have hsub :=
      intervalIntegral.integral_interval_sub_left (a := α) (b := x) (c := z) (f := ψ)
        hx_int hz_int
    exact sub_eq_iff_eq_add'.mp hsub
  have hy_split :
      ∫ u in α..y, ψ u = (∫ u in α..z, ψ u) - ∫ u in y..z, ψ u := by
    -- The left endpoint primitive is obtained by subtracting the `y..z` increment.
    have hsub :=
      intervalIntegral.integral_interval_sub_left (a := α) (b := z) (c := y) (f := ψ)
        hz_int hy_int
    have hsplit : ∫ u in α..z, ψ u = (∫ u in α..y, ψ u) + ∫ u in y..z, ψ u :=
      sub_eq_iff_eq_add'.mp hsub
    linarith
  have hzx_bound : (x - z) * ψ z ≤ ∫ u in z..x, ψ u := by
    -- Monotonicity bounds the right increment below by the constant value `ψ z`.
    have hconst_int :
        IntervalIntegrable (fun _ : ℝ ↦ ψ z) MeasureTheory.volume z x := intervalIntegrable_const
    have hmono :=
      intervalIntegral.integral_mono_on (a := z) (b := x) (f := fun _ : ℝ ↦ ψ z) (g := ψ)
        hzx hconst_int hzx_int (fun u hu ↦ hψ hu.1)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono
  have hyz_bound : ∫ u in y..z, ψ u ≤ (z - y) * ψ z := by
    -- Monotonicity bounds the left increment above by the same constant value `ψ z`.
    have hconst_int :
        IntervalIntegrable (fun _ : ℝ ↦ ψ z) MeasureTheory.volume y z := intervalIntegrable_const
    have hmono :=
      intervalIntegral.integral_mono_on (a := y) (b := z) (f := ψ) (g := fun _ : ℝ ↦ ψ z)
        hyz hyz_int hconst_int (fun u hu ↦ hψ hu.2)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono
  have hxz_eq : x - z = (1 - t) * (x - y) := by
    -- The distances from `z` to the endpoints are the usual affine-combination factors.
    dsimp [z]
    ring
  have hzy_eq : z - y = t * (x - y) := by
    -- This is the complementary endpoint distance identity.
    dsimp [z]
    ring
  -- Rewrite the Jensen gap in terms of the two increments and estimate each one separately.
  rw [hx_split, hy_split]
  nlinarith [hzx_bound, hyz_bound, hxz_eq, hzy_eq, ht0, ht1]

/-- Helper for Example 8.15: the primitive of a monotone function is convex on the half-line
`[α, +∞)`. -/
theorem integral_primitive_jensen_le (ψ : ℝ → ℝ) (α x y t : ℝ) (hψ : Monotone ψ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ u in α..(t * x + (1 - t) * y), ψ u ≤
      t * (∫ u in α..x, ψ u) + (1 - t) * (∫ u in α..y, ψ u) := by
  rcases le_total y x with hyx | hxy
  · -- When `y ≤ x`, apply the ordered interval-comparison argument directly.
    exact integral_primitive_jensen_le_of_le ψ α x y t hψ hyx ht0 ht1
  · -- Otherwise swap the two endpoints and replace `t` by `1 - t`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc]
      using integral_primitive_jensen_le_of_le ψ α y x (1 - t) hψ hxy
        (sub_nonneg.mpr ht1) (by nlinarith)

/-- Helper for Example 8.15: when `y < x`, the primitive of a strictly monotone function satisfies
the strict textbook Jensen inequality at the point `t x + (1 - t) y`. -/
private lemma integral_primitive_jensen_lt_of_lt (ψ : ℝ → ℝ) (α x y t : ℝ)
    (hψ : StrictMono ψ) (hyx : y < x) (ht0 : 0 < t) (ht1 : t < 1) :
    ∫ u in α..(t * x + (1 - t) * y), ψ u <
      t * (∫ u in α..x, ψ u) + (1 - t) * (∫ u in α..y, ψ u) := by
  let z := t * x + (1 - t) * y
  have hyz : y < z := by
    -- Strict interiority comes from `0 < t`.
    dsimp [z]
    nlinarith
  have hzx : z < x := by
    -- The weight `t < 1` keeps the affine combination strictly below `x`.
    dsimp [z]
    nlinarith
  have hz_int : IntervalIntegrable ψ MeasureTheory.volume α z := hψ.monotone.intervalIntegrable
  have hx_int : IntervalIntegrable ψ MeasureTheory.volume α x := hψ.monotone.intervalIntegrable
  have hy_int : IntervalIntegrable ψ MeasureTheory.volume α y := hψ.monotone.intervalIntegrable
  have hyz_int : IntervalIntegrable ψ MeasureTheory.volume y z := hψ.monotone.intervalIntegrable
  have hzx_int : IntervalIntegrable ψ MeasureTheory.volume z x := hψ.monotone.intervalIntegrable
  have hx_split :
      ∫ u in α..x, ψ u = (∫ u in α..z, ψ u) + ∫ u in z..x, ψ u := by
    -- Split the primitive at the interior point `z`.
    have hsub :=
      intervalIntegral.integral_interval_sub_left (a := α) (b := x) (c := z) (f := ψ)
        hx_int hz_int
    exact sub_eq_iff_eq_add'.mp hsub
  have hy_split :
      ∫ u in α..y, ψ u = (∫ u in α..z, ψ u) - ∫ u in y..z, ψ u := by
    -- The left endpoint primitive is the `z`-primitive minus the left increment.
    have hsub :=
      intervalIntegral.integral_interval_sub_left (a := α) (b := z) (c := y) (f := ψ)
        hz_int hy_int
    have hsplit : ∫ u in α..z, ψ u = (∫ u in α..y, ψ u) + ∫ u in y..z, ψ u :=
      sub_eq_iff_eq_add'.mp hsub
    linarith
  have hright_pos :
      0 < ∫ u in z..x, (ψ u - ψ z) := by
    -- Strict monotonicity makes the right-hand comparison gap pointwise positive.
    have hdiff_int :
        IntervalIntegrable (fun u : ℝ ↦ ψ u - ψ z) MeasureTheory.volume z x := by
      exact hzx_int.sub intervalIntegrable_const
    exact intervalIntegral.intervalIntegral_pos_of_pos_on hdiff_int
      (fun u hu ↦ sub_pos.mpr (hψ hu.1)) hzx
  have hleft_pos :
      0 < ∫ u in y..z, (ψ z - ψ u) := by
    -- The same strict monotonicity makes the left-hand comparison gap pointwise positive.
    have hconst_int :
        IntervalIntegrable (fun _ : ℝ ↦ ψ z) MeasureTheory.volume y z := intervalIntegrable_const
    have hdiff_int :
        IntervalIntegrable (fun u : ℝ ↦ ψ z - ψ u) MeasureTheory.volume y z := by
      exact hconst_int.sub hyz_int
    exact intervalIntegral.intervalIntegral_pos_of_pos_on hdiff_int
      (fun u hu ↦ sub_pos.mpr (hψ hu.2)) hyz
  have hright :
      (x - z) * ψ z < ∫ u in z..x, ψ u := by
    -- Expand the positive right-gap integral into the desired strict inequality.
    have hconst_int :
        IntervalIntegrable (fun _ : ℝ ↦ ψ z) MeasureTheory.volume z x := intervalIntegrable_const
    have h := hright_pos
    rw [intervalIntegral.integral_sub hzx_int hconst_int,
      intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  have hleft :
      ∫ u in y..z, ψ u < (z - y) * ψ z := by
    -- Expand the positive left-gap integral into the corresponding strict inequality.
    have hconst_int :
        IntervalIntegrable (fun _ : ℝ ↦ ψ z) MeasureTheory.volume y z := intervalIntegrable_const
    have h := hleft_pos
    rw [intervalIntegral.integral_sub hconst_int hyz_int,
      intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  have hxz_eq : x - z = (1 - t) * (x - y) := by
    -- This is the same affine-combination distance identity as in the nonstrict case.
    dsimp [z]
    ring
  have hzy_eq : z - y = t * (x - y) := by
    -- This is the complementary distance identity.
    dsimp [z]
    ring
  -- The two strict comparison gaps make the Jensen gap strictly positive.
  rw [hx_split, hy_split]
  nlinarith [hright, hleft, hxz_eq, hzy_eq, ht0, ht1]

/-- Helper for Example 8.15: the primitive of a strictly monotone function is strictly convex on
the half-line `[α, +∞)`. -/
theorem integral_primitive_jensen_lt (ψ : ℝ → ℝ) (α x y t : ℝ) (hψ : StrictMono ψ)
    (hxy : x ≠ y) (ht0 : 0 < t) (ht1 : t < 1) :
    ∫ u in α..(t * x + (1 - t) * y), ψ u <
      t * (∫ u in α..x, ψ u) + (1 - t) * (∫ u in α..y, ψ u) := by
  rcases lt_or_gt_of_ne hxy with hxy_lt | hyx_lt
  · -- If `x < y`, swap the endpoints and replace `t` by `1 - t`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc]
      using integral_primitive_jensen_lt_of_lt ψ α y x (1 - t) hψ hxy_lt
        (sub_pos.mpr ht1) (by nlinarith)
  · -- If `y < x`, the ordered strict comparison applies directly.
    exact integral_primitive_jensen_lt_of_lt ψ α x y t hψ hyx_lt ht0 ht1

-- Proof sketch: apply Proposition 8.14 to the real-valued primitive `x ↦ ∫ t in α..x, ψ t` on the
-- convex interval `Set.Ici α`, using that its derivative is `ψ`; then rewrite the extended-real
-- function as that primitive plus the indicator of `Set.Ici α` and invoke the indicator-sum
-- convexity criterion from Proposition 8.4.
/-- Example 8.15 (1): if `ψ` is increasing, then the extended-real function that equals
`∫ t in α..x, ψ t` on `[α,+∞)` and `+∞` on `(-∞, α)` has a convex epigraph. -/
theorem convex_epigraph_integralIciExtension (ψ : ℝ → ℝ) (α : ℝ) (hψ : Monotone ψ) :
    Convex ℝ (epigraph fun x : ℝ ↦ (integralIciExtension ψ α x : EReal)) := by
  -- Route correction: monotonicity alone does not provide the derivative API from Proposition 8.14,
  -- so we close convexity through Proposition 8.4 and the direct interval-comparison Jensen proof.
  refine (convex_epigraph_iff_jensen_on_dom
    (fun x : ℝ ↦ (integralIciExtension ψ α x : EReal))).2 ?_
  intro x y hx hy t ht0 ht1
  have hxα : α ≤ x := (integralIciExtension_lt_top_iff (ψ := ψ) (α := α) (x := x)).1 hx
  have hyα : α ≤ y := (integralIciExtension_lt_top_iff (ψ := ψ) (α := α) (x := y)).1 hy
  have hzα : α ≤ t * x + (1 - t) * y := by
    -- The effective domain `[α, +∞)` is convex, so the Jensen point stays in the domain.
    nlinarith [hxα, hyα, ht0, ht1]
  have hreal :=
    integral_primitive_jensen_le ψ α x y t hψ (le_of_lt ht0) (le_of_lt ht1)
  have hE :
      (((∫ u in α..(t * x + (1 - t) * y), ψ u : ℝ) : ℝ) : EReal) ≤
        (((t * (∫ u in α..x, ψ u) + (1 - t) * (∫ u in α..y, ψ u) : ℝ) : ℝ) : EReal) := by
    -- First cast the real Jensen inequality as a finite `EReal` inequality.
    exact_mod_cast hreal
  -- Then expand the finite `EReal` arithmetic into the target Jensen form.
  simpa [smul_eq_mul, EReal.coe_mul, EReal.coe_add,
    integralIciExtension_apply_of_le ψ hzα, integralIciExtension_apply_of_le ψ hxα,
    integralIciExtension_apply_of_le ψ hyα] using hE

-- Proof sketch: first obtain strict convexity of the real-valued primitive on `Set.Ici α` from the
-- strict derivative criterion of Proposition 8.14. Then identify the effective domain of
-- `integralIciExtension ψ α` with `Set.Ici α`, where the function agrees with the primitive, and
-- translate the strict Jensen inequality on that domain into `StrictlyConvex`.
/-- Example 8.15 (2): if `ψ` is strictly increasing, then the same extended-real function is
strictly convex. -/
theorem strictlyConvex_integralIciExtension (ψ : ℝ → ℝ) (α : ℝ) (hψ : StrictMono ψ) :
    StrictlyConvex (integralIciExtension ψ α) := by
  -- Route correction: strict convexity is proved directly from the strict Jensen inequality on the
  -- effective domain, without routing through the epigraph theorem.
  intro x hx y hy hxy t ht0 ht1
  have hxα : α ≤ x := by
    exact (integralIciExtension_lt_top_iff (ψ := ψ) (α := α) (x := x)).1 <| by
      simpa [effectiveDomain] using hx
  have hyα : α ≤ y := by
    exact (integralIciExtension_lt_top_iff (ψ := ψ) (α := α) (x := y)).1 <| by
      simpa [effectiveDomain] using hy
  have hzα : α ≤ t * x + (1 - t) * y := by
    -- The strict Jensen point also stays in the effective domain.
    nlinarith [hxα, hyα, ht0, ht1]
  have hreal := integral_primitive_jensen_lt ψ α x y t hψ hxy ht0 ht1
  have hE :
      (((∫ u in α..(t * x + (1 - t) * y), ψ u : ℝ) : ℝ) : EReal) <
        (((t * (∫ u in α..x, ψ u) + (1 - t) * (∫ u in α..y, ψ u) : ℝ) : ℝ) : EReal) := by
    -- First cast the strict real Jensen inequality as a finite `EReal` inequality.
    exact_mod_cast hreal
  -- Then expand the finite `EReal` arithmetic into the target strict Jensen form.
  simpa [smul_eq_mul, EReal.coe_mul, EReal.coe_add,
    integralIciExtension_apply_of_le ψ hzα, integralIciExtension_apply_of_le ψ hxα,
    integralIciExtension_apply_of_le ψ hyα] using hE

end ERealFunction
