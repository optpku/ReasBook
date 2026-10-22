/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section Normed

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Example 8.22: when `y ≤ x`, the primitive of a monotone function satisfies the
ordered Jensen inequality at the affine point `t * x + (1 - t) * y`. -/
private lemma integral_primitive_jensen_le_of_le (ψ : ℝ → ℝ) (x y t : ℝ)
    (hψmono : Monotone ψ) (hyx : y ≤ x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ u in 0..(t * x + (1 - t) * y), ψ u ≤
      t * (∫ u in 0..x, ψ u) + (1 - t) * (∫ u in 0..y, ψ u) := by
  let z := t * x + (1 - t) * y
  have hyz : y ≤ z := by
    -- The Jensen point stays between the ordered endpoints.
    dsimp [z]
    nlinarith
  have hzx : z ≤ x := by
    -- The same affine combination also stays to the left of `x`.
    dsimp [z]
    nlinarith
  have hz_int : IntervalIntegrable ψ MeasureTheory.volume 0 z := hψmono.intervalIntegrable
  have hx_int : IntervalIntegrable ψ MeasureTheory.volume 0 x := hψmono.intervalIntegrable
  have hy_int : IntervalIntegrable ψ MeasureTheory.volume 0 y := hψmono.intervalIntegrable
  have hyz_int : IntervalIntegrable ψ MeasureTheory.volume y z := hψmono.intervalIntegrable
  have hzx_int : IntervalIntegrable ψ MeasureTheory.volume z x := hψmono.intervalIntegrable
  have hx_split :
      ∫ u in 0..x, ψ u = (∫ u in 0..z, ψ u) + ∫ u in z..x, ψ u := by
    -- Split the primitive at the intermediate point `z`.
    have hsub :=
      intervalIntegral.integral_interval_sub_left (a := 0) (b := x) (c := z) (f := ψ)
        hx_int hz_int
    exact sub_eq_iff_eq_add'.mp hsub
  have hy_split :
      ∫ u in 0..y, ψ u = (∫ u in 0..z, ψ u) - ∫ u in y..z, ψ u := by
    -- The left endpoint primitive is the `z`-primitive minus the left increment.
    have hsub :=
      intervalIntegral.integral_interval_sub_left (a := 0) (b := z) (c := y) (f := ψ)
        hz_int hy_int
    have hsplit : ∫ u in 0..z, ψ u = (∫ u in 0..y, ψ u) + ∫ u in y..z, ψ u :=
      sub_eq_iff_eq_add'.mp hsub
    linarith
  have hzx_bound : (x - z) * ψ z ≤ ∫ u in z..x, ψ u := by
    -- Monotonicity bounds the right increment below by the constant value `ψ z`.
    have hconst_int :
        IntervalIntegrable (fun _ : ℝ ↦ ψ z) MeasureTheory.volume z x := intervalIntegrable_const
    have hmono :=
      intervalIntegral.integral_mono_on (a := z) (b := x) (f := fun _ : ℝ ↦ ψ z) (g := ψ)
        hzx hconst_int hzx_int (fun u hu ↦ hψmono hu.1)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono
  have hyz_bound : ∫ u in y..z, ψ u ≤ (z - y) * ψ z := by
    -- Monotonicity bounds the left increment above by the same constant value `ψ z`.
    have hconst_int :
        IntervalIntegrable (fun _ : ℝ ↦ ψ z) MeasureTheory.volume y z := intervalIntegrable_const
    have hmono :=
      intervalIntegral.integral_mono_on (a := y) (b := z) (f := ψ) (g := fun _ : ℝ ↦ ψ z)
        hyz hyz_int hconst_int (fun u hu ↦ hψmono hu.2)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono
  have hxz_eq : x - z = (1 - t) * (x - y) := by
    -- These are the standard affine-combination distance identities.
    dsimp [z]
    ring
  have hzy_eq : z - y = t * (x - y) := by
    dsimp [z]
    ring
  -- The two increment bounds give the Jensen inequality after expanding the primitive at `z`.
  rw [hx_split, hy_split]
  nlinarith [hzx_bound, hyz_bound, hxz_eq, hzy_eq, ht0, ht1]

/-- Helper for Example 8.22: the primitive of a monotone function satisfies Jensen's inequality on
all of `ℝ`. -/
lemma integral_primitive_jensen_le (ψ : ℝ → ℝ) (x y t : ℝ) (hψmono : Monotone ψ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ u in 0..(t * x + (1 - t) * y), ψ u ≤
      t * (∫ u in 0..x, ψ u) + (1 - t) * (∫ u in 0..y, ψ u) := by
  rcases le_total y x with hyx | hxy
  · -- In the ordered case, apply the previous interval comparison directly.
    exact integral_primitive_jensen_le_of_le ψ x y t hψmono hyx ht0 ht1
  · -- Otherwise swap the endpoints and replace `t` by `1 - t`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc]
      using integral_primitive_jensen_le_of_le ψ y x (1 - t) hψmono hxy
        (sub_nonneg.mpr ht1) (by nlinarith)

/-- Helper for Example 8.22: when `y < x`, the primitive of a strictly monotone function satisfies
the strict ordered Jensen inequality at the affine point `t * x + (1 - t) * y`. -/
private lemma integral_primitive_jensen_lt_of_lt (ψ : ℝ → ℝ) (x y t : ℝ)
    (hψstrict : StrictMono ψ) (hyx : y < x) (ht0 : 0 < t) (ht1 : t < 1) :
    ∫ u in 0..(t * x + (1 - t) * y), ψ u <
      t * (∫ u in 0..x, ψ u) + (1 - t) * (∫ u in 0..y, ψ u) := by
  let z := t * x + (1 - t) * y
  have hyz : y < z := by
    -- The affine point lies strictly between the endpoints when `0 < t < 1`.
    dsimp [z]
    nlinarith
  have hzx : z < x := by
    dsimp [z]
    nlinarith
  have hz_int : IntervalIntegrable ψ MeasureTheory.volume 0 z := hψstrict.monotone.intervalIntegrable
  have hx_int : IntervalIntegrable ψ MeasureTheory.volume 0 x := hψstrict.monotone.intervalIntegrable
  have hy_int : IntervalIntegrable ψ MeasureTheory.volume 0 y := hψstrict.monotone.intervalIntegrable
  have hyz_int : IntervalIntegrable ψ MeasureTheory.volume y z := hψstrict.monotone.intervalIntegrable
  have hzx_int : IntervalIntegrable ψ MeasureTheory.volume z x := hψstrict.monotone.intervalIntegrable
  have hx_split :
      ∫ u in 0..x, ψ u = (∫ u in 0..z, ψ u) + ∫ u in z..x, ψ u := by
    -- Split the primitive at the interior point `z`.
    have hsub :=
      intervalIntegral.integral_interval_sub_left (a := 0) (b := x) (c := z) (f := ψ)
        hx_int hz_int
    exact sub_eq_iff_eq_add'.mp hsub
  have hy_split :
      ∫ u in 0..y, ψ u = (∫ u in 0..z, ψ u) - ∫ u in y..z, ψ u := by
    -- The left endpoint primitive is again the `z`-primitive minus the left increment.
    have hsub :=
      intervalIntegral.integral_interval_sub_left (a := 0) (b := z) (c := y) (f := ψ)
        hz_int hy_int
    have hsplit : ∫ u in 0..z, ψ u = (∫ u in 0..y, ψ u) + ∫ u in y..z, ψ u :=
      sub_eq_iff_eq_add'.mp hsub
    linarith
  have hright_pos :
      0 < ∫ u in z..x, (ψ u - ψ z) := by
    -- Strict monotonicity makes the right-hand comparison gap pointwise positive.
    have hdiff_int :
        IntervalIntegrable (fun u : ℝ ↦ ψ u - ψ z) MeasureTheory.volume z x := by
      exact hzx_int.sub intervalIntegrable_const
    exact intervalIntegral.intervalIntegral_pos_of_pos_on hdiff_int
      (fun u hu ↦ sub_pos.mpr (hψstrict hu.1)) hzx
  have hleft_pos :
      0 < ∫ u in y..z, (ψ z - ψ u) := by
    -- The symmetric left-hand comparison gap is also strictly positive.
    have hconst_int :
        IntervalIntegrable (fun _ : ℝ ↦ ψ z) MeasureTheory.volume y z := intervalIntegrable_const
    have hdiff_int :
        IntervalIntegrable (fun u : ℝ ↦ ψ z - ψ u) MeasureTheory.volume y z := by
      exact hconst_int.sub hyz_int
    exact intervalIntegral.intervalIntegral_pos_of_pos_on hdiff_int
      (fun u hu ↦ sub_pos.mpr (hψstrict hu.2)) hyz
  have hright :
      (x - z) * ψ z < ∫ u in z..x, ψ u := by
    -- Expand the positive gap integral into the desired strict lower bound.
    have hconst_int :
        IntervalIntegrable (fun _ : ℝ ↦ ψ z) MeasureTheory.volume z x := intervalIntegrable_const
    have h := hright_pos
    rw [intervalIntegral.integral_sub hzx_int hconst_int,
      intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  have hleft :
      ∫ u in y..z, ψ u < (z - y) * ψ z := by
    -- Expand the positive left gap integral into the corresponding strict upper bound.
    have hconst_int :
        IntervalIntegrable (fun _ : ℝ ↦ ψ z) MeasureTheory.volume y z := intervalIntegrable_const
    have h := hleft_pos
    rw [intervalIntegral.integral_sub hconst_int hyz_int,
      intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  have hxz_eq : x - z = (1 - t) * (x - y) := by
    -- These identities convert the increment estimates into the strict Jensen gap.
    dsimp [z]
    ring
  have hzy_eq : z - y = t * (x - y) := by
    dsimp [z]
    ring
  rw [hx_split, hy_split]
  nlinarith [hright, hleft, hxz_eq, hzy_eq, ht0, ht1]

/-- Helper for Example 8.22: the primitive of a strictly monotone function satisfies the strict
Jensen inequality on all of `ℝ`. -/
lemma integral_primitive_jensen_lt (ψ : ℝ → ℝ) (x y t : ℝ) (hψstrict : StrictMono ψ)
    (hxy : x ≠ y) (ht0 : 0 < t) (ht1 : t < 1) :
    ∫ u in 0..(t * x + (1 - t) * y), ψ u <
      t * (∫ u in 0..x, ψ u) + (1 - t) * (∫ u in 0..y, ψ u) := by
  rcases lt_or_gt_of_ne hxy with hxy_lt | hyx_lt
  · -- If `x < y`, swap the endpoints and replace `t` by `1 - t`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc]
      using integral_primitive_jensen_lt_of_lt ψ y x (1 - t) hψstrict hxy_lt
        (sub_pos.mpr ht1) (by nlinarith)
  · -- If `y < x`, apply the ordered strict inequality directly.
    exact integral_primitive_jensen_lt_of_lt ψ x y t hψstrict hyx_lt ht0 ht1

/-- Helper for Example 8.22: the primitive `s ↦ ∫ t in 0..s, ψ t` is monotone on `[0,+∞)` when
`ψ` is increasing and `ψ 0 ≥ 0`. -/
lemma integral_primitive_monotoneOn_Ici_zero (ψ : ℝ → ℝ) (hψmono : Monotone ψ)
    (hψ0 : 0 ≤ ψ 0) :
    MonotoneOn (fun s : ℝ ↦ ∫ t in 0..s, ψ t) (Set.Ici 0) := by
  intro s hs t ht hst
  -- Split the larger primitive at `s` so the difference is the nonnegative increment on `s..t`.
  have hs_int : IntervalIntegrable ψ MeasureTheory.volume 0 s := hψmono.intervalIntegrable
  have ht_int : IntervalIntegrable ψ MeasureTheory.volume 0 t := hψmono.intervalIntegrable
  have hst_int : IntervalIntegrable ψ MeasureTheory.volume s t := hψmono.intervalIntegrable
  have hsplit_raw :=
    intervalIntegral.integral_interval_sub_left (a := 0) (b := t) (c := s) (f := ψ) ht_int hs_int
  have hsplit : ∫ u in 0..t, ψ u = (∫ u in 0..s, ψ u) + ∫ u in s..t, ψ u := by
    exact sub_eq_iff_eq_add'.mp hsplit_raw
  have hinc_nonneg : 0 ≤ ∫ u in s..t, ψ u := by
    -- Monotonicity pushes the lower bound `ψ 0 ≥ 0` across the whole interval `[s,t]`.
    exact intervalIntegral.integral_nonneg hst fun u hu ↦ by
      have hu0 : 0 ≤ u := le_trans hs hu.1
      exact le_trans hψ0 (hψmono hu0)
  linarith

/-- Helper for Example 8.22: the primitive `s ↦ ∫ t in 0..s, ψ t` is strictly increasing on
`[0,+∞)` when `ψ` is strictly increasing and `ψ 0 ≥ 0`. -/
lemma integral_primitive_strictMonoOn_Ici_zero (ψ : ℝ → ℝ) (hψstrict : StrictMono ψ)
    (hψ0 : 0 ≤ ψ 0) :
    StrictMonoOn (fun s : ℝ ↦ ∫ t in 0..s, ψ t) (Set.Ici 0) := by
  intro s hs t ht hst
  -- Split the larger primitive at `s`; the increment is strictly positive on a positive-length
  -- interval because strict monotonicity makes `ψ` positive away from `0`.
  have hs_int : IntervalIntegrable ψ MeasureTheory.volume 0 s := hψstrict.monotone.intervalIntegrable
  have ht_int : IntervalIntegrable ψ MeasureTheory.volume 0 t := hψstrict.monotone.intervalIntegrable
  have hst_int : IntervalIntegrable ψ MeasureTheory.volume s t := hψstrict.monotone.intervalIntegrable
  have hsplit_raw :=
    intervalIntegral.integral_interval_sub_left (a := 0) (b := t) (c := s) (f := ψ) ht_int hs_int
  have hsplit : ∫ u in 0..t, ψ u = (∫ u in 0..s, ψ u) + ∫ u in s..t, ψ u := by
    exact sub_eq_iff_eq_add'.mp hsplit_raw
  have hinc_pos : 0 < ∫ u in s..t, ψ u := by
    -- Every interior point `u ∈ (s,t)` satisfies `u > 0`, hence `ψ u > ψ 0 ≥ 0`.
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hst_int ?_ hst
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt hs hu.1
    exact lt_of_le_of_lt hψ0 (hψstrict hu0)
  linarith

/-- Helper for Example 8.22: the scalar primitive `s ↦ ∫ t in 0..s, ψ t` is convex on `ℝ` when
`ψ` is increasing. -/
lemma integral_primitive_convexOn_univ (ψ : ℝ → ℝ) (hψmono : Monotone ψ) :
    ConvexOn ℝ Set.univ (fun s : ℝ ↦ ∫ t in 0..s, ψ t) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hba : 1 - a = b := by
    nlinarith
  -- This is exactly the Jensen inequality from Example 8.15 with `α = 0`.
  simpa [smul_eq_mul, hba] using
    integral_primitive_jensen_le ψ x y a hψmono ha (by nlinarith)

-- Proof sketch: set `φ := integralIciExtension ψ 0`. Example 8.15 gives convexity of `φ`, while
-- `ψ(0) ≥ 0` and monotonicity imply that `φ` is increasing on `[0,+∞)`. Then combine the convex
-- norm from Example 8.9 with the composition principle of Proposition 8.21.
/-- If `ψ` is increasing with `ψ 0 ≥ 0`, then the radial primitive
`x ↦ ∫ t in 0..‖x‖, ψ t` is convex on the whole space. -/
theorem convexOn_univ_radialIntegral (ψ : ℝ → ℝ) (hψmono : Monotone ψ) (hψ0 : 0 ≤ ψ 0) :
    ConvexOn ℝ Set.univ (fun x : E ↦ ∫ t in 0..‖x‖, ψ t) := by
  let φ : ℝ → ℝ := fun s ↦ ∫ t in 0..s, ψ t
  have hφmono : MonotoneOn φ (Set.Ici 0) := integral_primitive_monotoneOn_Ici_zero ψ hψmono hψ0
  have hφconv : ConvexOn ℝ Set.univ φ := integral_primitive_convexOn_univ ψ hψmono
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hle_norm : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    -- Convexity of the norm controls the radius of the affine combination.
    simpa [smul_eq_mul] using
      convexOn_univ_norm.2 (by simp) (by simp) ha hb hab
  have hweighted_nonneg : 0 ≤ a * ‖x‖ + b * ‖y‖ := by
    nlinarith [ha, hb, norm_nonneg x, norm_nonneg y]
  have hmono_step :
      φ ‖a • x + b • y‖ ≤ φ (a * ‖x‖ + b * ‖y‖) :=
    hφmono (norm_nonneg _) hweighted_nonneg hle_norm
  have hconv_step :
      φ (a * ‖x‖ + b * ‖y‖) ≤ a * φ ‖x‖ + b * φ ‖y‖ := by
    -- Apply convexity of the scalar primitive at the two radii.
    simpa [φ, smul_eq_mul] using hφconv.2 (by simp) (by simp) ha hb hab
  -- Chaining the norm bound with scalar convexity proves convexity of the radial primitive.
  exact hmono_step.trans hconv_step

end Normed

section StrictConvex

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [StrictConvexSpace ℝ H]

/-- Helper for Example 8.22: the scalar primitive `s ↦ ∫ t in 0..s, ψ t` is strictly convex on
`ℝ` when `ψ` is strictly increasing. -/
lemma integral_primitive_strictConvexOn_univ (ψ : ℝ → ℝ) (hψstrict : StrictMono ψ) :
    StrictConvexOn ℝ Set.univ (fun s : ℝ ↦ ∫ t in 0..s, ψ t) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have hba : 1 - a = b := by
    nlinarith
  -- This is the strict Jensen inequality from Example 8.15 with `α = 0`.
  simpa [smul_eq_mul, hba] using
    integral_primitive_jensen_lt ψ x y a hψstrict hxy ha (by nlinarith)

-- Proof sketch: write `x ↦ ∫ t in 0..‖x‖, ψ t` as `φ ∘ ‖·‖` with
-- `φ(s) = ∫ t in 0..s, ψ t`. When
-- `‖x‖ ≠ ‖y‖`, combine convexity of the norm with strict convexity of `φ` from Example 8.15. When
-- `‖x‖ = ‖y‖`, strict convexity of the ambient space yields
-- `‖α • x + (1 - α) • y‖ < ‖x‖` for `x ≠ y`, and strict monotonicity of `φ` finishes.
/-- If `ψ` is strictly increasing and `ψ 0 ≥ 0`, then the radial primitive
`x ↦ ∫ t in 0..‖x‖, ψ t` is strictly convex on the whole space of a strictly convex real normed
space. -/
theorem strictConvexOn_univ_radialIntegral (ψ : ℝ → ℝ) (hψstrict : StrictMono ψ)
    (hψ0 : 0 ≤ ψ 0) :
    StrictConvexOn ℝ Set.univ (fun x : H ↦ ∫ t in 0..‖x‖, ψ t) := by
  let φ : ℝ → ℝ := fun s ↦ ∫ t in 0..s, ψ t
  have hφmono : MonotoneOn φ (Set.Ici 0) :=
    integral_primitive_monotoneOn_Ici_zero ψ hψstrict.monotone hψ0
  have hφstrictMono : StrictMonoOn φ (Set.Ici 0) :=
    integral_primitive_strictMonoOn_Ici_zero ψ hψstrict hψ0
  have hφstrictConv : StrictConvexOn ℝ Set.univ φ :=
    integral_primitive_strictConvexOn_univ ψ hψstrict
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  by_cases hnorm : ‖x‖ = ‖y‖
  · have hlt_norm : ‖a • x + b • y‖ < ‖x‖ := by
      -- Route correction: when the radii agree, strict convexity comes from the ambient geometry
      -- rather than from strict convexity of the outer scalar primitive.
      refine norm_combo_lt_of_ne le_rfl ?_ hxy ha hb hab
      simp [hnorm]
    have hlt_φ : φ ‖a • x + b • y‖ < φ ‖x‖ :=
      hφstrictMono (norm_nonneg _) (norm_nonneg _) hlt_norm
    calc
      φ ‖a • x + b • y‖ < φ ‖x‖ := hlt_φ
      _ = a * φ ‖x‖ + b * φ ‖y‖ := by
        rw [hnorm, ← add_mul, hab, one_mul]
  · have hle_norm : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
      -- When the radii differ, combine convexity of the norm with strict convexity of `φ`.
      simpa [smul_eq_mul] using
        convexOn_univ_norm.2 (by simp) (by simp) ha.le hb.le hab
    have hweighted_nonneg : 0 ≤ a * ‖x‖ + b * ‖y‖ := by
      nlinarith [ha, hb, norm_nonneg x, norm_nonneg y]
    have hmono_step :
        φ ‖a • x + b • y‖ ≤ φ (a * ‖x‖ + b * ‖y‖) :=
      hφmono (norm_nonneg _) hweighted_nonneg hle_norm
    have hstrict_step :
        φ (a * ‖x‖ + b * ‖y‖) < a * φ ‖x‖ + b * φ ‖y‖ := by
      simpa [φ, smul_eq_mul] using hφstrictConv.2 (by simp) (by simp) hnorm ha hb hab
    exact lt_of_le_of_lt hmono_step hstrict_step

end StrictConvex
