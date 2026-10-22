/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_42

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

noncomputable section NormPowerPerspectiveAtOrigin

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

open scoped Topology

local instance : DecidableEq H := Classical.decEq H

omit [NormedSpace ℝ H] in
private theorem normPower_toEReal_nonempty (p : ℝ) :
    (effectiveDomain ((fun x : H ↦ ‖x‖ ^ p).toEReal)).Nonempty := by
  simp

/-- Helper for Example 9.43: the recession function of `x ↦ ‖x‖ ^ p` vanishes at the origin. -/
private theorem recessionFunction_normPower_toEReal_zero
    (p : ℝ) :
    (recessionFunction ((fun x : H ↦ ‖x‖ ^ p).toEReal)
      (normPower_toEReal_nonempty (H := H) p) (0 : H) : EReal) = 0 := by
  -- On the zero direction every translated increment is the self-difference `f x - f x = 0`.
  rw [recessionFunction_apply]
  have himage :
      ((fun x : H ↦
          (((fun x : H ↦ ‖x‖ ^ p).toEReal (x + 0) : EReal) -
            ((fun x : H ↦ ‖x‖ ^ p).toEReal x : EReal))) ''
        effectiveDomain ((fun x : H ↦ ‖x‖ ^ p).toEReal)) = ({0} : Set EReal) := by
    ext a
    constructor
    · intro ha
      rcases ha with ⟨x, -, rfl⟩
      simp
    · intro ha
      rcases normPower_toEReal_nonempty (H := H) p with ⟨x, hx⟩
      rw [Set.mem_singleton_iff] at ha
      subst a
      refine ⟨x, hx, ?_⟩
      simp
  simpa [himage]

/-- Helper for Example 9.43: along a nonzero ray, the norm-power translated increment dominates a
positive multiple of `t ^ (p - 1)`. -/
private theorem ray_increment_norm_rpow_lower_bound
    (p : ℝ) (hp : 1 < p) {y : H} (hy : y ≠ 0) (t : Set.Ioi (0 : ℝ)) :
    (p * ‖y‖ ^ p) * (t : ℝ) ^ (p - 1) ≤
      ((((t : ℝ) + 1) ^ p - (t : ℝ) ^ p) * ‖y‖ ^ p : ℝ) := by
  have ht_pos : 0 < (t : ℝ) := t.2
  have ht_nonneg : 0 ≤ (t : ℝ) := ht_pos.le
  have hnorm_pow_nonneg : 0 ≤ ‖y‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  have hbern :
      1 + p * ((t : ℝ)⁻¹) ≤ (1 + (t : ℝ)⁻¹) ^ p :=
    one_add_mul_self_le_rpow_one_add (by
      have hinv_nonneg : 0 ≤ ((t : ℝ)⁻¹) := by positivity
      linarith) hp.le
  have hmul :
      (t : ℝ) ^ p * (1 + p * ((t : ℝ)⁻¹)) ≤
        (t : ℝ) ^ p * (1 + (t : ℝ)⁻¹) ^ p := by
    exact mul_le_mul_of_nonneg_left hbern (Real.rpow_nonneg ht_nonneg _)
  have hleft :
      (t : ℝ) ^ p * (1 + p * ((t : ℝ)⁻¹)) =
        (t : ℝ) ^ p + (p * (t : ℝ) ^ (p - 1)) := by
    have hsub :
        (t : ℝ) ^ p * ((t : ℝ)⁻¹) = (t : ℝ) ^ (p - 1) := by
      calc
        (t : ℝ) ^ p * ((t : ℝ)⁻¹) = (t : ℝ) ^ p / (t : ℝ) := by
          rw [div_eq_mul_inv]
        _ = (t : ℝ) ^ (p - 1) := by
          simpa [Real.rpow_one] using (Real.rpow_sub ht_pos p 1).symm
    calc
      (t : ℝ) ^ p * (1 + p * ((t : ℝ)⁻¹))
          = (t : ℝ) ^ p + ((t : ℝ) ^ p * (p * ((t : ℝ)⁻¹))) := by ring
      _ = (t : ℝ) ^ p + (p * ((t : ℝ) ^ p * ((t : ℝ)⁻¹))) := by ring
      _ = (t : ℝ) ^ p + (p * (t : ℝ) ^ (p - 1)) := by
        rw [hsub]
  have hright :
      (t : ℝ) ^ p * (1 + (t : ℝ)⁻¹) ^ p = ((t : ℝ) + 1) ^ p := by
    calc
      (t : ℝ) ^ p * (1 + (t : ℝ)⁻¹) ^ p
          = (((t : ℝ) * (1 + (t : ℝ)⁻¹)) ^ p : ℝ) := by
              symm
              rw [Real.mul_rpow ht_nonneg (by positivity)]
      _ = ((t : ℝ) + 1) ^ p := by
        congr 1
        field_simp [ht_pos.ne']
  have hmain :
      p * (t : ℝ) ^ (p - 1) ≤ ((t : ℝ) + 1) ^ p - (t : ℝ) ^ p := by
    have hmain' :
        (t : ℝ) ^ p + (p * (t : ℝ) ^ (p - 1)) ≤ ((t : ℝ) + 1) ^ p := by
      simpa [hleft, hright] using hmul
    linarith
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right hmain hnorm_pow_nonneg

/-- Helper for Example 9.43: along a nonzero ray, the translated increment of `x ↦ ‖x‖ ^ p`
tends to `+∞`. -/
private theorem tendsto_ray_increment_norm_rpow_toEReal_atTop
    (p : ℝ) (hp : 1 < p) {y : H} (hy : y ≠ 0) :
    Filter.Tendsto
      (fun t : Set.Ioi (0 : ℝ) ↦
        (((((t : ℝ) + 1) ^ p - (t : ℝ) ^ p) * ‖y‖ ^ p : ℝ) : EReal))
      Filter.atTop (nhds (⊤ : EReal)) := by
  have hp_sub_pos : 0 < p - 1 := by
    linarith
  have hy_norm_pow_pos : 0 < ‖y‖ ^ p := by
    exact Real.rpow_pos_of_pos (norm_pos_iff.mpr hy) _
  have hlower_real :
      Filter.Tendsto
        (fun t : Set.Ioi (0 : ℝ) ↦ (p * ‖y‖ ^ p) * (t : ℝ) ^ (p - 1))
        Filter.atTop Filter.atTop := by
    have hpow :
        Filter.Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ (t : ℝ) ^ (p - 1))
          Filter.atTop Filter.atTop := by
      refine (tendsto_rpow_atTop hp_sub_pos).comp ?_
      simpa [Filter.Tendsto] using (Filter.map_val_Ioi_atTop (0 : ℝ))
    exact Filter.Tendsto.const_mul_atTop (by positivity) hpow
  have hincrement_real :
      Filter.Tendsto
        (fun t : Set.Ioi (0 : ℝ) ↦
          ((((t : ℝ) + 1) ^ p - (t : ℝ) ^ p) * ‖y‖ ^ p : ℝ))
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono
      (fun t ↦ ray_increment_norm_rpow_lower_bound (H := H) p hp hy t) hlower_real
  refine EReal.tendsto_nhds_top_iff_real.2 ?_
  intro b
  have hb' :
      ∀ᶠ t : Set.Ioi (0 : ℝ) in Filter.atTop,
        b + 1 ≤ ((((t : ℝ) + 1) ^ p - (t : ℝ) ^ p) * ‖y‖ ^ p : ℝ) :=
    Filter.tendsto_atTop.mp hincrement_real (b + 1)
  filter_upwards [hb'] with t ht
  exact_mod_cast lt_of_lt_of_le (lt_add_one b) ht

/-- Helper for Example 9.43: the recession function of `x ↦ ‖x‖ ^ p` is the indicator of the
origin. -/
private theorem recessionFunction_normPower_toEReal_eq_origin_indicator
    (p : ℝ) (hp : 1 < p) (y : H) :
    (recessionFunction ((fun x : H ↦ ‖x‖ ^ p).toEReal)
      (normPower_toEReal_nonempty (H := H) p) y : EReal) =
      if y = 0 then 0 else ⊤ := by
  by_cases hy : y = 0
  · -- The zero direction is the exceptional finite branch.
    subst hy
    simpa using recessionFunction_normPower_toEReal_zero (H := H) p
  · -- Route correction: instead of relying on the Hilbert-only supercoercive API, evaluate the
    -- defining supremum directly along the ray `x = t • y`.
    rw [recessionFunction_apply]
    have hsSup :
        sSup
            ((fun x : H ↦
                (((fun x : H ↦ ‖x‖ ^ p).toEReal (x + y) : EReal) -
                  ((fun x : H ↦ ‖x‖ ^ p).toEReal x : EReal))) ''
              effectiveDomain ((fun x : H ↦ ‖x‖ ^ p).toEReal)) = (⊤ : EReal) := by
      rw [EReal.eq_top_iff_forall_lt]
      intro q
      have hqevent :
          ∀ᶠ t : Set.Ioi (0 : ℝ) in Filter.atTop,
            ((q : ℝ) : EReal) <
              ((((t : ℝ) + 1) ^ p - (t : ℝ) ^ p) * ‖y‖ ^ p : ℝ) := by
        simpa using
          (EReal.tendsto_nhds_top_iff_real.1
            (tendsto_ray_increment_norm_rpow_toEReal_atTop (H := H) p hp hy)) (q : ℝ)
      rcases Filter.Eventually.exists hqevent with ⟨t, ht⟩
      refine lt_of_lt_of_le ht (le_sSup ?_)
      refine ⟨(t : ℝ) • y, ?_, ?_⟩
      · simp [effectiveDomain]
      · have ht_pos : 0 < (t : ℝ) := t.2
        have hinc :
            (((fun x : H ↦ ‖x‖ ^ p).toEReal (((t : ℝ) • y) + y) : EReal) -
                ((fun x : H ↦ ‖x‖ ^ p).toEReal ((t : ℝ) • y) : EReal)) =
              (((((t : ℝ) + 1) ^ p - (t : ℝ) ^ p) * ‖y‖ ^ p : ℝ) : EReal) := by
          rw [Function.toEReal_apply, Function.toEReal_apply, ← EReal.coe_sub]
          · have hnorm_add :
              ‖((t : ℝ) • y) + y‖ = ((t : ℝ) + 1) * ‖y‖ := by
              calc
                ‖((t : ℝ) • y) + y‖ = ‖((t : ℝ) • y + (1 : ℝ) • y)‖ := by rw [one_smul]
                _ = ‖(((t : ℝ) + 1) • y)‖ := by rw [← add_smul]
                _ = ((t : ℝ) + 1) * ‖y‖ := by
                      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
            have hnorm_smul :
                ‖(t : ℝ) • y‖ = (t : ℝ) * ‖y‖ := by
              rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
            rw [hnorm_add, hnorm_smul, Real.mul_rpow (by positivity) (norm_nonneg _),
              Real.mul_rpow ht_pos.le (norm_nonneg _)]
            ring
        simpa using hinc
    simpa [hy] using hsSup

/-- The source-facing function of Example 9.43, realized by the canonical closed perspective of the
norm-power function. -/
noncomputable def normPowerPerspectiveAtOrigin (p : ℝ) : ℝ × H → Set.Ioi (⊥ : EReal) :=
  closedPerspective ((fun x : H ↦ ‖x‖ ^ p).toEReal) (normPower_toEReal_nonempty p)

-- Proof sketch: evaluate the canonical `closedPerspective` specialized to `x ↦ ‖x‖ ^ p`. For
-- positive height the ordinary perspective simplifies to `‖x‖^p / ξ^(p - 1)`, while on the
-- zero-height slice Example 9.32 identifies the recession function with the indicator of `{0}`.
/-- Evaluating `normPowerPerspectiveAtOrigin` gives the explicit textbook formula of
Example 9.43. -/
@[simp] theorem normPowerPerspectiveAtOrigin_apply
    (p : ℝ) (hp : 1 < p) (z : ℝ × H) :
    (normPowerPerspectiveAtOrigin p z : EReal) =
      if 0 < z.1 then
        ((‖z.2‖ ^ p / z.1 ^ (p - 1) : ℝ) : EReal)
      else if z = (0, (0 : H)) then
        0
      else
        ⊤ := by
  rcases z with ⟨ξ, x⟩
  by_cases hξ_pos : 0 < ξ
  · -- Positive heights are exactly the ordinary perspective branch.
    have hξ_ne : ξ ≠ 0 := ne_of_gt hξ_pos
    rw [normPowerPerspectiveAtOrigin, closedPerspective_coe,
      closedPerspectiveEReal_apply_of_ne_zero (φ := (fun x : H ↦ ‖x‖ ^ p).toEReal)
        (hdom := normPower_toEReal_nonempty (H := H) p) hξ_ne,
      if_pos hξ_pos]
    simp [perspective, hξ_pos]
    have hnorm_smul : ‖ξ⁻¹ • x‖ = ξ⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hξ_pos.le)]
    have hξpow : ξ ^ p = ξ ^ (p - 1) * ξ := by
      rw [show p = (p - 1) + 1 by ring, Real.rpow_add hξ_pos]
      simp
    have hreal :
        ξ * ‖ξ⁻¹ • x‖ ^ p = ‖x‖ ^ p / ξ ^ (p - 1) := by
      calc
      ξ * ‖ξ⁻¹ • x‖ ^ p
          = ξ * ((‖x‖ / ξ) ^ p) := by
              rw [hnorm_smul]
              congr 1
              field_simp [hξ_ne]
      _ = ξ * (‖x‖ ^ p / ξ ^ p) := by
            rw [Real.div_rpow (norm_nonneg _) hξ_pos.le]
      _ = ξ * (‖x‖ ^ p / (ξ ^ (p - 1) * ξ)) := by rw [hξpow]
      _ = ‖x‖ ^ p / ξ ^ (p - 1) := by
            field_simp [hξ_ne]
    exact_mod_cast hreal
  · -- On the zero-height slice the recession function is the indicator of `{0}`.
    by_cases hz : (ξ, x) = (0, (0 : H))
    · rcases Prod.mk.inj hz with ⟨rfl, rfl⟩
      rw [normPowerPerspectiveAtOrigin, closedPerspective_coe,
        closedPerspectiveEReal_apply_zero,
        recessionFunction_normPower_toEReal_eq_origin_indicator (H := H) p hp (0 : H)]
      simp [hξ_pos]
    · have hξ_nonpos : ξ ≤ 0 := le_of_not_gt hξ_pos
      rw [normPowerPerspectiveAtOrigin, closedPerspective_coe]
      by_cases hξ_zero : ξ = 0
      · subst hξ_zero
        have hx_ne : x ≠ 0 := by
          intro hx_zero
          exact hz (by simp [hx_zero])
        rw [closedPerspectiveEReal_apply_zero,
          recessionFunction_normPower_toEReal_eq_origin_indicator (H := H) p hp x]
        simp [hx_ne]
      · rw [closedPerspectiveEReal_apply_of_ne_zero
            (φ := (fun x : H ↦ ‖x‖ ^ p).toEReal)
            (hdom := normPower_toEReal_nonempty (H := H) p) hξ_zero]
        simp [perspective, hξ_nonpos, hξ_pos, hz]

/-- Helper for Example 9.43: the effective domain consists of the positive-height slice together
with the origin. -/
private theorem mem_effectiveDomain_normPowerPerspectiveAtOrigin_iff
    (p : ℝ) (hp : 1 < p) (z : ℝ × H) :
    z ∈ effectiveDomain (normPowerPerspectiveAtOrigin p) ↔
      0 < z.1 ∨ z = (0, (0 : H)) := by
  rw [mem_effectiveDomain_iff, normPowerPerspectiveAtOrigin_apply (H := H) p hp z]
  by_cases hξ : 0 < z.1
  · simp [hξ]
  · by_cases hz : z = (0, (0 : H))
    · simp [hξ, hz]
    · simp [hξ, hz]

/-- Helper for Example 9.43: the closed perspective never takes values below `0`. -/
private theorem normPowerPerspectiveAtOrigin_nonneg
    (p : ℝ) (hp : 1 < p) (z : ℝ × H) :
    (0 : EReal) ≤ (normPowerPerspectiveAtOrigin p z : EReal) := by
  -- Every branch of the explicit formula is either a nonnegative real or `+∞`.
  rw [normPowerPerspectiveAtOrigin_apply (H := H) p hp z]
  by_cases hξ : 0 < z.1
  · rw [if_pos hξ]
    exact_mod_cast div_nonneg
      (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg hξ.le _)
  · by_cases hz : z = (0, (0 : H))
    · simp [hξ, hz]
    · simp [hξ, hz]

/-- Helper for Example 9.43: the real-height epigraph of `x ↦ ‖x‖ ^ p` is convex. -/
private theorem convex_epigraph_normPower_toEReal
    (p : ℝ) (hp : 1 < p) :
    Convex ℝ (epigraph (fun y : H ↦ (((‖y‖ ^ p : ℝ) : EReal)))) := by
  -- Convexity comes from the convexity of the norm and the convexity of `t ↦ t ^ p` on
  -- `[0, +∞)`.
  refine (convex_epigraph_iff_jensen_on_dom
    (fun y : H ↦ (((‖y‖ ^ p : ℝ) : EReal)))).2 ?_
  intro x y _hx _hy α hα0 hα1
  have hβ0 : 0 ≤ 1 - α := sub_nonneg.mpr hα1.le
  have hnorm :
      ‖α • x + (1 - α) • y‖ ≤ α * ‖x‖ + (1 - α) * ‖y‖ := by
    -- First use convexity of the norm itself.
    simpa [smul_eq_mul] using
      (convexOn_univ_norm.2 (by simp) (by simp) hα0.le hβ0 (by ring))
  have hpow_monotone :
      ‖α • x + (1 - α) • y‖ ^ p ≤ (α * ‖x‖ + (1 - α) * ‖y‖) ^ p := by
    -- Then raise both sides using monotonicity of `rpow` on nonnegative reals.
    exact Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith)
  have hpow_convex :
      (α * ‖x‖ + (1 - α) * ‖y‖) ^ p ≤ α * ‖x‖ ^ p + (1 - α) * ‖y‖ ^ p := by
    -- Finally apply convexity of `t ↦ t ^ p` on `[0, +∞)`.
    simpa [smul_eq_mul] using
      (convexOn_rpow hp.le).2
        (by simp [norm_nonneg]) (by simp [norm_nonneg]) hα0.le hβ0 (by ring)
  have hreal :
      ‖α • x + (1 - α) • y‖ ^ p ≤ α * ‖x‖ ^ p + (1 - α) * ‖y‖ ^ p :=
    le_trans hpow_monotone hpow_convex
  simpa using
    (show (((‖α • x + (1 - α) • y‖ ^ p : ℝ) : EReal)) ≤
        (α : EReal) * (((‖x‖ ^ p : ℝ) : EReal)) +
          ((1 - α : ℝ) : EReal) * (((‖y‖ ^ p : ℝ) : EReal)) from by
      exact_mod_cast hreal)

/-- Helper for Example 9.43: the perspective formula is positively homogeneous along rays. -/
private theorem normPowerPerspectiveAtOrigin_scale_pos
    (p : ℝ) (hp : 1 < p) {a ξ : ℝ} {x : H}
    (ha : 0 ≤ a) (hξ : 0 < ξ) :
    (normPowerPerspectiveAtOrigin p (a * ξ, a • x) : EReal) =
      (a : EReal) * (normPowerPerspectiveAtOrigin p (ξ, x) : EReal) := by
  by_cases ha_zero : a = 0
  · -- The zero scalar collapses both sides to the origin value.
    subst ha_zero
    have hleft : (normPowerPerspectiveAtOrigin p (0 * ξ, (0 : ℝ) • x) : EReal) = 0 := by
      simpa using (normPowerPerspectiveAtOrigin_apply (H := H) p hp (0, (0 : H)))
    calc
      (normPowerPerspectiveAtOrigin p (0 * ξ, (0 : ℝ) • x) : EReal) = 0 := hleft
      _ = (0 : EReal) * (normPowerPerspectiveAtOrigin p (ξ, x) : EReal) := by simp
  · have ha_ne : 0 ≠ a := by
        simpa [eq_comm] using ha_zero
    have ha_pos : 0 < a := lt_of_le_of_ne ha ha_ne
    have hp_sub_ne : p - 1 ≠ 0 := by
      linarith
    have hnorm_smul : ‖a • x‖ = a * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg ha]
    have hreal :
        ‖a • x‖ ^ p / (a * ξ) ^ (p - 1) = a * (‖x‖ ^ p / ξ ^ (p - 1)) := by
      have ha_pow_ne : a ^ (p - 1) ≠ 0 := by
        apply (Real.rpow_ne_zero ha hp_sub_ne).2
        exact ha_zero
      have hξ_pow_ne : ξ ^ (p - 1) ≠ 0 := by
        apply (Real.rpow_ne_zero hξ.le hp_sub_ne).2
        exact hξ.ne'
      calc
        ‖a • x‖ ^ p / (a * ξ) ^ (p - 1)
            = (a * ‖x‖) ^ p / (a * ξ) ^ (p - 1) := by
                rw [hnorm_smul]
        _ = (a ^ p * ‖x‖ ^ p) / (a ^ (p - 1) * ξ ^ (p - 1)) := by
              rw [Real.mul_rpow ha (norm_nonneg _), Real.mul_rpow ha hξ.le]
        _ = (a ^ p / a ^ (p - 1)) * (‖x‖ ^ p / ξ ^ (p - 1)) := by
              field_simp [ha_pow_ne, hξ_pow_ne]
        _ = a * (‖x‖ ^ p / ξ ^ (p - 1)) := by
              have ha_ratio : a ^ p / a ^ (p - 1) = a := by
                calc
                  a ^ p / a ^ (p - 1) = a ^ (p - (p - 1)) := by
                    symm
                    exact Real.rpow_sub ha_pos p (p - 1)
                  _ = a ^ (1 : ℝ) := by
                    congr
                    ring
                  _ = a := by
                    simp
              rw [ha_ratio]
    -- After evaluating both positive branches, the homogeneity is the real identity above.
    rw [normPowerPerspectiveAtOrigin_apply (H := H) p hp (a * ξ, a • x)]
    rw [normPowerPerspectiveAtOrigin_apply (H := H) p hp (ξ, x)]
    rw [if_pos (mul_pos ha_pos hξ), if_pos hξ]
    exact_mod_cast hreal

/-- Helper for Example 9.43: on the positive-height slice, the explicit closed perspective agrees
with the ordinary perspective of `u ↦ ‖u‖ ^ p`. -/
private theorem perspective_normPower_toEReal_apply_of_pos
    (p : ℝ) (hp : 1 < p) {z : ℝ × H} (hz : 0 < z.1) :
    perspective (fun u : H ↦ ((‖u‖ ^ p : ℝ) : EReal)) z =
      (normPowerPerspectiveAtOrigin p z : EReal) := by
  rcases z with ⟨ξ, x⟩
  have hξ_pos : 0 < ξ := by
    simpa using hz
  have hξ_ne : ξ ≠ 0 := ne_of_gt hξ_pos
  rw [perspective_apply_of_pos _ hξ_pos, normPowerPerspectiveAtOrigin_apply (H := H) p hp (ξ, x),
    if_pos hξ_pos]
  simp only
  have hnorm_smul : ‖ξ⁻¹ • x‖ = ξ⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hξ_pos.le)]
  have hξpow : ξ ^ p = ξ ^ (p - 1) * ξ := by
    rw [show p = (p - 1) + 1 by ring, Real.rpow_add hξ_pos]
    simp
  have hreal :
      ξ * ‖ξ⁻¹ • x‖ ^ p = ‖x‖ ^ p / ξ ^ (p - 1) := by
    calc
      ξ * ‖ξ⁻¹ • x‖ ^ p
          = ξ * ((‖x‖ / ξ) ^ p) := by
              rw [hnorm_smul]
              congr 1
              field_simp [hξ_ne]
      _ = ξ * (‖x‖ ^ p / ξ ^ p) := by
            rw [Real.div_rpow (norm_nonneg _) hξ_pos.le]
      _ = ξ * (‖x‖ ^ p / (ξ ^ (p - 1) * ξ)) := by
            rw [hξpow]
      _ = ‖x‖ ^ p / ξ ^ (p - 1) := by
            field_simp [hξ_ne]
  exact_mod_cast hreal

/-- Helper for Example 9.43: on the zero-height slice away from the origin, the explicit
perspective formula is lower semicontinuous because the positive branch blows up as `ξ → 0+`. -/
private theorem lowerSemicontinuousAt_normPowerPerspectiveAtOrigin_zero_slice_nonzero
    (p : ℝ) (hp : 1 < p) {x : H} (hx : x ≠ 0) :
    LowerSemicontinuousAt
      (fun z : ℝ × H ↦ (normPowerPerspectiveAtOrigin p z : EReal))
      (0, x) := by
  -- Use the neighborhood characterization of lower semicontinuity and force a uniform positive
  -- lower bound on nearby second coordinates.
  rw [lowerSemicontinuousAt_iff]
  intro β hβ
  rcases EReal.lt_iff_exists_real_btwn.mp hβ with ⟨M, hβM, -⟩
  let r : ℝ := ‖x‖ / 2
  have hr_pos : 0 < r := by
    have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    dsimp [r]
    positivity
  have hp_sub_pos : 0 < p - 1 := by
    linarith
  have hrpow_pos : 0 < r ^ p := Real.rpow_pos_of_pos hr_pos _
  have htendsto_div :
      Filter.Tendsto (fun ξ : ℝ ↦ r ^ p / ξ ^ (p - 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
    have htendsto_mul :
        Filter.Tendsto (fun ξ : ℝ ↦ r ^ p * ξ ^ (-(p - 1)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
      have htendsto_pow :
          Filter.Tendsto (fun ξ : ℝ ↦ ξ ^ (-(p - 1)))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
        apply tendsto_rpow_neg_nhdsGT_zero
        linarith
      exact Filter.Tendsto.const_mul_atTop hrpow_pos htendsto_pow
    refine Filter.Tendsto.congr' ?_ htendsto_mul
    filter_upwards [self_mem_nhdsWithin] with ξ hξ
    rw [div_eq_mul_inv, ← Real.rpow_neg hξ.le]
  have hlarge :
      {ξ : ℝ | M + 1 ≤ r ^ p / ξ ^ (p - 1)} ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    (Filter.tendsto_atTop.mp htendsto_div) (M + 1)
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hlarge with ⟨S, hS_nhds, hS_sub⟩
  have hnorm_nhds :
      {z : ℝ × H | r < ‖z.2‖} ∈ 𝓝 (0, x) := by
    have hIoi : Set.Ioi r ∈ 𝓝 ‖x‖ := by
      exact Ioi_mem_nhds (by
        dsimp [r]
        nlinarith [norm_pos_iff.mpr hx])
    exact (continuous_snd.norm.continuousAt).preimage_mem_nhds hIoi
  have hfst_nhds : {z : ℝ × H | z.1 ∈ S} ∈ 𝓝 (0, x) := by
    show Prod.fst ⁻¹' S ∈ 𝓝 (0, x)
    exact continuous_fst.continuousAt.preimage_mem_nhds hS_nhds
  have hnear :
      {z : ℝ × H | z.1 ∈ S} ∩ {z : ℝ × H | r < ‖z.2‖} ∈ 𝓝 (0, x) :=
    Filter.inter_mem hfst_nhds hnorm_nhds
  filter_upwards [hnear] with z hz
  rcases hz with ⟨hzS, hzNorm⟩
  by_cases hξ : 0 < z.1
  · -- On the positive branch, the nearby norm lower bound and the blow-up estimate force a large
    -- finite value.
    have hbound : M + 1 ≤ r ^ p / z.1 ^ (p - 1) := hS_sub ⟨hzS, hξ⟩
    have hnum_le : r ^ p ≤ ‖z.2‖ ^ p := by
      exact Real.rpow_le_rpow hr_pos.le hzNorm.le (by linarith)
    have hdiv_le :
        r ^ p / z.1 ^ (p - 1) ≤ ‖z.2‖ ^ p / z.1 ^ (p - 1) := by
      refine div_le_div_of_nonneg_right hnum_le ?_
      exact (Real.rpow_pos_of_pos hξ _).le
    have hreal_lt : M < ‖z.2‖ ^ p / z.1 ^ (p - 1) := by
      exact lt_of_lt_of_le (lt_add_one M) (le_trans hbound hdiv_le)
    have hM_lt :
        ((M : ℝ) : EReal) <
          (((‖z.2‖ ^ p / z.1 ^ (p - 1) : ℝ) : EReal)) := by
      exact_mod_cast hreal_lt
    rw [normPowerPerspectiveAtOrigin_apply (H := H) p hp z, if_pos hξ]
    exact lt_trans hβM hM_lt
  · -- Nonpositive nearby heights already land in the `+∞` branch.
    have hz_ne : z ≠ (0, (0 : H)) := by
      intro hz_eq
      have : ¬ r < ‖(0 : H)‖ := by
        simpa using (not_lt_of_ge hr_pos.le : ¬ r < 0)
      exact this (by simpa [hz_eq] using hzNorm)
    rw [normPowerPerspectiveAtOrigin_apply (H := H) p hp z, if_neg hξ, if_neg hz_ne]
    exact lt_trans hβM (EReal.coe_lt_top M)

/-- Helper for Example 9.43: the positive-height branch satisfies Jensen's inequality because it
is the ordinary perspective of the convex function `x ↦ ‖x‖ ^ p`. -/
private theorem jensen_normPowerPerspectiveAtOrigin_pos_pos
    (p : ℝ) (hp : 1 < p) {x y : ℝ × H} (hx : 0 < x.1) (hy : 0 < y.1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (normPowerPerspectiveAtOrigin p (α • x + (1 - α) • y) : EReal) ≤
      (α : EReal) * (normPowerPerspectiveAtOrigin p x : EReal) +
        (1 - α : EReal) * (normPowerPerspectiveAtOrigin p y : EReal) := by
  let F : H → EReal := fun u ↦ ((‖u‖ ^ p : ℝ) : EReal)
  have hF_conv : Convex ℝ (epigraph F) := by
    simpa [F] using convex_epigraph_normPower_toEReal (H := H) p hp
  have hx_dom : x ∈ dom (perspective F) := by
    rw [mem_dom_iff, perspective_apply_of_pos F hx]
    exact EReal.coe_lt_top _
  have hy_dom : y ∈ dom (perspective F) := by
    rw [mem_dom_iff, perspective_apply_of_pos F hy]
    exact EReal.coe_lt_top _
  have hxy_pos : 0 < (α • x + (1 - α) • y).1 := by
    have hβ0 : 0 < 1 - α := sub_pos.mpr hα1
    change 0 < α * x.1 + (1 - α) * y.1
    nlinarith
  have hJ :
      perspective F (α • x + (1 - α) • y) ≤
        (α : EReal) * perspective F x + (1 - α : EReal) * perspective F y :=
    (convex_epigraph_iff_jensen_on_dom (perspective F)).1
      (convex_epigraph_perspective F hF_conv) hx_dom hy_dom hα0 hα1
  have hleft :
      (normPowerPerspectiveAtOrigin p (α • x + (1 - α) • y) : EReal) =
        perspective F (α • x + (1 - α) • y) := by
    simpa [F] using
      (perspective_normPower_toEReal_apply_of_pos (H := H) p hp hxy_pos).symm
  have hx_eq : (normPowerPerspectiveAtOrigin p x : EReal) = perspective F x := by
    simpa [F] using
      (perspective_normPower_toEReal_apply_of_pos (H := H) p hp hx).symm
  have hy_eq : (normPowerPerspectiveAtOrigin p y : EReal) = perspective F y := by
    simpa [F] using
      (perspective_normPower_toEReal_apply_of_pos (H := H) p hp hy).symm
  -- Rewrite Jensen's inequality for the abstract perspective back to the explicit textbook
  -- formula on the positive slice.
  calc
    (normPowerPerspectiveAtOrigin p (α • x + (1 - α) • y) : EReal)
        = perspective F (α • x + (1 - α) • y) := hleft
    _ ≤ (α : EReal) * perspective F x + (1 - α : EReal) * perspective F y := hJ
    _ = (α : EReal) * (normPowerPerspectiveAtOrigin p x : EReal) +
          (1 - α : EReal) * (normPowerPerspectiveAtOrigin p y : EReal) := by
          rw [hx_eq, hy_eq]

/-- Helper for Example 9.43: mixing a positive-height point with the origin is controlled by the
positive homogeneity of the explicit perspective formula. -/
private theorem normPowerPerspectiveAtOrigin_jensen_with_origin
    (p : ℝ) (hp : 1 < p) {z : ℝ × H} (hz : 0 < z.1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (normPowerPerspectiveAtOrigin p
      (α • z + (1 - α) • (0, (0 : H))) : EReal) ≤
      (α : EReal) * (normPowerPerspectiveAtOrigin p z : EReal) +
        (1 - α : EReal) * (normPowerPerspectiveAtOrigin p (0, (0 : H)) : EReal) := by
  have hsum :
      α • z + (1 - α) • (0, (0 : H)) = (α * z.1, α • z.2) := by
    ext <;> simp [Prod.smul_mk, smul_eq_mul]
  have horigin : (normPowerPerspectiveAtOrigin p (0, (0 : H)) : EReal) = 0 := by
    rw [normPowerPerspectiveAtOrigin_apply (H := H) p hp (0, (0 : H))]
    simp
  -- The mixed Jensen inequality is actually equality after collapsing the origin term.
  calc
    (normPowerPerspectiveAtOrigin p
        (α • z + (1 - α) • (0, (0 : H))) : EReal) =
        (normPowerPerspectiveAtOrigin p (α * z.1, α • z.2) : EReal) := by
          rw [hsum]
    _ = (α : EReal) * (normPowerPerspectiveAtOrigin p z : EReal) := by
          simpa using
            normPowerPerspectiveAtOrigin_scale_pos (H := H) p hp hα0.le hz
    _ ≤ (α : EReal) * (normPowerPerspectiveAtOrigin p z : EReal) +
          (1 - α : EReal) * (normPowerPerspectiveAtOrigin p (0, (0 : H)) : EReal) := by
          rw [horigin]
          simp

/-- Helper for Example 9.43: the explicit formula is lower semicontinuous. -/
private theorem lowerSemicontinuous_normPowerPerspectiveAtOrigin
    (p : ℝ) (hp : 1 < p) :
    LowerSemicontinuous (fun z : ℝ × H ↦ (normPowerPerspectiveAtOrigin p z : EReal)) := by
  -- Split into the four geometric regions from the source proof: positive height, negative height,
  -- the origin, and the zero slice away from the origin.
  rw [lowerSemicontinuous_iff]
  intro z
  rcases z with ⟨ξ, x⟩
  by_cases hξ_pos : 0 < ξ
  · let q : ℝ × H → EReal := fun w ↦ ((‖w.2‖ ^ p / w.1 ^ (p - 1) : ℝ) : EReal)
    have hq_cont : ContinuousAt q (ξ, x) := by
      have hreal_cont :
          ContinuousAt (fun w : ℝ × H ↦ ‖w.2‖ ^ p / w.1 ^ (p - 1)) (ξ, x) := by
        have hnum : Continuous (fun w : ℝ × H ↦ ‖w.2‖ ^ p) := by
          simpa using
            (continuous_snd.norm.rpow_const fun w ↦ Or.inr (show 0 ≤ p by linarith [hp]))
        have hden : Continuous (fun w : ℝ × H ↦ w.1 ^ (p - 1)) := by
          simpa using
            (continuous_fst.rpow_const fun w ↦
              Or.inr (show 0 ≤ p - 1 by linarith [hp]))
        refine hnum.continuousAt.div hden.continuousAt ?_
        exact (Real.rpow_ne_zero hξ_pos.le (by linarith)).2 hξ_pos.ne'
      exact continuous_coe_real_ereal.continuousAt.comp hreal_cont
    rw [lowerSemicontinuousAt_iff]
    intro β hβ
    have hβq : β < q (ξ, x) := by
      simpa [q, normPowerPerspectiveAtOrigin_apply (H := H) p hp, hξ_pos] using hβ
    have hq_lsc : LowerSemicontinuousAt q (ξ, x) := hq_cont.lowerSemicontinuousAt
    rw [lowerSemicontinuousAt_iff] at hq_lsc
    have hpos_nhds : {w : ℝ × H | 0 < w.1} ∈ 𝓝 (ξ, x) := by
      exact continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hξ_pos)
    filter_upwards [hq_lsc β hβq, hpos_nhds] with w hwQ hwPos
    rw [normPowerPerspectiveAtOrigin_apply (H := H) p hp w, if_pos hwPos]
    exact hwQ
  · by_cases hξ_neg : ξ < 0
    · -- A neighborhood where the first coordinate stays negative keeps the function equal to `⊤`.
      rw [lowerSemicontinuousAt_iff]
      intro β hβ
      have hβ_top : β < (⊤ : EReal) := by
        simpa [normPowerPerspectiveAtOrigin_apply (H := H) p hp, hξ_pos, hξ_neg.ne] using hβ
      have hneg_nhds : {w : ℝ × H | w.1 < 0} ∈ 𝓝 (ξ, x) := by
        exact continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds hξ_neg)
      filter_upwards [hneg_nhds] with w hw
      have hw_not_pos : ¬ 0 < w.1 := not_lt.mpr hw.le
      have hw_ne_origin : w ≠ (0, (0 : H)) := by
        intro hw0
        exact hw.ne (by simpa [hw0])
      rw [normPowerPerspectiveAtOrigin_apply (H := H) p hp w, if_neg hw_not_pos, if_neg hw_ne_origin]
      exact hβ_top
    · have hξ_zero : ξ = 0 := by linarith
      subst hξ_zero
      by_cases hx : x = 0
      · subst hx
        -- At the origin, every strict lower bound of `0` remains below the globally nonnegative
        -- function.
        rw [lowerSemicontinuousAt_iff]
        intro β hβ
        have hβ_zero : β < (0 : EReal) := by
          simpa [normPowerPerspectiveAtOrigin_apply (H := H) p hp (0, (0 : H))] using hβ
        exact Filter.Eventually.of_forall fun w ↦
          lt_of_lt_of_le hβ_zero (normPowerPerspectiveAtOrigin_nonneg (H := H) p hp w)
      · -- The only hard case is the zero slice away from the origin, handled separately.
        simpa using
          lowerSemicontinuousAt_normPowerPerspectiveAtOrigin_zero_slice_nonzero
            (H := H) p hp hx

/-- Helper for Example 9.43: the effective domain is convex under the explicit perspective
formula. -/
private theorem normPowerPerspectiveAtOrigin_convexOn_effectiveDomain
    (p : ℝ) (hp : 1 < p) :
    ConvexOn (H := ℝ × H)
      (normPowerPerspectiveAtOrigin (H := H) p)
      (effectiveDomain (normPowerPerspectiveAtOrigin (H := H) p)) := by
  -- Unfold the local Chapter 8 `ConvexOn` structure and split the domain points into the positive
  -- slice or the origin.
  refine ⟨?_, subset_rfl, ?_⟩
  · exact ⟨(0, (0 : H)), (mem_effectiveDomain_normPowerPerspectiveAtOrigin_iff
      (H := H) p hp (0, (0 : H))).2 (Or.inr rfl)⟩
  · intro x hx y hy α hα0 hα1
    rw [mem_effectiveDomain_normPowerPerspectiveAtOrigin_iff (H := H) p hp x] at hx
    rw [mem_effectiveDomain_normPowerPerspectiveAtOrigin_iff (H := H) p hp y] at hy
    rcases hx with hx_pos | rfl
    · rcases hy with hy_pos | rfl
      · -- The positive-positive branch is the ordinary perspective Jensen inequality.
        exact jensen_normPowerPerspectiveAtOrigin_pos_pos (H := H) p hp hx_pos hy_pos hα0 hα1
      · -- Mixing with the origin reduces to positive homogeneity.
        simpa [Prod.smul_mk, smul_eq_mul] using
          normPowerPerspectiveAtOrigin_jensen_with_origin (H := H) p hp hx_pos hα0 hα1
    · rcases hy with hy_pos | rfl
      · have hβ0 : 0 < 1 - α := sub_pos.mpr hα1
        -- Re-use positive homogeneity directly when the second point is the positive one.
        have hscale :
            (normPowerPerspectiveAtOrigin p ((1 - α) * y.1, (1 - α) • y.2) : EReal) =
              (1 - α : EReal) * (normPowerPerspectiveAtOrigin p y : EReal) := by
          simpa using
            normPowerPerspectiveAtOrigin_scale_pos (H := H) p hp
              (sub_nonneg.mpr hα1.le) hy_pos
        have horigin : (normPowerPerspectiveAtOrigin p (0, (0 : H)) : EReal) = 0 := by
          rw [normPowerPerspectiveAtOrigin_apply (H := H) p hp (0, (0 : H))]
          simp
        have hsum :
            α • (0, (0 : H)) + (1 - α) • y = ((1 - α) * y.1, (1 - α) • y.2) := by
          ext <;> simp [Prod.smul_mk, smul_eq_mul]
        calc
          (normPowerPerspectiveAtOrigin p (α • (0, (0 : H)) + (1 - α) • y) : EReal)
              = (normPowerPerspectiveAtOrigin p ((1 - α) * y.1, (1 - α) • y.2) : EReal) := by
                  rw [hsum]
          _ = (1 - α : EReal) * (normPowerPerspectiveAtOrigin p y : EReal) := hscale
          _ ≤ (α : EReal) * (normPowerPerspectiveAtOrigin p (0, (0 : H)) : EReal) +
                (1 - α : EReal) * (normPowerPerspectiveAtOrigin p y : EReal) := by
                rw [horigin]
                simp
      · -- Both endpoints are the origin, so Jensen's inequality is equality.
        have horigin : (normPowerPerspectiveAtOrigin p (0, (0 : H)) : EReal) = 0 := by
          rw [normPowerPerspectiveAtOrigin_apply (H := H) p hp (0, (0 : H))]
          simp
        simpa [horigin, Prod.smul_mk, smul_eq_mul]

-- Proof sketch: package the explicit lower-semicontinuity and convexity results proved above.
/-- Example 9.43: for `p > 1`, the function `g : ℝ × H → ]-∞,+∞]` given by
`g(ξ, x) = ‖x‖^p / ξ^(p - 1)` for `ξ > 0`, `g(0, 0) = 0`, and `g(ξ, x) = +∞` otherwise belongs
to `Γ₀(ℝ × H)`. -/
theorem normPowerPerspectiveAtOrigin_mem_gammaZero
    (p : ℝ) (hp : 1 < p) :
    normPowerPerspectiveAtOrigin p ∈ Γ₀(ℝ × H) := by
  rw [mem_gammaZero_iff]
  constructor
  · -- Lower semicontinuity is read directly from the explicit branch formula.
    exact lowerSemicontinuous_normPowerPerspectiveAtOrigin (H := H) p hp
  · -- Convexity holds on the positive slice by perspective convexity, with the origin handled by
    -- positive homogeneity.
    exact normPowerPerspectiveAtOrigin_convexOn_effectiveDomain p hp

-- Proof sketch: choose a unit vector `u` in the nontrivial space and a positive sequence
-- `α_n → 0`. Along the domain points `(α_n^(p/(p - 1)), α_n • u)`, the function values stay equal
-- to `1` while the points converge to `(0, 0)`, so the real-valued restriction on the effective
-- domain cannot be continuous there.
/-- The restriction of the Example 9.43 function to its effective domain is not continuous at the
origin when the space is nontrivial. -/
theorem not_continuousWithinAt_toReal_normPowerPerspectiveAtOrigin
    [Nontrivial H] (p : ℝ) (hp : 1 < p) :
    ¬ ContinuousWithinAt
      (fun z : ℝ × H ↦ ((normPowerPerspectiveAtOrigin p z : EReal).toReal))
      (effectiveDomain (normPowerPerspectiveAtOrigin p))
      (0, (0 : H)) := by
  intro hcont
  obtain ⟨v, hv⟩ : ∃ v : H, v ≠ 0 := exists_ne (0 : H)
  let u : H := NormedSpace.normalize v
  have hu_norm : ‖u‖ = 1 := NormedSpace.norm_normalize hv
  let α : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  let z : ℕ → ℝ × H := fun n ↦ (α n ^ (p / (p - 1)), α n • u)
  have hp_sub_pos : 0 < p - 1 := by
    linarith
  have hp_ratio_nonneg : 0 ≤ p / (p - 1) := by
    positivity
  have hα_tendsto : Filter.Tendsto α Filter.atTop (nhds (0 : ℝ)) := by
    have hdenom :
        Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) Filter.atTop Filter.atTop := by
      have hnat : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop
      have hone :
          Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds (1 : ℝ)) :=
        tendsto_const_nhds
      simpa [add_comm] using hone.add_atTop hnat
    simpa [α, one_div] using tendsto_inv_atTop_zero.comp hdenom
  have hz_tendsto : Filter.Tendsto z Filter.atTop (nhds (0, (0 : H))) := by
    have hp_ratio_pos : 0 < p / (p - 1) := by
      positivity
    have hfst :
        Filter.Tendsto (fun n ↦ α n ^ (p / (p - 1))) Filter.atTop (nhds (0 : ℝ)) := by
      simpa [Real.zero_rpow hp_ratio_pos.ne'] using
        hα_tendsto.rpow_const (Or.inr hp_ratio_nonneg)
    have hsnd :
        Filter.Tendsto (fun n ↦ α n • u) Filter.atTop (nhds (0 : H)) := by
      have hsnd' :
          Filter.Tendsto (fun n : ℕ ↦ (α n : ℝ) • u) Filter.atTop (nhds ((0 : ℝ) • u)) := by
        exact hα_tendsto.smul
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ u) Filter.atTop (nhds u))
      simpa [smul_zero] using hsnd'
    have hz_tendsto' :
        Filter.Tendsto
          (fun n : ℕ ↦ (α n ^ (p / (p - 1)), α n • u))
          Filter.atTop ((nhds (0 : ℝ)) ×ˢ (nhds (0 : H))) :=
      Filter.tendsto_prod_iff'.2 ⟨hfst, hsnd⟩
    simpa [nhds_prod_eq, z] using hz_tendsto'
  have hz_dom :
      ∀ n, z n ∈ effectiveDomain (normPowerPerspectiveAtOrigin p) := by
    intro n
    rw [mem_effectiveDomain_normPowerPerspectiveAtOrigin_iff (H := H) p hp]
    left
    exact Real.rpow_pos_of_pos (by positivity) _
  have hz_within :
      Filter.Tendsto z Filter.atTop
        (nhdsWithin (0, (0 : H)) (effectiveDomain (normPowerPerspectiveAtOrigin p))) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨hz_tendsto, Filter.Eventually.of_forall hz_dom⟩
  have hcomp :
      Filter.Tendsto
        (fun n ↦ ((normPowerPerspectiveAtOrigin p (z n) : EReal).toReal))
        Filter.atTop (nhds 0) := by
    have hzero :
        ((normPowerPerspectiveAtOrigin p (0, (0 : H)) : EReal).toReal) = 0 := by
      rw [normPowerPerspectiveAtOrigin_apply (H := H) p hp (0, (0 : H))]
      simp
    simpa [z, hzero] using hcont.tendsto.comp hz_within
  have hvalue :
      ∀ n, ((normPowerPerspectiveAtOrigin p (z n) : EReal).toReal) = 1 := by
    intro n
    have hα_pos : 0 < α n := by
      positivity
    have hpow_eq :
        (α n ^ (p / (p - 1))) ^ (p - 1) = α n ^ p := by
      rw [← Real.rpow_mul (show 0 ≤ α n by positivity)]
      have hratio : (p / (p - 1)) * (p - 1) = p := by
        field_simp [hp_sub_pos.ne']
      simpa [hratio]
    have hformula :=
      normPowerPerspectiveAtOrigin_apply (H := H) p hp (z n)
    simp only [z] at hformula
    rw [if_pos (Real.rpow_pos_of_pos hα_pos _)] at hformula
    have hnorm_alpha_u : ‖α n • u‖ ^ p = α n ^ p := by
      rw [norm_smul, Real.norm_of_nonneg hα_pos.le, hu_norm]
      simpa [Real.one_rpow] using
        (Real.mul_rpow hα_pos.le (show 0 ≤ (1 : ℝ) by positivity) (p := p))
    rw [hformula, EReal.toReal_coe, hnorm_alpha_u, hpow_eq]
    field_simp [show α n ^ p ≠ 0 by positivity]
  have hconst :
      Filter.Tendsto
        (fun n ↦ ((normPowerPerspectiveAtOrigin p (z n) : EReal).toReal))
        Filter.atTop (nhds (1 : ℝ)) := by
    simpa [hvalue] using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds 1))
  have : (0 : ℝ) = 1 := tendsto_nhds_unique hcomp hconst
  norm_num at this

end NormPowerPerspectiveAtOrigin

end ERealFunction
