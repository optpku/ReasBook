/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Text_8_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Example_8_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Theorem_8_38

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open ERealFunction
open scoped Pointwise

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Helper for Example 8.43: the Minkowski gauge is nonnegative because its defining infimum runs
over positive real scalars only. -/
private theorem minkowskiGauge_nonneg (C : Set H) (x : H) :
    0 ≤ m[C] x := by
  -- Rewrite the gauge as the infimum over admissible positive witnesses.
  rw [minkowskiGauge_eq_sInf, sInf_image]
  refine le_iInf ?_
  intro ξ
  refine le_iInf ?_
  intro hξ
  exact EReal.coe_nonneg.2 hξ.1.le

/-- Helper for Example 8.43: every Minkowski gauge value lies strictly above `⊥`. -/
private theorem minkowskiGauge_mem_Ioi_bot (C : Set H) (x : H) :
    (m[C] x : EReal) ∈ Set.Ioi (⊥ : EReal) := by
  -- Nonnegativity places the gauge above `0`, hence above `⊥`.
  exact lt_of_lt_of_le (by simp) (minkowskiGauge_nonneg C x)

/-- Helper for Example 8.43: package the Minkowski gauge as an `]-∞,+∞]`-valued function. -/
noncomputable def minkowskiGaugeIoi (C : Set H) : H → Set.Ioi (⊥ : EReal) :=
  fun x ↦ ⟨m[C] x, minkowskiGauge_mem_Ioi_bot C x⟩

/-- Helper for Example 8.43: coercing the packaged gauge back to `EReal` recovers the original
gauge. -/
@[simp] private theorem minkowskiGaugeIoi_coe (C : Set H) (x : H) :
    (minkowskiGaugeIoi C x : EReal) = m[C] x := rfl

/-- Helper for Example 8.43: any positive scaled-set witness yields the corresponding upper bound
on the Minkowski gauge. -/
private theorem minkowskiGauge_le_of_mem_pos_smul (C : Set H) {x : H} {ξ : ℝ}
    (hξ : 0 < ξ) (hx : x ∈ ξ • C) :
    (m[C] x : EReal) ≤ (ξ : EReal) := by
  -- The witness scalar belongs to the set whose infimum defines `m[C] x`.
  rw [minkowskiGauge_eq_sInf]
  exact sInf_le ⟨ξ, ⟨hξ, hx⟩, rfl⟩

/-- Helper for Example 8.43: a ball around `0` contained in `C` absorbs every vector, so the
Minkowski gauge is finite everywhere. -/
private theorem minkowskiGauge_dom_eq_univ_of_ball_zero_subset (C : Set H) {ρ : ℝ}
    (hρ : 0 < ρ) (hball : Metric.ball (0 : H) ρ ⊆ C) :
    dom (m[C]) = univ := by
  ext x
  constructor
  · intro _hx
    simp
  · intro _hx
    let ε : ℝ := ρ / (‖x‖ + 1)
    have hε : 0 < ε := by
      dsimp [ε]
      positivity
    have hscaled_ball : ε • x ∈ Metric.ball (0 : H) ρ := by
      -- Choose a small enough scalar multiple of `x` to land inside the prescribed ball.
      rw [Metric.mem_ball, dist_eq_norm]
      have hnorm_lt : ‖x‖ < ‖x‖ + 1 := by
        linarith [norm_nonneg x]
      have hmul_lt : ε * ‖x‖ < ε * (‖x‖ + 1) := by
        exact mul_lt_mul_of_pos_left hnorm_lt hε
      have hcancel : ε * (‖x‖ + 1) = ρ := by
        dsimp [ε]
        field_simp
      simpa [norm_smul, Real.norm_of_nonneg hε.le, hcancel] using hmul_lt
    have hscaled_mem : ε • x ∈ C := hball hscaled_ball
    let ξ : ℝ := ε⁻¹
    have hξ : 0 < ξ := inv_pos.mpr hε
    have hxsmul : x ∈ ξ • C := by
      -- Rewrite `x` as the inverse scaling of the point already placed inside `C`.
      refine ⟨ε • x, hscaled_mem, ?_⟩
      dsimp [ξ]
      rw [smul_smul]
      simp [hε.ne']
    have hle : (m[C] x : EReal) ≤ (ξ : EReal) :=
      minkowskiGauge_le_of_mem_pos_smul C hξ hxsmul
    -- A finite real upper bound places `x` in the gauge domain.
    rw [mem_dom_iff]
    exact lt_of_le_of_lt hle (EReal.coe_lt_top ξ)

/-- Helper for Example 8.43: on a ball around `0` contained in `C`, the Minkowski gauge is bounded
above by `1`, so the image supremum on that ball is finite. -/
private theorem minkowskiGauge_finiteSupBall_of_ball_zero_subset (C : Set H) {ρ : ℝ}
    (hball : Metric.ball (0 : H) ρ ⊆ C) :
    sSup ((fun y : H ↦ (m[C] y : EReal)) '' Metric.ball (0 : H) ρ) < ⊤ := by
  -- Every point of the ball already lies in `1 • C`, so the gauge is at most `1` there.
  refine lt_of_le_of_lt ?_ (EReal.coe_lt_top (1 : ℝ))
  refine sSup_le ?_
  rintro _ ⟨y, hy, rfl⟩
  have hyC : y ∈ C := hball hy
  have hy_smul : y ∈ (1 : ℝ) • C := by
    simpa using hyC
  exact minkowskiGauge_le_of_mem_pos_smul C zero_lt_one hy_smul

/-- Helper for Example 8.43: on the finite domain of the gauge, coercing `toReal` back to `EReal`
recovers the original gauge value. -/
private theorem minkowskiGauge_coe_toReal_of_mem_dom (C : Set H) {x : H}
    (hx : x ∈ dom (m[C])) :
    (((m[C] x : EReal).toReal : ℝ) : EReal) = (m[C] x : EReal) := by
  -- Domain membership rules out `⊤`, and the gauge never attains `⊥`.
  have htop : (m[C] x : EReal) ≠ ⊤ := ne_of_lt hx
  have hbot : (m[C] x : EReal) ≠ ⊥ := ne_of_gt (minkowskiGauge_mem_Ioi_bot C x)
  exact EReal.coe_toReal htop hbot

-- Proof sketch: if `0 ∈ interior C`, then every `x : H` is absorbed by `C`, so some positive
-- multiple of `x` belongs to `C` and `m[C] x < ⊤`; hence `dom (m[C]) = univ`. Since `C` is an
-- open neighborhood of `0` and `m[C] x ≤ 1` for every `x ∈ C`, the gauge is locally bounded above
-- on an open set. Route correction: the present theorem header only assumes a normed space, so we
-- use the local-Lipschitz consequence from Theorem 8.38 rather than the stronger Hilbert-space
-- Corollary 8.39 statement.
/-- Example 8.43: if `C` is convex and contains `0` in its interior, then the Minkowski gauge is
finite everywhere and continuous on the whole space. -/
theorem minkowskiGauge_dom_eq_univ_and_continuous
    (C : Set H) (hC : Convex ℝ C) (h0C : (0 : H) ∈ interior C) :
    dom (m[C]) = univ ∧ Continuous (m[C]) := by
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0C) with ⟨ρ, hρ, hball⟩
  have hdom : dom (m[C]) = univ :=
    minkowskiGauge_dom_eq_univ_of_ball_zero_subset C hρ hball
  have hsup :
      sSup ((fun y : H ↦ (m[C] y : EReal)) '' Metric.ball (0 : H) ρ) < ⊤ :=
    minkowskiGauge_finiteSupBall_of_ball_zero_subset C hball
  let f : H → Set.Ioi (⊥ : EReal) := minkowskiGaugeIoi C
  have heff : effectiveDomain f = univ := by
    -- Full finiteness of the gauge is exactly full effective domain for the packaged function.
    ext x
    constructor
    · intro _hx
      simp
    · intro _hx
      have hx_dom : x ∈ dom (m[C]) := by
        rw [hdom]
        simp
      simpa [f, ERealFunction.effectiveDomain, ERealFunction.dom] using hx_dom
  have hconv : ERealFunction.ConvexOn f (effectiveDomain f) := by
    -- Convexity of the gauge epigraph gives Jensen's inequality on the whole finite domain.
    refine ⟨by simpa [heff], ?_, ?_⟩
    · intro x hx
      simpa [heff] using hx
    · intro x hx y hy α hα hα_lt_one
      have hx_dom : x ∈ dom (fun z : H ↦ (m[C] z : EReal)) := by
        simpa [f, ERealFunction.effectiveDomain, ERealFunction.dom] using hx
      have hy_dom : y ∈ dom (fun z : H ↦ (m[C] z : EReal)) := by
        simpa [f, ERealFunction.effectiveDomain, ERealFunction.dom] using hy
      have hJ :=
        (convex_epigraph_iff_jensen_on_dom (fun z : H ↦ (m[C] z : EReal))).1
          (convex_epigraph_minkowskiGauge C hC)
      simpa [f] using hJ hx_dom hy_dom hα hα_lt_one
  have hfinite :
      ∃ r > 0, sSup ((fun y : H ↦ (f y : EReal)) '' Metric.ball (0 : H) r) < ⊤ := by
    -- The finite-sup ball for the ambient gauge is the same ball for the packaged version.
    exact ⟨ρ, hρ, by simpa [f] using hsup⟩
  have hcontToReal : Continuous (fun x : H ↦ (f x : EReal).toReal) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hx_int : x ∈ interior (effectiveDomain f) := by
      simpa [heff]
    rcases convex_locallyLipschitzNear_on_interior_of_finiteSupBall f hconv hfinite x hx_int with
      ⟨β, r, hr, _hball_dom, hLip⟩
    -- Local Lipschitz continuity on a neighborhood ball yields continuity of the real part.
    exact hLip.continuousOn.continuousAt (Metric.ball_mem_nhds x hr)
  have hcoe :
      Continuous (fun x : H ↦ (((f x : EReal).toReal : ℝ) : EReal)) := by
    -- Compose the continuous real representative with the continuous coercion into `EReal`.
    simpa using continuous_coe_real_ereal.comp hcontToReal
  have hfun :
      (fun x : H ↦ (((f x : EReal).toReal : ℝ) : EReal)) = m[C] := by
    -- Since the gauge is finite everywhere, coercing `toReal` back to `EReal` is exact.
    funext x
    have hx_dom : x ∈ dom (m[C]) := by
      rw [hdom]
      simp
    simpa [f] using minkowskiGauge_coe_toReal_of_mem_dom C hx_dom
  refine ⟨hdom, ?_⟩
  -- Replace the coerced real representative by the original gauge.
  simpa [hfun] using hcoe

end
