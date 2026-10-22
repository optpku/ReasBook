/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_20
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

private lemma exists_mem_ball_and_lt_of_not_continuous
    (f : H →ₗ[ℝ] ℝ) (hf : ¬ Continuous f) (ρ : ℝ) (hρ : 0 < ρ) (r : ℝ) :
    ∃ y ∈ Metric.ball (0 : H) ρ, f y < r := by
  have hno_some : ¬ ∃ x0 : H, ContinuousAt f x0 := by
    intro hsome
    rcases (linearMap_continuousAt_some_iff_exists_lipschitz_constant f).1 hsome with ⟨K, hK⟩
    exact hf hK.continuous
  let K : ℝ := 2 * (|r| + 1) / ρ
  have hK_pos : 0 < K := by
    dsimp [K]
    positivity
  have hnot_bound : ¬ ∀ x y : H, ‖f x - f y‖ ≤ K * ‖x - y‖ := by
    intro hbound
    have hsome : ∃ x0 : H, ContinuousAt f x0 :=
      (linearMap_continuousAt_some_iff_exists_nonneg_real_lipschitz_constant f).2
        ⟨K, le_of_lt hK_pos, hbound⟩
    exact hno_some hsome
  push Not at hnot_bound
  rcases hnot_bound with ⟨x, y, hxy⟩
  let z : H := x - y
  have hz : z ≠ 0 := by
    intro hz
    have : ¬ K * ‖z‖ < ‖f z‖ := by
      simp [hz]
    exact this (by simpa [z, LinearMap.map_sub] using hxy)
  have hznorm_pos : 0 < ‖z‖ := norm_pos_iff.2 hz
  let a : ℝ := ρ / (2 * ‖z‖)
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have habs : |f z| > K * ‖z‖ := by
    simpa [Real.norm_eq_abs, z, LinearMap.map_sub] using hxy
  have hscale : a * |f z| > |r| + 1 := by
    have hmul := mul_lt_mul_of_pos_left habs ha_pos
    have hEq : a * (K * ‖z‖) = |r| + 1 := by
      dsimp [a, K]
      field_simp [hznorm_pos.ne', hρ.ne']
    calc
      a * |f z| > a * (K * ‖z‖) := hmul
      _ = |r| + 1 := hEq
  have hrlt : -(|r| + 1) < r := by
    have h1 : -(|r| + 1) < -|r| := by
      linarith
    exact lt_of_lt_of_le h1 (neg_abs_le r)
  by_cases hfz : 0 ≤ f z
  · refine ⟨(-a) • z, ?_, ?_⟩
    · have hnorm : ‖(-a) • z‖ < ρ := by
        rw [norm_smul]
        simp [Real.norm_eq_abs, abs_of_pos ha_pos]
        dsimp [a]
        field_simp [hznorm_pos.ne']
        ring_nf
        linarith
      simpa [Metric.mem_ball, dist_eq_norm] using hnorm
    · have hy : f ((-a) • z) = -(a * f z) := by
        calc
          f ((-a) • z) = (-a) * f z := by simp
          _ = -(a * f z) := by ring
      have hlt : a * f z > |r| + 1 := by
        rw [abs_of_nonneg hfz] at hscale
        exact hscale
      rw [hy]
      have hneg_lt : -(a * f z) < -(|r| + 1) := by
        linarith
      exact lt_trans hneg_lt hrlt
  · refine ⟨a • z, ?_, ?_⟩
    · have hnorm : ‖a • z‖ < ρ := by
        rw [norm_smul]
        simp [Real.norm_eq_abs, abs_of_pos ha_pos]
        dsimp [a]
        field_simp [hznorm_pos.ne']
        ring_nf
        linarith
      simpa [Metric.mem_ball, dist_eq_norm] using hnorm
    · have hy : f (a • z) = a * f z := by simp
      have hfz_neg : f z < 0 := lt_of_not_ge hfz
      have hlt : a * f z < -(|r| + 1) := by
        have habs_eq : |f z| = -f z := abs_of_neg hfz_neg
        rw [habs_eq] at hscale
        linarith
      rw [hy]
      exact lt_trans hlt hrlt

-- Proof sketch: the Chapter 2 continuity criterion yields arbitrarily negative values of a
-- discontinuous linear functional inside every ball around `0`. For fixed `x`, test the defining
-- infimum of `normPowerEnvelope ((f : H → ℝ).toEReal) p γ x` at such a point in the unit ball.
-- The penalization term is then bounded above by `((‖x‖ + 1)^p) / (γ p)`, while the linear term
-- can be pushed below
-- any prescribed real threshold, so each envelope value is `⊥`.
/-- Remark 12.10: the `p`-power envelope of a discontinuous real linear functional is identically
`-∞`. -/
theorem normPowerEnvelope_eq_bot_of_not_continuous_linearFunctional
    (f : H →ₗ[ℝ] ℝ) (hf : ¬ Continuous f) (p : Set.Ici (1 : ℝ))
    (γ : Set.Ioi (0 : ℝ)) :
    normPowerEnvelope ((f : H → ℝ).toEReal) p γ = (⊥ : H → EReal) := by
  ext x
  rw [normPowerEnvelope_apply]
  refine (EReal.eq_bot_iff_forall_lt _).2 ?_
  intro r
  let B : ℝ := (‖x‖ + 1) ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ))
  rcases exists_mem_ball_and_lt_of_not_continuous f hf 1 zero_lt_one (r - B) with
    ⟨y, hyball, hylt⟩
  refine lt_of_le_of_lt (iInf_le _ y) ?_
  have hdist_le : ‖x - y‖ ≤ ‖x‖ + 1 := by
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ ‖x‖ + 1 := by
        have hy_norm : ‖y‖ < 1 := by
          simpa [Metric.mem_ball, dist_eq_norm] using hyball
        linarith
  have hp_nonneg : 0 ≤ (p : ℝ) := le_trans (by norm_num) p.2
  have hp_pos : 0 < (p : ℝ) := lt_of_lt_of_le zero_lt_one p.2
  have hden_pos : 0 < ((γ : ℝ) * (p : ℝ)) := mul_pos γ.2 hp_pos
  have hpenalty_le : ‖x - y‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) ≤ B := by
    refine div_le_div_of_nonneg_right ?_ hden_pos.le
    exact Real.rpow_le_rpow (norm_nonneg _) hdist_le hp_nonneg
  have hsum_lt : f y + ‖x - y‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) < r := by
    linarith
  change ((f y : EReal) +
      (((‖x - y‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal))) < (r : EReal)
  exact_mod_cast hsum_lt

end ERealFunction
