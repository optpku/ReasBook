/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Example_16_19

open Filter MeasureTheory ProbabilityTheory MeasureTheory.ProbabilityMeasure
open scoped MeasureTheory NNReal

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

variable {α cMinus cPlus : ℝ}

/-- Helper for Lemma 16.25: the stable Lévy density is pointwise nonnegative for admissible
coefficients `c⁻`, `c⁺`. -/
lemma stableLevyDensity_nonneg
    (hcoeff : StableLevyCoefficients cMinus cPlus) (x : ℝ) :
    0 ≤ stableLevyDensity α cMinus cPlus x := by
  obtain ⟨hcMinus_nonneg, hcPlus_nonneg, hcoeff_pos⟩ := hcoeff
  have hcoeff' : StableLevyCoefficients cMinus cPlus := ⟨hcMinus_nonneg, hcPlus_nonneg, hcoeff_pos⟩
  by_cases hx_neg : x < 0
  · rw [stableLevyDensity, if_pos hx_neg]
    refine mul_nonneg hcMinus_nonneg ?_
    exact Real.rpow_nonneg (by linarith : 0 ≤ -x) _
  · by_cases hx_pos : 0 < x
    · rw [stableLevyDensity, if_neg hx_neg, if_pos hx_pos]
      refine mul_nonneg hcPlus_nonneg ?_
      exact Real.rpow_nonneg hx_pos.le _
    · have hx_zero : x = 0 := by linarith
      simp [stableLevyDensity, hx_zero]

/-- Helper for Lemma 16.25: on the negative half-line, the stable centering kernel is supported
on the shell `(-1, -1 / s]`. -/
lemma stableLevyCenteringKernel_eq_of_neg
    (hcoeff : StableLevyCoefficients cMinus cPlus)
    {s x : ℝ} (hs_one : 1 ≤ s) (hx_neg : x < 0) :
    (ENNReal.ofReal (stableLevyDensity α cMinus cPlus x)).toReal *
        ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0)) =
      Set.indicator (Set.Ico (1 / s) 1) (fun y : ℝ ↦ -cPlus * y ^ (-α)) x +
        Set.indicator (Set.Ioc (-1) (-(1 / s))) (fun y : ℝ ↦ cMinus * (-y) ^ (-α)) x := by
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs_one
  have hs_inv_pos : 0 < 1 / s := one_div_pos.mpr hs_pos
  have hs_inv_le_one : 1 / s ≤ 1 := by
    simpa [one_div] using inv_le_one_of_one_le₀ hs_one
  have hx_abs : |x| = -x := abs_of_neg hx_neg
  have hx_posShell : x ∉ Set.Ico (1 / s) 1 := by
    intro hx_mem
    linarith [hs_inv_pos, hx_mem.1, hx_neg]
  by_cases hx_gt_neg_one : -1 < x
  · by_cases hx_le_neg_inv : x ≤ -(1 / s)
    · have hx_negShell : x ∈ Set.Ioc (-1) (-(1 / s)) := ⟨hx_gt_neg_one, hx_le_neg_inv⟩
      have hx_negx_pos : 0 < -x := by linarith
      have hnot_small : ¬ |x| < 1 / s := by
        rw [hx_abs]
        exact not_lt.mpr (by linarith)
      have hsmall_one : |x| < 1 := by
        rw [hx_abs]
        linarith
      have hx_corr :
          ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0)) = -x := by
        rw [if_neg hnot_small, if_pos hsmall_one]
        ring
      calc
        (ENNReal.ofReal (stableLevyDensity α cMinus cPlus x)).toReal *
            ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0))
            = stableLevyDensity α cMinus cPlus x * (-x) := by
                rw [ENNReal.toReal_ofReal (stableLevyDensity_nonneg hcoeff x), hx_corr]
        _ = cMinus * (-x) ^ (-α) := by
              rw [stableLevyDensity, if_pos hx_neg]
              calc
                (cMinus * (-x) ^ (-α - 1)) * (-x)
                    = cMinus * ((-x) ^ (-α - 1) * (-x)) := by ring
                _ = cMinus * ((-x) ^ (-α - 1) * (-x) ^ (1 : ℝ)) := by rw [Real.rpow_one]
                _ = cMinus * (-x) ^ (-α) := by
                      rw [← Real.rpow_add hx_negx_pos (-α - 1) (1 : ℝ)]
                      congr 2
                      ring
        _ = Set.indicator (Set.Ico (1 / s) 1) (fun y : ℝ ↦ -cPlus * y ^ (-α)) x +
              Set.indicator (Set.Ioc (-1) (-(1 / s))) (fun y : ℝ ↦ cMinus * (-y) ^ (-α)) x := by
                rw [Set.indicator_of_notMem hx_posShell, Set.indicator_of_mem hx_negShell]
                simp
    · have hx_negShell : x ∉ Set.Ioc (-1) (-(1 / s)) := by
        intro hx_mem
        exact hx_le_neg_inv hx_mem.2
      have hsmall : |x| < 1 / s := by
        rw [hx_abs]
        linarith
      have hsmall_one : |x| < 1 := by
        rw [hx_abs]
        linarith [hs_inv_le_one]
      rw [Set.indicator_of_notMem hx_posShell, Set.indicator_of_notMem hx_negShell]
      rw [ENNReal.toReal_ofReal (stableLevyDensity_nonneg hcoeff x), stableLevyDensity,
        if_pos hx_neg]
      rw [if_pos hsmall, if_pos hsmall_one]
      ring
  · have hx_negShell : x ∉ Set.Ioc (-1) (-(1 / s)) := by
      intro hx_mem
      exact hx_gt_neg_one hx_mem.1
    have hnot_one : ¬ |x| < 1 := by
      rw [hx_abs]
      linarith
    have hnot_small : ¬ |x| < 1 / s := by
      rw [hx_abs]
      linarith [hs_inv_pos]
    rw [Set.indicator_of_notMem hx_posShell, Set.indicator_of_notMem hx_negShell]
    rw [ENNReal.toReal_ofReal (stableLevyDensity_nonneg hcoeff x), stableLevyDensity,
      if_pos hx_neg]
    rw [if_neg hnot_small, if_neg hnot_one]
    ring

/-- Helper for Lemma 16.25: on the positive half-line, the stable centering kernel is supported
on the shell `[1 / s, 1)`. -/
lemma stableLevyCenteringKernel_eq_of_pos
    (hcoeff : StableLevyCoefficients cMinus cPlus)
    {s x : ℝ} (hs_one : 1 ≤ s) (hx_pos : 0 < x) :
    (ENNReal.ofReal (stableLevyDensity α cMinus cPlus x)).toReal *
        ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0)) =
      Set.indicator (Set.Ico (1 / s) 1) (fun y : ℝ ↦ -cPlus * y ^ (-α)) x +
        Set.indicator (Set.Ioc (-1) (-(1 / s))) (fun y : ℝ ↦ cMinus * (-y) ^ (-α)) x := by
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs_one
  have hs_inv_pos : 0 < 1 / s := one_div_pos.mpr hs_pos
  have hs_inv_le_one : 1 / s ≤ 1 := by
    simpa [one_div] using inv_le_one_of_one_le₀ hs_one
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hx_abs : |x| = x := abs_of_pos hx_pos
  have hx_negShell : x ∉ Set.Ioc (-1) (-(1 / s)) := by
    intro hx_mem
    have hx_nonpos : x ≤ 0 := by
      linarith [hx_mem.2, hs_inv_pos]
    linarith
  by_cases hx_lt_inv : x < 1 / s
  · have hx_posShell : x ∉ Set.Ico (1 / s) 1 := by
      intro hx_mem
      exact not_lt_of_ge hx_mem.1 hx_lt_inv
    have hx_lt_one : x < 1 := lt_of_lt_of_le hx_lt_inv hs_inv_le_one
    rw [Set.indicator_of_notMem hx_posShell, Set.indicator_of_notMem hx_negShell]
    rw [ENNReal.toReal_ofReal (stableLevyDensity_nonneg hcoeff x), stableLevyDensity,
      if_neg (not_lt.mpr hx_nonneg), if_pos hx_pos]
    rw [if_pos (by simpa [hx_abs] using hx_lt_inv), if_pos (by simpa [hx_abs] using hx_lt_one)]
    ring
  · by_cases hx_lt_one : x < 1
    · have hx_posShell : x ∈ Set.Ico (1 / s) 1 := ⟨le_of_not_gt hx_lt_inv, hx_lt_one⟩
      have hx_corr :
          ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0)) = -x := by
        rw [if_neg (by simpa [hx_abs] using hx_lt_inv), if_pos (by simpa [hx_abs] using hx_lt_one)]
        ring
      calc
        (ENNReal.ofReal (stableLevyDensity α cMinus cPlus x)).toReal *
            ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0))
            = stableLevyDensity α cMinus cPlus x * (-x) := by
                rw [ENNReal.toReal_ofReal (stableLevyDensity_nonneg hcoeff x), hx_corr]
        _ = -cPlus * x ^ (-α) := by
              rw [stableLevyDensity, if_neg (not_lt.mpr hx_nonneg), if_pos hx_pos]
              calc
                (cPlus * x ^ (-α - 1)) * (-x)
                    = -(cPlus * (x ^ (-α - 1) * x)) := by ring
                _ = -(cPlus * (x ^ (-α - 1) * x ^ (1 : ℝ))) := by rw [Real.rpow_one]
                _ = -(cPlus * x ^ (-α)) := by
                      rw [← Real.rpow_add hx_pos (-α - 1) (1 : ℝ)]
                      congr 2
                      ring
                _ = -cPlus * x ^ (-α) := by ring
        _ = Set.indicator (Set.Ico (1 / s) 1) (fun y : ℝ ↦ -cPlus * y ^ (-α)) x +
              Set.indicator (Set.Ioc (-1) (-(1 / s))) (fun y : ℝ ↦ cMinus * (-y) ^ (-α)) x := by
                rw [Set.indicator_of_mem hx_posShell, Set.indicator_of_notMem hx_negShell]
                simp
    · have hx_posShell : x ∉ Set.Ico (1 / s) 1 := by
        intro hx_mem
        exact hx_lt_one hx_mem.2
      have hnot_one : ¬ |x| < 1 := by
        rw [hx_abs]
        exact hx_lt_one
      have hnot_small : ¬ |x| < 1 / s := by
        rw [hx_abs]
        exact hx_lt_inv
      rw [Set.indicator_of_notMem hx_posShell, Set.indicator_of_notMem hx_negShell]
      rw [ENNReal.toReal_ofReal (stableLevyDensity_nonneg hcoeff x), stableLevyDensity,
        if_neg (not_lt.mpr hx_nonneg), if_pos hx_pos]
      rw [if_neg hnot_small, if_neg hnot_one]
      ring

/-- Helper for Lemma 16.25: the stable centering kernel vanishes at the origin. -/
lemma stableLevyCenteringKernel_eq_zero
    {s : ℝ} (hs_one : 1 ≤ s) (x : ℝ) (hx_zero : x = 0) :
    (ENNReal.ofReal (stableLevyDensity α cMinus cPlus x)).toReal *
        ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0)) =
      Set.indicator (Set.Ico (1 / s) 1) (fun y : ℝ ↦ -cPlus * y ^ (-α)) x +
        Set.indicator (Set.Ioc (-1) (-(1 / s))) (fun y : ℝ ↦ cMinus * (-y) ^ (-α)) x := by
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs_one
  have hs_inv_pos : 0 < 1 / s := one_div_pos.mpr hs_pos
  subst hx_zero
  have hzero_posShell : (0 : ℝ) ∉ Set.Ico (1 / s) 1 := by
    intro hzero
    linarith [hs_inv_pos, hzero.1]
  have hzero_negShell : (0 : ℝ) ∉ Set.Ioc (-1) (-(1 / s)) := by
    intro hzero
    linarith [hs_inv_pos, hzero.2]
  rw [Set.indicator_of_notMem hzero_posShell, Set.indicator_of_notMem hzero_negShell]
  simp [stableLevyDensity]

/-- Helper for Lemma 16.25: the stable centering correction is supported on the finite shell
between radii `1 / s` and `1`. -/
lemma stableLevyCenteringCorrection_eq_intervalIntegral
    (hcoeff : StableLevyCoefficients cMinus cPlus)
    {s : ℝ} (hs_one : 1 ≤ s) :
    ∫ x : ℝ, ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0))
      ∂ stableLevyMeasure α cMinus cPlus =
      (cMinus - cPlus) * ∫ x in (1 / s)..1, x ^ (-α) := by
  obtain ⟨hcMinus_nonneg, hcPlus_nonneg, hcoeff_pos⟩ := hcoeff
  have hcoeff' : StableLevyCoefficients cMinus cPlus :=
    ⟨hcMinus_nonneg, hcPlus_nonneg, hcoeff_pos⟩
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs_one
  have hs_inv_pos : 0 < 1 / s := one_div_pos.mpr hs_pos
  have hs_inv_le_one : 1 / s ≤ 1 := by
    simpa [one_div] using inv_le_one_of_one_le₀ hs_one
  have hneg_bounds : (-1 : ℝ) ≤ -(1 / s) := by
    linarith
  let posShell : Set ℝ := Set.Ico (1 / s) 1
  let negShell : Set ℝ := Set.Ioc (-1) (-(1 / s))
  have hpos_int_on :
      IntegrableOn (fun x : ℝ ↦ -cPlus * x ^ (-α)) posShell volume := by
    have hcont_pow : ContinuousOn (fun x : ℝ ↦ x ^ (-α)) (Set.Icc (1 / s) 1) := by
      refine ContinuousOn.rpow_const continuousOn_id ?_
      intro x hx
      left
      exact ne_of_gt (lt_of_lt_of_le hs_inv_pos hx.1)
    have hcont : ContinuousOn (fun x : ℝ ↦ -cPlus * x ^ (-α)) (Set.Icc (1 / s) 1) := by
      simpa [neg_mul] using hcont_pow.const_mul (-cPlus)
    have hint :
        IntervalIntegrable (fun x : ℝ ↦ -cPlus * x ^ (-α)) volume (1 / s) 1 := by
      exact hcont.intervalIntegrable_of_Icc hs_inv_le_one
    exact (intervalIntegrable_iff_integrableOn_Ico_of_le hs_inv_le_one).1 hint
  have hneg_int_on :
      IntegrableOn (fun x : ℝ ↦ cMinus * (-x) ^ (-α)) negShell volume := by
    have hcont_neg : ContinuousOn (fun x : ℝ ↦ -x) (Set.Icc (-1) (-(1 / s))) := by
      fun_prop
    have hcont_pow : ContinuousOn (fun x : ℝ ↦ (-x) ^ (-α)) (Set.Icc (-1) (-(1 / s))) := by
      refine ContinuousOn.rpow_const hcont_neg ?_
      intro x hx
      left
      have hx_negx_pos : 0 < -x := by
        have hx_le : x ≤ -(1 / s) := hx.2
        linarith
      exact ne_of_gt hx_negx_pos
    have hcont : ContinuousOn (fun x : ℝ ↦ cMinus * (-x) ^ (-α)) (Set.Icc (-1) (-(1 / s))) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using continuousOn_const.mul hcont_pow
    have hint :
        IntervalIntegrable (fun x : ℝ ↦ cMinus * (-x) ^ (-α)) volume (-1) (-(1 / s)) := by
      exact hcont.intervalIntegrable_of_Icc hneg_bounds
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hneg_bounds).1 hint
  have hpos_int :
      Integrable (Set.indicator posShell (fun x : ℝ ↦ -cPlus * x ^ (-α))) := by
    simpa [posShell] using (integrable_indicator_iff measurableSet_Ico).2 hpos_int_on
  have hneg_int :
      Integrable (Set.indicator negShell (fun x : ℝ ↦ cMinus * (-x) ^ (-α))) := by
    simpa [negShell] using (integrable_indicator_iff measurableSet_Ioc).2 hneg_int_on
  have hkernel :
      (fun x : ℝ =>
        (ENNReal.ofReal (stableLevyDensity α cMinus cPlus x)).toReal *
          ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0))) =
        fun x : ℝ =>
          Set.indicator posShell (fun y : ℝ ↦ -cPlus * y ^ (-α)) x +
            Set.indicator negShell (fun y : ℝ ↦ cMinus * (-y) ^ (-α)) x := by
    funext x
    rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
    · simpa [posShell, negShell] using
        stableLevyCenteringKernel_eq_of_neg hcoeff' hs_one hx_neg
    · simpa [posShell, negShell] using
        stableLevyCenteringKernel_eq_zero
          (α := α) (cMinus := cMinus) (cPlus := cPlus) hs_one x hx_zero
    · simpa [posShell, negShell] using
        stableLevyCenteringKernel_eq_of_pos hcoeff' hs_one hx_pos
  -- Proof comment: rewrite the stable measure as a density, then collapse the correction to the
  -- positive and negative finite shells.
  have hkernel_smul :
      (fun x : ℝ =>
        (ENNReal.ofReal (stableLevyDensity α cMinus cPlus x)).toReal •
          ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0))) =
        fun x : ℝ =>
          Set.indicator posShell (fun y : ℝ ↦ -cPlus * y ^ (-α)) x +
            Set.indicator negShell (fun y : ℝ ↦ cMinus * (-y) ^ (-α)) x := by
    simpa [smul_eq_mul] using hkernel
  have hDensityMeas :
      Measurable (fun x ↦ ENNReal.ofReal (stableLevyDensity α cMinus cPlus x)) := by
    have hDensityReal :
        Measurable (fun x : ℝ ↦ stableLevyDensity α cMinus cPlus x) := by
      rw [show (fun x : ℝ ↦ stableLevyDensity α cMinus cPlus x) =
          (fun x : ℝ ↦
            if x < 0 then
              cMinus * (-x) ^ (-α - 1)
            else if 0 < x then
              cPlus * x ^ (-α - 1)
            else
              0) by
            funext x
            rw [stableLevyDensity]]
      refine Measurable.ite measurableSet_Iio ?_ ?_
      · fun_prop
      · refine Measurable.ite measurableSet_Ioi ?_ measurable_const
        fun_prop
    exact hDensityReal.ennreal_ofReal
  have hDensityFinite :
      ∀ᵐ x ∂volume, ENNReal.ofReal (stableLevyDensity α cMinus cPlus x) < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ by simp
  rw [stableLevyMeasure, integral_withDensity_eq_integral_toReal_smul hDensityMeas hDensityFinite]
  · rw [hkernel_smul, integral_add hpos_int hneg_int, integral_indicator measurableSet_Ico,
      integral_indicator measurableSet_Ioc]
    have hpos_set :
        ∫ x in posShell, -cPlus * x ^ (-α) =
          (-cPlus) * ∫ x in (1 / s)..1, x ^ (-α) := by
        calc
          ∫ x in posShell, -cPlus * x ^ (-α)
              = ∫ x in Set.Ioc (1 / s) 1, -cPlus * x ^ (-α) := by
                  simpa [posShell] using
                    (MeasureTheory.integral_Ico_eq_integral_Ioc
                      (μ := volume) (f := fun x : ℝ ↦ -cPlus * x ^ (-α))
                      (x := 1 / s) (y := (1 : ℝ)))
          _ = (-cPlus) * ∫ x in (1 / s : ℝ)..1, x ^ (-α) := by
                rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hs_inv_le_one]
    have hneg_ioc :
        ∫ x in Set.Ioc (-1) (-(1 / s)), cMinus * (-x) ^ (-α) =
          cMinus * ∫ x in (1 / s)..1, x ^ (-α) := by
      calc
        ∫ x in Set.Ioc (-1) (-(1 / s)), cMinus * (-x) ^ (-α)
            = ∫ x in (-1 : ℝ)..(-(1 / s)), cMinus * (-x) ^ (-α) := by
                rw [← intervalIntegral.integral_of_le hneg_bounds]
        _ = ∫ x in (1 / s : ℝ)..1, cMinus * x ^ (-α) := by
              simpa using
                (intervalIntegral.integral_comp_neg (f := fun x : ℝ ↦ cMinus * x ^ (-α))
                  (a := (-1 : ℝ)) (b := -(1 / s)))
        _ = cMinus * ∫ x in (1 / s : ℝ)..1, x ^ (-α) := by
              rw [← intervalIntegral.integral_const_mul]
    have hneg_set :
        ∫ x in negShell, cMinus * (-x) ^ (-α) =
          cMinus * ∫ x in (1 / s)..1, x ^ (-α) := by
      simpa [negShell] using hneg_ioc
    rw [hpos_set, hneg_set]
    ring

/-- Helper for Lemma 16.25: for `α ≠ 1`, the finite-shell stable centering correction has the
closed form needed in the drift comparison. -/
lemma stableLevyCenteringCorrection_eq_of_ne_one
    (hcoeff : StableLevyCoefficients cMinus cPlus)
    {s : ℝ} (hs_one : 1 ≤ s) (_hα0 : 0 < α) (hα_ne : α ≠ 1) :
    s * ∫ x : ℝ, ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0))
      ∂ stableLevyMeasure α cMinus cPlus =
      -((cPlus - cMinus) / (α - 1)) * (s ^ α - s) := by
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs_one
  have hs_inv_pos : 0 < 1 / s := one_div_pos.mpr hs_pos
  have hs_inv_le_one : 1 / s ≤ 1 := by
    simpa [one_div] using inv_le_one_of_one_le₀ hs_one
  have hzero_not_mem : (0 : ℝ) ∉ Set.uIcc (1 / s) 1 := by
    rw [Set.uIcc_of_le hs_inv_le_one]
    intro hzero
    linarith [hs_inv_pos, hzero.1]
  have hα_sub_ne : α - 1 ≠ 0 := sub_ne_zero.mpr hα_ne
  have hone_sub_ne : 1 - α ≠ 0 := by
    intro hone
    apply hα_ne
    linarith
  have hnegα_ne : (-α : ℝ) ≠ -1 := by
    intro hneg
    apply hα_ne
    linarith
  have hs_mul_inv_pow :
      s * (1 / s) ^ (1 - α) = s ^ α := by
    have hpow_inv : (s ^ (1 - α))⁻¹ = s ^ (α - 1) := by
      rw [← Real.rpow_neg hs_pos.le]
      congr 1
      ring
    calc
      s * (1 / s) ^ (1 - α) = s * (s ^ (1 - α))⁻¹ := by
        rw [one_div, Real.inv_rpow hs_pos.le]
      _ = s * s ^ (α - 1) := by rw [hpow_inv]
      _ = s ^ (1 : ℝ) * s ^ (α - 1) := by rw [Real.rpow_one]
      _ = s ^ α := by
        rw [← Real.rpow_add hs_pos (1 : ℝ) (α - 1)]
        congr 1
        ring
  have hinterval :
      ∫ x in (1 / s)..1, x ^ (-α) = (1 - (1 / s) ^ (1 - α)) / (1 - α) := by
    rw [integral_rpow (a := 1 / s) (b := 1) (r := -α)]
    · have hexp : -α + 1 = 1 - α := by ring
      rw [hexp]
      simp
    · right
      exact ⟨hnegα_ne, hzero_not_mem⟩
  -- Proof comment: evaluate the finite shell by `integral_rpow` and simplify the resulting
  -- power-law expression.
  rw [stableLevyCenteringCorrection_eq_intervalIntegral hcoeff (s := s) hs_one, hinterval]
  calc
    s * ((cMinus - cPlus) * ((1 - (1 / s) ^ (1 - α)) / (1 - α)))
        = ((cMinus - cPlus) / (1 - α)) * (s - s * (1 / s) ^ (1 - α)) := by
            field_simp [hone_sub_ne]
    _ = ((cMinus - cPlus) / (1 - α)) * (s - s ^ α) := by rw [hs_mul_inv_pow]
    _ = -((cPlus - cMinus) / (α - 1)) * (s ^ α - s) := by
          field_simp [hone_sub_ne, hα_sub_ne]
          ring

/-- Helper for Lemma 16.25: when `α = 1`, the finite-shell stable centering correction reduces to
the logarithmic term from `(16.26)`. -/
lemma stableLevyCenteringCorrection_eq_of_eq_one
    (hcoeff : StableLevyCoefficients cMinus cPlus)
    {s : ℝ} (hs_one : 1 ≤ s) :
    s * ∫ x : ℝ, ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0))
      ∂ stableLevyMeasure 1 cMinus cPlus =
      -(cPlus - cMinus) * s * Real.log s := by
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs_one
  have hs_inv_pos : 0 < 1 / s := one_div_pos.mpr hs_pos
  have hinterval :
      ∫ x in (1 / s)..1, x ^ (-(1 : ℝ)) = Real.log s := by
    have hpow :
        (fun x : ℝ ↦ x ^ (-(1 : ℝ))) = fun x : ℝ ↦ 1 / x := by
      funext x
      simpa [one_div] using (Real.rpow_neg_one x)
    calc
      ∫ x in (1 / s)..1, x ^ (-(1 : ℝ)) = ∫ x : ℝ in (1 / s)..1, 1 / x := by
        rw [hpow]
      _ = Real.log (1 / (1 / s)) := by
        rw [integral_one_div_of_pos hs_inv_pos zero_lt_one]
      _ = Real.log s := by
        have hdiv : 1 / (1 / s) = s := by
          field_simp [hs_pos.ne']
        rw [hdiv]
  -- Proof comment: the shell correction is the `x⁻¹` interval integral, hence logarithmic.
  rw [stableLevyCenteringCorrection_eq_intervalIntegral hcoeff (α := 1) (s := s) hs_one, hinterval]
  ring

end MeasureTheory.ProbabilityMeasure
