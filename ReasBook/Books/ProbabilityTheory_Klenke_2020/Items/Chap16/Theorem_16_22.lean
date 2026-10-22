/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.ContinuousExpLift
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Exercise_16_1_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Example_16_19
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Lemma_16_24
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Remark_16_21

open Filter MeasureTheory ProbabilityTheory MeasureTheory.ProbabilityMeasure
open scoped Topology MeasureTheory NNReal

noncomputable section

/-- The stable Levy density is the textbook power-law density on the two half-lines. -/
theorem stableLevyDensity_apply (α cMinus cPlus x : ℝ) :
    stableLevyDensity α cMinus cPlus x =
      if x < 0 then
        cMinus * (-x) ^ (-α - 1)
      else if 0 < x then
        cPlus * x ^ (-α - 1)
      else
        0 := rfl

/-- Helper for Theorem 16.22: the stable Lévy density is nonnegative when the one-sided
coefficients are nonnegative. -/
private lemma stableLevyDensity_nonneg
    {α cMinus cPlus : ℝ} (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus) (x : ℝ) :
    0 ≤ stableLevyDensity α cMinus cPlus x := by
  by_cases hx_neg : x < 0
  · -- Proof comment: on the negative half-line the density is `c⁻ (-x)^(-α-1)`.
    rw [stableLevyDensity, if_pos hx_neg]
    refine mul_nonneg hcMinus ?_
    exact Real.rpow_nonneg (by linarith : 0 ≤ -x) _
  · by_cases hx_pos : 0 < x
    · -- Proof comment: on the positive half-line the density is `c⁺ x^(-α-1)`.
      rw [stableLevyDensity, if_neg hx_neg, if_pos hx_pos]
      refine mul_nonneg hcPlus ?_
      exact Real.rpow_nonneg hx_pos.le _
    · -- Proof comment: at the origin the density is defined to be zero.
      have hx_zero : x = 0 := by linarith
      simp [stableLevyDensity, hx_zero]

/-- The stable Levy measure is Lebesgue measure with density `stableLevyDensity α c⁻ c⁺`. -/
theorem stableLevyMeasure_def (α cMinus cPlus : ℝ) :
    stableLevyMeasure α cMinus cPlus =
      volume.withDensity (fun x ↦ ENNReal.ofReal (stableLevyDensity α cMinus cPlus x)) := rfl

namespace MeasureTheory.ProbabilityMeasure

/-- Admissible one-sided coefficients for a nontrivial stable Levy measure. -/
def StableLevyCoefficients (cMinus cPlus : ℝ) : Prop :=
  0 ≤ cMinus ∧ 0 ≤ cPlus ∧ 0 < cMinus + cPlus

/-- Helper for Theorem 16.22: on the negative half-line, the stable centering kernel is supported
on the finite shell `(-1, -1 / s]`. -/
private lemma stableLevyCenteringKernel_eq_of_neg
    {α cMinus cPlus s x : ℝ} (hs_one : 1 ≤ s) (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus)
    (hx_neg : x < 0) :
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
            ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0)) =
          stableLevyDensity α cMinus cPlus x * (-x) := by
            rw [ENNReal.toReal_ofReal (stableLevyDensity_nonneg hcMinus hcPlus x), hx_corr]
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
      rw [ENNReal.toReal_ofReal (stableLevyDensity_nonneg hcMinus hcPlus x), stableLevyDensity,
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
    rw [ENNReal.toReal_ofReal (stableLevyDensity_nonneg hcMinus hcPlus x), stableLevyDensity,
      if_pos hx_neg]
    rw [if_neg hnot_small, if_neg hnot_one]
    ring

/-- Helper for Theorem 16.22: on the positive half-line, the stable centering kernel is supported
on the finite shell `[1 / s, 1)`. -/
private lemma stableLevyCenteringKernel_eq_of_pos
    {α cMinus cPlus s x : ℝ} (hs_one : 1 ≤ s) (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus)
    (hx_pos : 0 < x) :
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
    rw [ENNReal.toReal_ofReal (stableLevyDensity_nonneg hcMinus hcPlus x), stableLevyDensity,
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
            ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0)) =
          stableLevyDensity α cMinus cPlus x * (-x) := by
            rw [ENNReal.toReal_ofReal (stableLevyDensity_nonneg hcMinus hcPlus x), hx_corr]
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
      rw [ENNReal.toReal_ofReal (stableLevyDensity_nonneg hcMinus hcPlus x), stableLevyDensity,
        if_neg (not_lt.mpr hx_nonneg), if_pos hx_pos]
      rw [if_neg hnot_small, if_neg hnot_one]
      ring

/-- Helper for Theorem 16.22: the stable centering kernel vanishes at the origin. -/
private lemma stableLevyCenteringKernel_eq_zero
    {α cMinus cPlus s : ℝ} (hs_one : 1 ≤ s) (x : ℝ) (hx_zero : x = 0) :
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

/-- Helper for Theorem 16.22: the stable centering correction collapses to an interval integral
over the finite shell between radii `1 / s` and `1`. -/
private lemma stableLevyCenteringCorrection_eq_intervalIntegral
    {α cMinus cPlus s : ℝ} (hs_one : 1 ≤ s) (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus) :
    ∫ x : ℝ, ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0))
      ∂ stableLevyMeasure α cMinus cPlus =
      (cMinus - cPlus) * ∫ x in (1 / s)..1, x ^ (-α) := by
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
      (fun x : ℝ ↦
        (ENNReal.ofReal (stableLevyDensity α cMinus cPlus x)).toReal *
          ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0))) =
        fun x : ℝ ↦
          Set.indicator posShell (fun y : ℝ ↦ -cPlus * y ^ (-α)) x +
            Set.indicator negShell (fun y : ℝ ↦ cMinus * (-y) ^ (-α)) x := by
    funext x
    rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
    · simpa [posShell, negShell] using
        stableLevyCenteringKernel_eq_of_neg hs_one hcMinus hcPlus hx_neg
    · simpa [posShell, negShell] using
        stableLevyCenteringKernel_eq_zero hs_one x hx_zero
    · simpa [posShell, negShell] using
        stableLevyCenteringKernel_eq_of_pos hs_one hcMinus hcPlus hx_pos
  have hkernel_smul :
      (fun x : ℝ ↦
        (ENNReal.ofReal (stableLevyDensity α cMinus cPlus x)).toReal •
          ((if |x| < 1 / s then x else 0) - (if |x| < 1 then x else 0))) =
        fun x : ℝ ↦
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
  rw [hkernel_smul, integral_add hpos_int hneg_int, integral_indicator measurableSet_Ico,
    integral_indicator measurableSet_Ioc]
  have hpos_set :
      ∫ x in posShell, -cPlus * x ^ (-α) =
        (-cPlus) * ∫ x in (1 / s)..1, x ^ (-α) := by
    calc
      ∫ x in posShell, -cPlus * x ^ (-α)
          = ∫ x in Set.Ioc (1 / s) 1, -cPlus * x ^ (-α) := by
              simpa [posShell] using
                (MeasureTheory.integral_Ico_eq_integral_Ioc :
                  ∫ x in Set.Ico (1 / s) 1, -cPlus * x ^ (-α) =
                    ∫ x in Set.Ioc (1 / s) 1, -cPlus * x ^ (-α))
      _ = (-cPlus) * ∫ x in (1 / s : ℝ)..1, x ^ (-α) := by
            rw [← intervalIntegral.integral_const_mul]
            rw [intervalIntegral.integral_of_le hs_inv_le_one]
  have hneg_ioc :
      ∫ x in Set.Ioc (-1) (-(1 / s)), cMinus * (-x) ^ (-α) =
        cMinus * ∫ x in (1 / s)..1, x ^ (-α) := by
      calc
        ∫ x in Set.Ioc (-1) (-(1 / s)), cMinus * (-x) ^ (-α)
            = ∫ x in (-1 : ℝ)..(-(1 / s)), cMinus * (-x) ^ (-α) := by
                rw [← intervalIntegral.integral_of_le hneg_bounds]
        _ = ∫ x in (1 / s : ℝ)..1, cMinus * x ^ (-α) := by
              simpa using
                (@intervalIntegral.integral_comp_neg ℝ _ _ (-1) (-(1 / s))
                  (fun x : ℝ ↦ cMinus * x ^ (-α)))
        _ = cMinus * ∫ x in (1 / s : ℝ)..1, x ^ (-α) := by
            rw [← intervalIntegral.integral_const_mul]
  have hneg_set :
      ∫ x in negShell, cMinus * (-x) ^ (-α) =
        cMinus * ∫ x in (1 / s)..1, x ^ (-α) := by
    simpa [negShell] using hneg_ioc
  rw [hpos_set, hneg_set]
  ring

/-- Helper for Theorem 16.22: when `α = 1`, the finite-shell stable centering correction reduces
to the logarithmic term from the source formula `(16.26)`. -/
private lemma stableLevyCenteringCorrection_eq_of_eq_one
    {cMinus cPlus s : ℝ} (hs_one : 1 ≤ s) (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus) :
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
  rw [stableLevyCenteringCorrection_eq_intervalIntegral hs_one hcMinus hcPlus, hinterval]
  ring_nf

/-- Helper for Theorem 16.22: for `α ≠ 1`, the finite-shell stable centering correction has the
closed form needed to remove the broad centering term. -/
private lemma stableLevyCenteringCorrection_eq_of_ne_one_local
    {α cMinus cPlus s : ℝ} (hs_one : 1 ≤ s) (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus)
    (hα0 : 0 < α) (hα_ne : α ≠ 1) :
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
  -- Proof comment: evaluate the finite-shell integral explicitly and simplify the resulting
  -- power-law expression.
  rw [stableLevyCenteringCorrection_eq_intervalIntegral hs_one hcMinus hcPlus, hinterval]
  calc
    s * ((cMinus - cPlus) * ((1 - (1 / s) ^ (1 - α)) / (1 - α)))
        = ((cMinus - cPlus) / (1 - α)) * (s - s * (1 / s) ^ (1 - α)) := by
            field_simp [hone_sub_ne]
    _ = ((cMinus - cPlus) / (1 - α)) * (s - s ^ α) := by rw [hs_mul_inv_pow]
    _ = -((cPlus - cMinus) / (α - 1)) * (s ^ α - s) := by
          field_simp [hone_sub_ne, hα_sub_ne]
          ring

/-- Helper for Theorem 16.22: if a positive convolution power of a law is a Dirac mass, then the
original law is already a Dirac mass. -/
private lemma eq_diracProba_of_pow_eq_diracProba
    {μ : ProbabilityMeasure ℝ} {n : ℕ+} {x : ℝ}
    (hpow : μ ^ (n : ℕ) = diracProba x) :
    ∃ y : ℝ, μ = diracProba y := by
  let t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have ht_antitone : Antitone fun k ↦ |t k| := by
    intro m n hmn
    -- Proof comment: the reciprocal sequence decreases and stays nonnegative.
    simp only [t]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
      (Nat.one_div_le_one_div hmn : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1))
  have ht_zero : Tendsto (fun k ↦ |t k|) atTop (𝓝 0) := by
    -- Proof comment: the reciprocal sequence tends to `0`.
    have habs : (fun k ↦ |t k|) = fun k : ℕ ↦ 1 / ((k : ℝ) + 1) := by
      funext k
      have hk : 0 ≤ (k : ℝ) + 1 := by positivity
      dsimp [t]
      rw [abs_of_nonneg (one_div_nonneg.mpr hk)]
    rw [habs]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have ht_nonzero : ∀ k, t k ≠ 0 := by
    intro k
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    simp [t, hk]
  have hφ_unit : ∀ k, ‖charFun (μ : Measure ℝ) (t k)‖ = 1 := by
    intro k
    have hchar :
        charFun ((μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) (t k) =
          charFun (Measure.dirac x) (t k) := by
      simp [hpow, MeasureTheory.diracProba]
    have hnorm : ‖charFun (μ : Measure ℝ) (t k) ^ (n : ℕ)‖ = 1 := by
      simpa [MeasureTheory.ProbabilityMeasure.charFun_pow, MeasureTheory.charFun_dirac] using
        congrArg norm hchar
    have hpow_one : ‖charFun (μ : Measure ℝ) (t k)‖ ^ (n : ℕ) = 1 := by
      simpa [norm_pow] using hnorm
    have hnonneg : 0 ≤ ‖charFun (μ : Measure ℝ) (t k)‖ := norm_nonneg _
    exact (pow_eq_one_iff_of_nonneg hnonneg n.ne_zero).1 hpow_one
  obtain ⟨y, hy⟩ :=
    Measure.eq_dirac_of_charFun_norm_eq_one_along_zero ht_antitone ht_zero ht_nonzero hφ_unit
  -- Proof comment: upgrade the measure-level Dirac conclusion back to a probability measure.
  refine ⟨y, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  simpa [MeasureTheory.diracProba] using hy

/-- Helper for Theorem 16.22: every affine scaling witness of broad stability has positive scale. -/
private lemma scalePosOfBroadStable
    {μ : ProbabilityMeasure ℝ} (hμ : IsStableInBroadSense μ)
    {a d : ℕ+ → ℝ} (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable) :
    ∀ n : ℕ+, 0 < a n := by
  intro n
  rcases hμ with ⟨hnotDirac, _⟩
  by_contra hna
  have hzero : a n = 0 := le_antisymm (not_lt.mp hna) (ha_nonneg n)
  have hdiracPow : μ ^ (n : ℕ) = diracProba (d n) := by
    -- Proof comment: a zero slope collapses the affine pushforward to a Dirac mass.
    rw [hscale n, hzero]
    apply ProbabilityMeasure.toMeasure_injective
    ext s hs
    simp [hs]
  rcases eq_diracProba_of_pow_eq_diracProba hdiracPow with ⟨x, hx⟩
  exact hnotDirac x hx

/-- Helper for Theorem 16.22: the canonical centering cutoff is uniformly bounded by `1`. -/
private lemma norm_levyKhinchinCanonicalCentering_le_one (x : ℝ) :
    ‖levyKhinchinCanonicalCentering x‖ ≤ 1 := by
  by_cases hx : |x| < 1
  · -- Proof comment: inside the unit ball the cutoff is exactly `x`.
    simpa [levyKhinchinCanonicalCentering, hx, Real.norm_eq_abs] using le_of_lt hx
  · -- Proof comment: outside the unit ball the cutoff vanishes.
    simp [levyKhinchinCanonicalCentering, hx]

/-- Helper for Theorem 16.22: a finite measure with no atom at `0` is already canonical. -/
private lemma isCanonicalMeasure_of_isFiniteMeasure_of_measure_singleton_zero
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν0 : ν ({0} : Set ℝ) = 0) :
    IsCanonicalMeasure ν := by
  refine ⟨hν0, ?_⟩
  -- Proof comment: the canonical integrand is bounded by the integrable constant `1`.
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    have hnonneg : 0 ≤ min (x ^ (2 : ℕ)) 1 := by positivity
    have hle : min (x ^ (2 : ℕ)) 1 ≤ 1 := min_le_right _ _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle

/-- Helper for Theorem 16.22: the complex centering correction is integrable against every finite
jump intensity. -/
private lemma integrable_complexCenteringCorrection_of_isFiniteMeasure
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable
      (fun x : ℝ ↦ (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ν := by
  -- Proof comment: the cutoff correction has norm at most `‖t‖`.
  have hmeas :
      Measurable
        (fun x : ℝ ↦ (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) := by
    exact
      (Complex.measurable_ofReal.comp
        (measurable_const.mul measurable_levyKhinchinCanonicalCentering)).mul_const Complex.I
  refine (integrable_const ‖t‖).mono' hmeas.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    calc
      ‖(((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)‖
          = ‖t * levyKhinchinCanonicalCentering x‖ := by simp
      _ = ‖t‖ * ‖levyKhinchinCanonicalCentering x‖ := by simp [norm_mul]
      _ ≤ ‖t‖ * 1 := by
            exact mul_le_mul_of_nonneg_left
              (norm_levyKhinchinCanonicalCentering_le_one x) (norm_nonneg t)
      _ = ‖t‖ := by ring

/-- Helper for Theorem 16.22: the raw compound-Poisson Fourier kernel is integrable against every
finite jump intensity. -/
private lemma integrable_compoundPoissonKernel_of_isFiniteMeasure
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ν := by
  -- Proof comment: `exp (i t x)` has norm `1`, so subtracting `1` gives the uniform bound `2`.
  refine (integrable_const (2 : ℝ)).mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    calc
      ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖
          ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by
            rw [Complex.norm_exp_ofReal_mul_I]
            simp
      _ = 2 := by norm_num

/-- Helper for Theorem 16.22: integrating the complex centering correction recovers the linear
drift term. -/
private lemma integral_complexCenteringCorrection_eq
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν =
      ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) * Complex.I) := by
  -- Proof comment: move the constant factor `I` outside the integral and then reduce to the
  -- real-valued cutoff integral.
  calc
    ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν
        = (∫ x : ℝ, ((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) ∂ν) * Complex.I := by
            simpa using
              (integral_mul_const
                (μ := ν)
                (f := fun x : ℝ ↦ ((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ))
                (r := Complex.I))
    _ = ((((∫ x : ℝ, t * levyKhinchinCanonicalCentering x ∂ν : ℝ)) : ℂ)) * Complex.I := by
          rw [integral_complex_ofReal]
    _ = ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) * Complex.I) := by
          rw [integral_const_mul]

/-- Helper for Theorem 16.22: the complex `sin` correction is integrable against every finite
measure. -/
private lemma integrable_complexSinCorrection_of_isFiniteMeasure_local
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun x : ℝ ↦ (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ν := by
  -- Proof comment: `sin` is uniformly bounded by `1`, so the complex `sin` correction is bounded
  -- by the constant `‖t‖`.
  refine (integrable_const ‖t‖).mono'
    (((Complex.measurable_ofReal.comp
      (measurable_const.mul Real.measurable_sin)).mul_const Complex.I).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    calc
      ‖(((t * Real.sin x : ℝ) : ℂ) * Complex.I)‖
          = ‖((t * Real.sin x : ℝ) : ℂ)‖ * ‖Complex.I‖ := by
              rw [norm_mul]
      _ = ‖t * Real.sin x‖ := by rw [Complex.norm_real, Complex.norm_I, mul_one]
      _ = |t * Real.sin x| := by rw [Real.norm_eq_abs]
      _ = |t| * |Real.sin x| := by rw [abs_mul]
      _ = ‖t‖ * ‖Real.sin x‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖t‖ * 1 := by
            gcongr
            simpa [Real.norm_eq_abs] using Real.abs_sin_le_one x
      _ = ‖t‖ := by ring

/-- Helper for Theorem 16.22: integrating the complex `sin` correction recovers the linear drift
term with the sine integral factored out. -/
private lemma integral_complexSinCorrection_eq_local
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    ∫ x : ℝ, (((t * Real.sin x : ℝ) : ℂ) * Complex.I) ∂ν =
      ((((t * ∫ x : ℝ, Real.sin x ∂ν : ℝ) : ℂ)) * Complex.I) := by
  -- Proof comment: move the factor `I` through the integral and then rewrite the remaining
  -- complex integral as the complexification of the real-valued sine integral.
  calc
    ∫ x : ℝ, (((t * Real.sin x : ℝ) : ℂ) * Complex.I) ∂ν
        = (∫ x : ℝ, ((t * Real.sin x : ℝ) : ℂ) ∂ν) * Complex.I := by
            simpa using
              (integral_mul_const
                (μ := ν)
                (f := fun x : ℝ ↦ ((t * Real.sin x : ℝ) : ℂ))
                (r := Complex.I))
    _ = ((((∫ x : ℝ, t * Real.sin x ∂ν : ℝ)) : ℂ)) * Complex.I := by
          rw [integral_complex_ofReal]
    _ = ((((t * ∫ x : ℝ, Real.sin x ∂ν : ℝ) : ℂ)) * Complex.I) := by
          rw [integral_const_mul]

/-- Helper for Theorem 16.22: a finite jump intensity with no atom at `0` already gives the
canonical Lévy--Khintchin representation of its compound-Poisson law. -/
private lemma compoundPoisson_hasLevyKhinchinRepresentation
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν0 : ν ({0} : Set ℝ) = 0) :
    HasLevyKhinchinRepresentation
      (compoundPoissonMeasure ν)
      { sigma2 := 0
        b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν
        ν := ν } := by
  constructor
  · -- Proof comment: finite jump intensities with no atom at `0` are canonical with zero
    -- Gaussian coefficient.
    refine ⟨by simp, isCanonicalMeasure_of_isFiniteMeasure_of_measure_singleton_zero ν hν0⟩
  · intro t
    have hkernel :
        Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ν :=
      integrable_compoundPoissonKernel_of_isFiniteMeasure ν t
    have hcorr :
        Integrable
          (fun x : ℝ ↦ (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ν :=
      integrable_complexCenteringCorrection_of_isFiniteMeasure ν t
    have hsplit :
        ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂ν =
          ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
            ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν := by
      -- Proof comment: split the centered kernel into the raw Poisson kernel minus the cutoff
      -- correction.
      rw [integral_sub hkernel hcorr]
    have hexponent :
        levyKhinchinExponent
            { sigma2 := 0
              b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν
              ν := ν } t =
          ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν := by
      -- Proof comment: the explicit drift term cancels the centering correction.
      calc
        levyKhinchinExponent
            { sigma2 := 0
              b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν
              ν := ν } t
            =
              ((((∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) * t : ℝ) : ℂ) *
                  Complex.I) +
                ∫ x : ℝ,
                  (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
                    (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂ν := by
                  simp [levyKhinchinExponent, levyKhinchinExponentWithCentering, mul_comm]
        _ =
              ((((∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) * t : ℝ) : ℂ) *
                  Complex.I) +
                (∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
                  ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν) := by
                    rw [hsplit]
        _ =
              ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) * Complex.I) +
                (∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
                  ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) *
                    Complex.I)) := by
                      rw [integral_complexCenteringCorrection_eq]
                      congr 1
                      ring
        _ = ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν := by
              ring
    -- Proof comment: the remaining exponent is exactly the compound-Poisson characteristic
    -- exponent.
    rw [charFun_compoundPoissonMeasure]
    simpa [hexponent]

/-- Helper for Theorem 16.22: pushing a punctured finite measure forward along `Subtype.val`
preserves the fact that there is no atom at `0`. -/
private lemma map_puncturedFiniteMeasure_apply_singleton_zero
    (ν : FiniteMeasure {x : ℝ // x ≠ 0}) :
    (((ν.map Subtype.val : FiniteMeasure ℝ) : Measure ℝ) ({0} : Set ℝ)) = 0 := by
  change (Measure.map Subtype.val (ν : Measure {x : ℝ // x ≠ 0})) ({0} : Set ℝ) = 0
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton 0)]
  have hpreimage :
      (Subtype.val : {x : ℝ // x ≠ 0} → ℝ) ⁻¹' ({0} : Set ℝ) =
        (∅ : Set {x : ℝ // x ≠ 0}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false]
    constructor
    · intro hx
      exact x.2 hx
    · intro hFalse
      exact False.elim hFalse
  simp [hpreimage]

/-- Helper for Theorem 16.22: on `ℝ`, the inner product is ordinary multiplication. -/
private lemma realInner_eq_mul (x y : ℝ) : inner ℝ x y = x * y := by
  have h := real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y
  simp [Real.norm_eq_abs] at h
  nlinarith

/-- Helper for Theorem 16.22: vanishing Gaussian and Lévy terms force the represented law to be
the Dirac mass at the drift coefficient. -/
private lemma eq_diracProba_of_zeroGaussian_zeroLevy
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (hσ : τ.sigma2 = 0) (hν : τ.ν = 0) :
    μ = diracProba τ.b := by
  apply ProbabilityMeasure.toMeasure_injective
  refine Measure.ext_of_charFun ?_
  ext t
  -- Proof comment: with no Gaussian or jump term, the Lévy--Khintchin exponent is exactly the
  -- characteristic exponent of the point mass at `τ.b`.
  simpa [MeasureTheory.diracProba, MeasureTheory.charFun_dirac, realInner_eq_mul,
    levyKhinchinExponent, levyKhinchinExponentWithCentering, hσ, hν] using hτ.charFun_eq_exp t

/-- Helper for Theorem 16.22: affine pushforwards commute with convolution powers, with the
translation term accumulating linearly. -/
private lemma map_affine_pow_eq_map_pow_affine
    (μ : ProbabilityMeasure ℝ) (a c : ℝ) (n : ℕ+) :
    (map μ (measurable_affineMap a c).aemeasurable) ^ (n : ℕ) =
      map (μ ^ (n : ℕ)) (measurable_affineMap a ((n : ℝ) * c)).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  refine Measure.ext_of_charFun ?_
  ext t
  have hmap :
      charFun ((map μ (measurable_affineMap a c).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ)
          t =
        charFun (μ : Measure ℝ) (a * t) *
          Complex.exp ((((c * t : ℝ) : ℂ) * Complex.I)) := by
    -- Proof comment: decompose the affine map into scaling followed by translation.
    rw [ProbabilityMeasure.toMeasure_map]
    have hcomp :
        Measure.map (fun x : ℝ ↦ a * x + c) (μ : Measure ℝ) =
          Measure.map (fun x : ℝ ↦ x + c) (Measure.map (fun x : ℝ ↦ a * x) (μ : Measure ℝ)) := by
      rw [show (fun x : ℝ ↦ a * x + c) = (fun x : ℝ ↦ x + c) ∘ fun x : ℝ ↦ a * x from rfl,
        ← Measure.map_map]
      all_goals fun_prop
    rw [hcomp, MeasureTheory.charFun_map_add_const, MeasureTheory.charFun_map_mul]
    simp [realInner_eq_mul, mul_comm]
  have htarget :
      charFun
          ((map (μ ^ (n : ℕ)) (measurable_affineMap a ((n : ℝ) * c)).aemeasurable :
              ProbabilityMeasure ℝ) : Measure ℝ) t =
        charFun (μ : Measure ℝ) (a * t) ^ (n : ℕ) *
          Complex.exp ((((((n : ℝ) * c) * t : ℝ) : ℂ) * Complex.I)) := by
    -- Proof comment: rewrite the target affine image in the same characteristic-function
    -- coordinates.
    rw [ProbabilityMeasure.toMeasure_map]
    rw [show (fun x : ℝ ↦ a * x + (n : ℝ) * c) =
        (fun x : ℝ ↦ x + (n : ℝ) * c) ∘ fun x : ℝ ↦ a * x from rfl, ← Measure.map_map]
    · rw [MeasureTheory.charFun_map_add_const, MeasureTheory.charFun_map_mul,
        ProbabilityMeasure.charFun_pow]
      simp [realInner_eq_mul, mul_left_comm, mul_comm]
    all_goals fun_prop
  -- Proof comment: both measures have the same characteristic function after one affine
  -- normalization.
  calc
    charFun (((map μ (measurable_affineMap a c).aemeasurable) ^ (n : ℕ) :
        ProbabilityMeasure ℝ) : Measure ℝ) t
        = charFun
            ((map μ (measurable_affineMap a c).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ)
            t ^ (n : ℕ) := by
              simpa using
                congrArg (fun f : ℝ → ℂ ↦ f t)
                  (ProbabilityMeasure.charFun_pow
                    (map μ (measurable_affineMap a c).aemeasurable) (n : ℕ))
    _ = (charFun (μ : Measure ℝ) (a * t) *
          Complex.exp ((((c * t : ℝ) : ℂ) * Complex.I))) ^ (n : ℕ) := by
            rw [hmap]
    _ = charFun (μ : Measure ℝ) (a * t) ^ (n : ℕ) *
          Complex.exp (((((n : ℝ) * (c * t) : ℝ) : ℂ) * Complex.I)) := by
            rw [mul_pow, (Complex.exp_nat_mul ((((c * t : ℝ) : ℂ) * Complex.I)) (n : ℕ)).symm]
            congr 1
            norm_num
            ring
    _ = charFun (μ : Measure ℝ) (a * t) ^ (n : ℕ) *
          Complex.exp ((((((n : ℝ) * c) * t : ℝ) : ℂ) * Complex.I)) := by
            congr 2
            ring
    _ = charFun
          ((map (μ ^ (n : ℕ)) (measurable_affineMap a ((n : ℝ) * c)).aemeasurable :
              ProbabilityMeasure ℝ) : Measure ℝ) t := by
            rw [htarget]

/-- Helper for Theorem 16.22: composing two affine pushforwards yields the pushforward under the
composed affine map. -/
private lemma map_map_affine_eq_map_affine_local
    (μ : ProbabilityMeasure ℝ) (a₁ d₁ a₂ d₂ : ℝ) :
    map (map μ (measurable_affineMap a₁ d₁).aemeasurable)
        (measurable_affineMap a₂ d₂).aemeasurable =
      map μ (measurable_affineMap (a₂ * a₁) (a₂ * d₁ + d₂)).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map]
  · congr 1
    funext x
    simp [Function.comp]
    ring
  all_goals
    fun_prop

/-- Helper for Theorem 16.22: the identity affine map leaves a probability measure unchanged. -/
private lemma map_affine_one_zero_eq_self_local (μ : ProbabilityMeasure ℝ) :
    map μ (measurable_affineMap 1 0).aemeasurable = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  have hId : (fun x : ℝ ↦ 1 * x + 0) = id := by
    funext x
    simp
  rw [hId]
  simpa using (Measure.map_id (μ := (μ : Measure ℝ)))

/-- Helper for Theorem 16.22: affine maps send Dirac masses to the corresponding affine images. -/
private lemma map_diracProba_affine_local (a d x : ℝ) :
    map (diracProba x) (measurable_affineMap a d).aemeasurable =
      diracProba (a * x + d) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  ext s hs
  simp [MeasureTheory.diracProba, hs]

/-- Helper for Theorem 16.22: translating a non-Dirac law by `-b` keeps it non-Dirac. -/
private lemma shiftedLaw_not_dirac_local
    {μ : ProbabilityMeasure ℝ} (hμ : ∀ x : ℝ, μ ≠ diracProba x) (b : ℝ) :
    ∀ x : ℝ, map μ (measurable_affineMap 1 (-b)).aemeasurable ≠ diracProba x := by
  intro x hshift
  have hback :
      μ = diracProba (x + b) := by
    calc
      μ = map (map μ (measurable_affineMap 1 (-b)).aemeasurable)
            (measurable_affineMap 1 b).aemeasurable := by
              symm
              rw [map_map_affine_eq_map_affine_local μ 1 (-b) 1 b]
              simpa using map_affine_one_zero_eq_self_local μ
      _ = map (diracProba x) (measurable_affineMap 1 b).aemeasurable := by rw [hshift]
      _ = diracProba (x + b) := by
            simpa using map_diracProba_affine_local 1 b x
  exact hμ (x + b) hback

/-- Helper for Theorem 16.22: the canonical scale `n^(1 / α)` satisfies
`(n^(1 / α))^α = n` for `α > 0`. -/
private lemma stableScalePow_eq_natCast_local {α : ℝ} (hα0 : 0 < α) (n : ℕ+) :
    (((n : ℝ) ^ (1 / α)) ^ α) = (n : ℝ) := by
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  calc
    (((n : ℝ) ^ (1 / α)) ^ α) = (n : ℝ) ^ ((1 / α) * α) := by
      rw [Real.rpow_mul hn_nonneg]
    _ = (n : ℝ) ^ (1 : ℝ) := by
          congr 1
          field_simp [hα0.ne']
    _ = (n : ℝ) := by rw [Real.rpow_one]

/-- Helper for Theorem 16.22: inverting one affine scaling relation produces an explicit
convolution root of the original law. -/
private lemma affineRootPow_eq_self_of_affinePow
    {μ : ProbabilityMeasure ℝ} {n : ℕ+} {a d : ℝ} (ha : 0 < a)
    (hpow : μ ^ (n : ℕ) = map μ (measurable_affineMap a d).aemeasurable) :
    let ν : ProbabilityMeasure ℝ :=
      map μ (measurable_affineMap a⁻¹ (-(a⁻¹ * d) / (n : ℝ))).aemeasurable
    ν ^ (n : ℕ) = μ := by
  let ν : ProbabilityMeasure ℝ :=
    map μ (measurable_affineMap a⁻¹ (-(a⁻¹ * d) / (n : ℝ))).aemeasurable
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast n.ne_zero
  -- Proof comment: transport the convolution power through the inverse affine normalization.
  calc
    ν ^ (n : ℕ)
        = map (μ ^ (n : ℕ))
            (measurable_affineMap a⁻¹ ((n : ℝ) * (-(a⁻¹ * d) / (n : ℝ)))).aemeasurable := by
              simpa [ν] using
                map_affine_pow_eq_map_pow_affine μ a⁻¹ (-(a⁻¹ * d) / (n : ℝ)) n
    _ = map (map μ (measurable_affineMap a d).aemeasurable)
          (measurable_affineMap a⁻¹ ((n : ℝ) * (-(a⁻¹ * d) / (n : ℝ)))).aemeasurable := by
            rw [hpow]
    _ = μ := by
          apply ProbabilityMeasure.toMeasure_injective
          -- Proof comment: the inverse normalization composes with the original affine map to the
          -- identity, so the nested pushforward is trivial.
          rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
          rw [Measure.map_map
            (measurable_affineMap a⁻¹ ((n : ℝ) * (-(a⁻¹ * d) / (n : ℝ))))
            (measurable_affineMap a d)]
          have hcomp :
              ((fun x : ℝ ↦ a⁻¹ * x + (n : ℝ) * (-(a⁻¹ * d) / (n : ℝ))) ∘
                fun x : ℝ ↦ a * x + d) = fun x : ℝ ↦ x := by
            funext x
            simp [Function.comp, div_eq_mul_inv]
            field_simp [ha_ne, hn_ne]
            ring
          rw [hcomp]
          exact (Measure.map_id : Measure.map id (μ : Measure ℝ) = (μ : Measure ℝ))

/-- Helper for Theorem 16.22: broad stability already implies infinite divisibility by undoing
each affine scaling witness. -/
private lemma isInfinitelyDivisible_of_broadStableScaling
    {μ : ProbabilityMeasure ℝ}
    (hμ : IsStableInBroadSense μ)
    {a d : ℕ+ → ℝ} (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable) :
    IsInfinitelyDivisible μ := by
  have ha_pos : ∀ n : ℕ+, 0 < a n := scalePosOfBroadStable hμ ha_nonneg hscale
  refine ⟨?_⟩
  intro n
  let ν : ProbabilityMeasure ℝ :=
    map μ (measurable_affineMap (a n)⁻¹ (-( (a n)⁻¹ * d n) / (n : ℝ))).aemeasurable
  refine ⟨ν, ?_⟩
  -- Proof comment: the inverse affine normalization gives the required `n`th convolution root.
  simpa [ν] using
    affineRootPow_eq_self_of_affinePow (ha_pos n) (hscale n)

/-- Helper for Theorem 16.22: broad stability yields a punctured compound-Poisson approximation
via the earlier infinite-divisibility approximation theorem. -/
private lemma compoundPoissonApproximation_of_broadStable
    {μ : ProbabilityMeasure ℝ} (hμ : IsStableInBroadSense μ) :
    ∃ νs : ℕ → FiniteMeasure {x : ℝ // x ≠ 0},
      Tendsto (fun n ↦ compoundPoissonMeasure ((νs n).map Subtype.val)) atTop (𝓝 μ) := by
  rcases hμ.exists_scale_shift with ⟨a, d, ha_nonneg, hscale⟩
  have hInf : IsInfinitelyDivisible μ :=
    isInfinitelyDivisible_of_broadStableScaling hμ ha_nonneg hscale
  -- Proof comment: once broad stability is converted into infinite divisibility, the earlier
  -- compound-Poisson approximation owner applies directly.
  exact exists_compoundPoissonApproximation_of_isInfinitelyDivisible hInf

/-- Helper for Theorem 16.22: positive convolution powers of an infinitely divisible law remain
infinitely divisible. -/
private lemma isInfinitelyDivisible_pow
    {μ : ProbabilityMeasure ℝ} (hμ : IsInfinitelyDivisible μ) (n : ℕ+) :
    IsInfinitelyDivisible (μ ^ (n : ℕ)) := by
  refine ⟨?_⟩
  intro m
  rcases hμ.exists_root m with ⟨ν, hν⟩
  refine ⟨ν ^ (n : ℕ), ?_⟩
  -- Proof comment: reuse the same `m`th root of `μ`, then take its fixed `n`th convolution power.
  calc
    (ν ^ (n : ℕ)) ^ (m : ℕ) = ν ^ ((n : ℕ) * (m : ℕ)) := by
      rw [pow_mul]
    _ = ν ^ ((m : ℕ) * (n : ℕ)) := by
      rw [Nat.mul_comm]
    _ = (ν ^ (m : ℕ)) ^ (n : ℕ) := by
      rw [pow_mul]
    _ = μ ^ (n : ℕ) := by
      rw [hν]

/-- Helper for Theorem 16.22: an infinitely divisible law admits a normalized continuous lift of
its characteristic function through `Complex.exp`. -/
private lemma continuousExpLift_of_isInfinitelyDivisible_local
    {μ : ProbabilityMeasure ℝ} (hμ : IsInfinitelyDivisible μ) :
    ∃ Ψ : C(ℝ, ℂ), Ψ 0 = 0 ∧ ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t := by
  -- Proof comment: infinite divisibility gives a zero-free characteristic function, so the
  -- covering-space lift from `ContinuousExpLift` applies directly.
  obtain ⟨Ψ, hΨ, _huniq⟩ :=
    existsUniqueContinuousExpLift
      (MeasureTheory.continuous_charFun : Continuous (charFun (μ : Measure ℝ)))
      (charFun_ne_zero_of_isInfinitelyDivisible hμ)
      (by simpa using (MeasureTheory.charFun_zero (μ := (μ : Measure ℝ))))
  exact ⟨Ψ, hΨ.1, hΨ.2⟩

/-- Helper for Theorem 16.22: package exact positive-integer convolution roots of an infinitely
divisible law into a single `ℕ+`-indexed family. -/
private theorem existsExactRootFamily_of_isInfinitelyDivisible_local
    {μ : ProbabilityMeasure ℝ} (hμ : IsInfinitelyDivisible μ) :
    ∃ μroot : ℕ+ → ProbabilityMeasure ℝ, ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ := by
  -- Proof comment: choose one exact `n`th root for each positive integer and package the choices
  -- into a single family indexed by `ℕ+`.
  refine ⟨fun n ↦ Classical.choose (hμ.exists_root n), ?_⟩
  intro n
  exact Classical.choose_spec (hμ.exists_root n)

/-- Helper for Theorem 16.22: an exact positive-integer root family yields the expected
compound-Poisson approximation. -/
private theorem exactRootCompoundPoissonApproximation_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ) :
    Tendsto
      (fun n : ℕ ↦
        compoundPoissonMeasure
          (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
            FiniteMeasure ℝ)))
      atTop
      (𝓝 μ) := by
  let φs : ℕ → ℝ → ℂ := fun n t ↦ charFun (μroot (Nat.toPNat' n) : Measure ℝ) t
  have hφs : ∀ n : ℕ, IsCFP (φs n) := by
    intro n
    -- Proof comment: each exact root already appears as a characteristic function.
    refine ⟨μroot (Nat.toPNat' n), ?_⟩
    funext t
    rfl
  have hpow :
      ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (φs n t) ^ n) atTop (𝓝 (charFun (μ : Measure ℝ) t)) := by
    intro t
    have hrootChar :
        ∀ n : ℕ+, (charFun (μroot n : Measure ℝ) t) ^ (n : ℕ) = charFun (μ : Measure ℝ) t := by
      intro n
      calc
        (charFun (μroot n : Measure ℝ) t) ^ (n : ℕ)
            = charFun ((μroot n ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) t := by
                simpa using
                  (congrArg (fun f : ℝ → ℂ ↦ f t)
                    (ProbabilityMeasure.charFun_pow (μroot n) (n : ℕ))).symm
        _ = charFun (μ : Measure ℝ) t := by
              simpa using
                congrArg (fun ν : ProbabilityMeasure ℝ ↦ charFun (ν : Measure ℝ) t) (hroot n)
    have hpowP :
        Tendsto
          (fun n : ℕ+ ↦ (charFun (μroot n : Measure ℝ) t) ^ (n : ℕ))
          atTop
          (𝓝 (charFun (μ : Measure ℝ) t)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      exact Filter.Eventually.of_forall fun n ↦ by
        simpa using (hrootChar n).symm
    have hshiftPNat :
        Tendsto
          (fun n : ℕ ↦ (charFun (μroot (Nat.succPNat n) : Measure ℝ) t) ^
            ((Nat.succPNat n : ℕ+) : ℕ))
          atTop
          (𝓝 (charFun (μ : Measure ℝ) t)) := by
      -- Proof comment: reindex the positive integers by `Nat.succPNat`.
      simpa [OrderIso.pnatIsoNat_symm_apply] using
        hpowP.comp OrderIso.pnatIsoNat.symm.tendsto_atTop
    have hshiftNat :
        Tendsto (fun n : ℕ ↦ (φs (n + 1) t) ^ (n + 1)) atTop
          (𝓝 (charFun (μ : Measure ℝ) t)) := by
      -- Proof comment: after shifting by one, `Nat.toPNat'` agrees with `Nat.succPNat`.
      simpa [φs, PNat.toPNat'_coe (Nat.succ_pos _), Nat.succPNat_coe] using hshiftPNat
    -- Proof comment: a finite shift does not change the `atTop` limit.
    exact (Filter.tendsto_add_atTop_iff_nat 1).1 hshiftNat
  have hchar0 : ContinuousAt (charFun (μ : Measure ℝ)) 0 := by
    simpa using
      (MeasureTheory.continuous_charFun : Continuous (charFun (μ : Measure ℝ))).continuousAt
  rcases
      (cfp_power_limit_iff_linearized_limit hφs).1
        ⟨charFun (μ : Measure ℝ), hpow, hchar0⟩ with
    ⟨ψ, hlin, _hψ0⟩
  have hcharEq :
      charFun (μ : Measure ℝ) = fun t : ℝ ↦ Complex.exp (ψ t) :=
    cfp_power_limit_eq_cexp_linearized_limit hφs hpow hchar0 hlin
  let μs : ℕ → ProbabilityMeasure ℝ := fun n ↦
    compoundPoissonMeasure
      (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
        FiniteMeasure ℝ))
  have hμsChar :
      ∀ t : ℝ,
        Tendsto (fun n : ℕ ↦ charFun (μs n : Measure ℝ) t) atTop
          (𝓝 (charFun (μ : Measure ℝ) t)) := by
    intro t
    have htarget : charFun (μ : Measure ℝ) t = Complex.exp (ψ t) := by
      simpa using congrArg (fun f : ℝ → ℂ ↦ f t) hcharEq
    have hlinShift :
        Tendsto
          (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ) * (φs (n + 1) t - 1))
          atTop
          (𝓝 (ψ t)) :=
      (Filter.tendsto_add_atTop_iff_nat 1).2 (hlin t)
    have hExpCont : ContinuousAt Complex.exp (ψ t) := by
      simpa using Complex.continuous_exp.continuousAt
    rw [htarget]
    refine Tendsto.congr' ?_ (hExpCont.tendsto.comp hlinShift)
    exact Filter.Eventually.of_forall fun n ↦ by
      -- Proof comment: the compound-Poisson characteristic function is exactly the centered
      -- exponential attached to the `(n + 1)`st root.
      simpa [μs, φs, PNat.toPNat'_coe (Nat.succ_pos _), Nat.succPNat_coe] using
        (charFun_compoundPoissonMeasure_natSmulProbability
          (μroot (Nat.succPNat n)) (n + 1) t).symm
  -- Proof comment: characteristic functions determine weak convergence of probability laws.
  exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 hμsChar

/-- Helper for Theorem 16.22: rewrite a Lévy--Khintchin representation along an equality of
probability laws. -/
private lemma hasLevyKhinchinRepresentation_congr
    {μ ν : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hμν : μ = ν) (hτ : HasLevyKhinchinRepresentation μ τ) :
    HasLevyKhinchinRepresentation ν τ := by
  simpa [hμν] using hτ

-- Route correction: this helper block is live theorem-local API, not a disabled comment block.

/-- Helper for Theorem 16.22: an exact positive-integer root family already witnesses infinite
divisibility. -/
private lemma isInfinitelyDivisible_of_exactRootFamily_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ) :
    IsInfinitelyDivisible μ := by
  -- Proof comment: the chosen `n`th convolution root from the family is exactly the witness
  -- required by the definition of infinite divisibility.
  refine ⟨?_⟩
  intro n
  exact ⟨μroot n, hroot n⟩

/-- Helper for Theorem 16.22: a Lévy--Khintchin representation never vanishes under the complex
exponential, so the represented characteristic function is zero-free. -/
private lemma charFun_ne_zero_of_hasLevyKhinchinRepresentation
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    ∀ t : ℝ, charFun (μ : Measure ℝ) t ≠ 0 := by
  intro t
  rw [hτ.charFun_eq_exp t]
  exact Complex.exp_ne_zero _

/-- Helper for Theorem 16.22: every Lévy--Khintchin exponent is normalized by vanishing at the
origin. -/
private lemma levyKhinchinExponent_zero (τ : LevyKhinchinTriple) :
    levyKhinchinExponent τ 0 = 0 := by
  -- Proof comment: the quadratic, linear, and jump terms all vanish at frequency `0`.
  simp [levyKhinchinExponent, levyKhinchinExponentWithCentering]

/-- Helper for Theorem 16.22: the local canonical jump kernel used to prove continuity of the
Lévy--Khintchin exponent. -/
private def levyKhinchinCanonicalKernelLocal (t : ℝ) : ℝ → ℂ :=
  fun x ↦
    Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
      (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)

/-- Helper for Theorem 16.22: the smooth sine-centered jump kernel used in the compact-average
reconstruction. -/
private def levyKhinchinSineKernelLocal (t : ℝ) : ℝ → ℂ :=
  fun x ↦
    Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
      (((t * Real.sin x : ℝ) : ℂ) * Complex.I)

/-- Helper for Theorem 16.22: the local canonical jump kernel is measurable. -/
private lemma measurable_levyKhinchinCanonicalKernelLocal (t : ℝ) :
    Measurable (levyKhinchinCanonicalKernelLocal t) := by
  -- Proof comment: measurability follows from the measurable exponential term and the measurable
  -- canonical centering correction.
  have hExp :
      Measurable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hCenter :
      Measurable
        (fun x : ℝ ↦ (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) := by
    exact
      (Complex.measurable_ofReal.comp
        (measurable_const.mul measurable_levyKhinchinCanonicalCentering)).mul_const Complex.I
  exact (hExp.sub measurable_const).sub hCenter

/-- Helper for Theorem 16.22: the local canonical jump kernel is pointwise continuous in the
frequency variable. -/
private lemma continuous_levyKhinchinCanonicalKernelLocal (x : ℝ) :
    Continuous (fun t : ℝ ↦ levyKhinchinCanonicalKernelLocal t x) := by
  -- Proof comment: for fixed `x`, the kernel is an explicit combination of continuous scalar and
  -- exponential functions of `t`.
  continuity

/-- Helper for Theorem 16.22: inside the unit ball the canonical truncated second moment is just
`x²`. -/
private lemma sqMinOne_eq_sq_of_abs_lt_one_local {x : ℝ} (hx : |x| < 1) :
    min (x ^ (2 : ℕ)) 1 = x ^ (2 : ℕ) := by
  -- Proof comment: inside the unit ball the truncation `min (x^2) 1` does not cut anything off.
  refine min_eq_left ?_
  exact le_of_lt ((sq_lt_one_iff_abs_lt_one x).2 hx)

/-- Helper for Theorem 16.22: outside the unit ball the canonical truncated second moment is `1`.
-/
private lemma sqMinOne_eq_one_of_one_le_abs_local {x : ℝ} (hx : 1 ≤ |x|) :
    min (x ^ (2 : ℕ)) 1 = 1 := by
  -- Proof comment: once `|x| ≥ 1`, the truncation saturates at `1`.
  refine min_eq_right ?_
  have hxSq : 1 ≤ |x| * |x| := by
    nlinarith
  simpa [pow_two, sq_abs] using hxSq

/-- Helper for Theorem 16.22: the quadratic term `|t * x|²` factors as `|t|² x²`. -/
private lemma abs_mul_sq_local (t x : ℝ) :
    |t * x| ^ (2 : ℕ) = |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := by
  -- Proof comment: take absolute values first, then expand the square of the product.
  rw [abs_mul, mul_pow, sq_abs, sq_abs]

/-- Helper for Theorem 16.22: when `|t * x| > 1`, the crude bound `2 + |t * x|` is still
controlled by `3 |t * x|²`. -/
private lemma two_add_abs_mul_le_three_abs_mul_sq_local {t x : ℝ} (hlarge : 1 < |t * x|) :
    2 + |t * x| ≤ 3 * |t * x| ^ (2 : ℕ) := by
  -- Proof comment: if `|t * x| > 1`, then both `2` and `|t * x|` are bounded by multiples of
  -- `|t * x|²`.
  nlinarith [le_of_lt hlarge, sq_nonneg (|t * x|)]

/-- Helper for Theorem 16.22: the oscillatory term `exp (i t x) - 1` is uniformly bounded by
`2`. -/
private lemma norm_exp_sub_one_mul_I_le_two_local (t x : ℝ) :
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤ 2 := by
  -- Proof comment: `exp (i y)` lies on the unit circle, so subtracting `1` has norm at most `2`.
  calc
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 1 + 1 := by
          rw [Complex.norm_exp_ofReal_mul_I]
          simp
    _ = 2 := by norm_num

/-- Helper for Theorem 16.22: the oscillatory remainder is bounded by `2 + |t * x|`. -/
private lemma norm_exp_sub_one_sub_id_mul_I_le_two_add_abs_mul_local (t x : ℝ) :
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
        (((t * x : ℝ) : ℂ) * Complex.I)‖ ≤
      2 + |t * x| := by
  -- Proof comment: use the triangle inequality and the basic bounds for `exp (i y) - 1` and
  -- `‖y I‖`.
  calc
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
        (((t * x : ℝ) : ℂ) * Complex.I)‖
        ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ +
            ‖(((t * x : ℝ) : ℂ) * Complex.I)‖ := norm_sub_le _ _
    _ ≤ 2 + |t * x| := by
      gcongr
      · exact norm_exp_sub_one_mul_I_le_two_local t x
      · simp [Complex.norm_I, Real.norm_eq_abs]

/-- Helper for Theorem 16.22: the local canonical jump kernel satisfies the standard quadratic
domination bound from the Chapter 16 owner API. -/
private lemma norm_levyKhinchinCanonicalKernelLocal_le (t x : ℝ) :
    ‖levyKhinchinCanonicalKernelLocal t x‖ ≤
      max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
  by_cases hx : |x| < 1
  · by_cases htx : |t * x| ≤ 1
    · -- Proof comment: on the small-jump branch, the quadratic Taylor remainder bound controls
      -- the oscillatory kernel by `|t x|²`.
      let z : ℂ := (((t * x : ℝ) : ℂ) * Complex.I)
      have hquad :
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - (((t * x : ℝ) : ℂ) * Complex.I)‖ ≤
            |t * x| ^ (2 : ℕ) := by
        have hz : ‖z‖ ≤ 1 := by
          simpa [z, Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs] using htx
        simpa [z, Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs] using
          (Complex.norm_exp_sub_one_sub_id_le hz)
      calc
        ‖levyKhinchinCanonicalKernelLocal t x‖
            = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
                (((t * x : ℝ) : ℂ) * Complex.I)‖ := by
                  simp [levyKhinchinCanonicalKernelLocal, levyKhinchinCanonicalCentering, hx]
        _ ≤ |t * x| ^ (2 : ℕ) := hquad
        _ = |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := abs_mul_sq_local t x
        _ ≤ 3 * |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := by
              nlinarith [sq_nonneg (|t|), sq_nonneg x]
        _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 * x ^ (2 : ℕ) := by
              gcongr
              exact le_max_left _ _
        _ = max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
              rw [sqMinOne_eq_sq_of_abs_lt_one_local hx]
    · -- Proof comment: once `|t x| > 1`, the coarse linear bound still yields quadratic control
      -- on the unit-ball branch.
      have hlarge : 1 < |t * x| := lt_of_not_ge htx
      calc
        ‖levyKhinchinCanonicalKernelLocal t x‖
            = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
                (((t * x : ℝ) : ℂ) * Complex.I)‖ := by
                  simp [levyKhinchinCanonicalKernelLocal, levyKhinchinCanonicalCentering, hx]
        _ ≤ 2 + |t * x| := norm_exp_sub_one_sub_id_mul_I_le_two_add_abs_mul_local t x
        _ ≤ 3 * |t * x| ^ (2 : ℕ) := two_add_abs_mul_le_three_abs_mul_sq_local hlarge
        _ = 3 * (|t| ^ (2 : ℕ) * x ^ (2 : ℕ)) := by rw [abs_mul_sq_local]
        _ = 3 * |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := by ring
        _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 * x ^ (2 : ℕ) := by
              gcongr
              exact le_max_left _ _
        _ = max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
              rw [sqMinOne_eq_sq_of_abs_lt_one_local hx]
  · -- Proof comment: outside the unit ball, the linear correction vanishes and the uniform bound
    -- `2` is enough because `min (x², 1) = 1`.
    have hxLarge : 1 ≤ |x| := le_of_not_gt hx
    calc
      ‖levyKhinchinCanonicalKernelLocal t x‖
          = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ := by
              simp [levyKhinchinCanonicalKernelLocal, levyKhinchinCanonicalCentering, hx]
      _ ≤ 2 := norm_exp_sub_one_mul_I_le_two_local t x
      _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 := le_max_right _ _
      _ = max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
            rw [sqMinOne_eq_one_of_one_le_abs_local hxLarge, mul_one]

/-- Helper for Theorem 16.22: the local canonical jump kernel is integrable against every
canonical Lévy measure. -/
private lemma integrable_levyKhinchinCanonicalKernelLocal {ν : Measure ℝ}
    (hν : IsCanonicalMeasure ν) (t : ℝ) :
    Integrable (levyKhinchinCanonicalKernelLocal t) ν := by
  have hbound :
      Integrable (fun x : ℝ ↦ max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1) ν := by
    -- Proof comment: the dominating function is a constant multiple of the canonical integrand.
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hν.integrable_sq_min_one.const_mul (max (3 * |t| ^ (2 : ℕ)) 2)
  refine Integrable.mono' hbound
      (measurable_levyKhinchinCanonicalKernelLocal t).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x ↦
    norm_levyKhinchinCanonicalKernelLocal_le t x

/-- Helper for Theorem 16.22: canonical Lévy--Khintchin exponents are continuous. -/
private lemma continuousLevyKhinchinExponentLocal
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) :
    Continuous (levyKhinchinExponent τ) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t₀
  let M : ℝ := max (3 * (|t₀| + 1) ^ (2 : ℕ)) 2
  have hτMeasure : IsCanonicalMeasure τ.ν := hτ.isCanonicalMeasure
  have hboundInt :
      Integrable (fun x : ℝ ↦ M * min (x ^ (2 : ℕ)) 1) τ.ν := by
    -- Proof comment: on a unit neighborhood of `t₀`, one fixed quadratic bound controls all
    -- nearby jump kernels.
    simpa [M, mul_comm, mul_left_comm, mul_assoc] using
      hτMeasure.integrable_sq_min_one.const_mul M
  have hkernel :
      ContinuousAt (fun t : ℝ ↦ ∫ x : ℝ, levyKhinchinCanonicalKernelLocal t x ∂τ.ν) t₀ := by
    have hmeas :
        ∀ᶠ t : ℝ in 𝓝 t₀,
          AEStronglyMeasurable (levyKhinchinCanonicalKernelLocal t) τ.ν := by
      exact Filter.Eventually.of_forall fun t ↦
        (measurable_levyKhinchinCanonicalKernelLocal t).aestronglyMeasurable
    have hbound :
        ∀ᶠ t : ℝ in 𝓝 t₀, ∀ᵐ x ∂τ.ν,
          ‖levyKhinchinCanonicalKernelLocal t x‖ ≤ M * min (x ^ (2 : ℕ)) 1 := by
      filter_upwards [Metric.ball_mem_nhds t₀ zero_lt_one] with t ht
      have ht_dist : |t - t₀| < 1 := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using ht
      have ht_abs : |t| ≤ |t₀| + 1 := by
        have htriangle : abs (|t| - |t₀|) ≤ |t - t₀| := abs_abs_sub_abs_le_abs_sub _ _
        rcases abs_le.mp htriangle with ⟨hneg, hpos⟩
        linarith
      have hM :
          max (3 * |t| ^ (2 : ℕ)) 2 ≤ M := by
        dsimp [M]
        have hsq : |t| ^ (2 : ℕ) ≤ (|t₀| + 1) ^ (2 : ℕ) := by
          nlinarith [ht_abs, abs_nonneg t, show 0 ≤ |t₀| + 1 by positivity]
        exact max_le_max (by gcongr) le_rfl
      filter_upwards with x
      exact (norm_levyKhinchinCanonicalKernelLocal_le t x).trans <|
        mul_le_mul_of_nonneg_right hM (by positivity)
    have hlim :
        ∀ᵐ x ∂τ.ν,
          Tendsto (fun t : ℝ ↦ levyKhinchinCanonicalKernelLocal t x) (𝓝 t₀)
            (𝓝 (levyKhinchinCanonicalKernelLocal t₀ x)) := by
      filter_upwards with x
      exact (continuous_levyKhinchinCanonicalKernelLocal x).continuousAt.tendsto
    have htendsto :
        Tendsto (fun t : ℝ ↦ ∫ x : ℝ, levyKhinchinCanonicalKernelLocal t x ∂τ.ν)
          (𝓝 t₀) (𝓝 (∫ x : ℝ, levyKhinchinCanonicalKernelLocal t₀ x ∂τ.ν)) := by
      exact
        tendsto_integral_filter_of_dominated_convergence
          (fun x ↦ M * min (x ^ (2 : ℕ)) 1) hmeas hbound hboundInt hlim
    simpa [ContinuousAt] using htendsto
  have hpoly :
      ContinuousAt
        (fun t : ℝ ↦
          (((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
            (((τ.b * t : ℝ) : ℂ) * Complex.I)) t₀ := by
    -- Proof comment: the Gaussian and drift contributions are explicit polynomial functions of
    -- the frequency variable.
    have hQuad :
        Continuous
          (fun t : ℝ ↦ (((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ))) := by
      continuity
    have hDrift :
        Continuous
          (fun t : ℝ ↦ (((τ.b * t : ℝ) : ℂ) * Complex.I)) := by
      continuity
    exact hQuad.continuousAt.add hDrift.continuousAt
  -- Proof comment: continuity of the full exponent is the sum of the explicit polynomial part and
  -- the dominated-convergence continuity of the jump integral.
  have hsum :
      ContinuousAt
        (fun t : ℝ ↦
          (((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
            (((τ.b * t : ℝ) : ℂ) * Complex.I) +
            ∫ x : ℝ, levyKhinchinCanonicalKernelLocal t x ∂τ.ν) t₀ := by
    exact hpoly.add hkernel
  change ContinuousAt
      (fun t : ℝ ↦ levyKhinchinExponentWithCentering
        τ.sigma2 τ.b τ.ν levyKhinchinCanonicalCentering t) t₀
  convert hsum using 1

/-- Helper for Theorem 16.22: once continuity is supplied, two Lévy--Khintchin representations of
the same law have the same exponent. -/
private lemma levyKhinchinExponent_eq_of_sameRepresentation_of_continuous
    {μ : ProbabilityMeasure ℝ} {τ₁ τ₂ : LevyKhinchinTriple}
    (hτ₁ : HasLevyKhinchinRepresentation μ τ₁)
    (hτ₂ : HasLevyKhinchinRepresentation μ τ₂)
    (hcont₁ : Continuous (levyKhinchinExponent τ₁))
    (hcont₂ : Continuous (levyKhinchinExponent τ₂)) :
    ∀ t : ℝ, levyKhinchinExponent τ₁ t = levyKhinchinExponent τ₂ t := by
  -- Route correction: the unavailable Theorem 16.17 import blocked the old uniqueness route, so
  -- this local bridge records the exact continuous-lift argument directly in the current file.
  let Ψ₁ : C(ℝ, ℂ) := ⟨levyKhinchinExponent τ₁, hcont₁⟩
  let Ψ₂ : C(ℝ, ℂ) := ⟨levyKhinchinExponent τ₂, hcont₂⟩
  obtain ⟨Ψ, hΨ, huniq⟩ :=
    existsUniqueContinuousExpLift
      (MeasureTheory.continuous_charFun : Continuous (charFun (μ : Measure ℝ)))
      (charFun_ne_zero_of_hasLevyKhinchinRepresentation hτ₁)
      (by simpa using (MeasureTheory.charFun_zero (μ : Measure ℝ)))
  have hΨ₁ :
      Ψ₁ 0 = 0 ∧ ∀ t : ℝ, Complex.exp (Ψ₁ t) = charFun (μ : Measure ℝ) t := by
    constructor
    · -- Proof comment: the first exponent uses the standard normalization at `0`.
      simpa [Ψ₁] using levyKhinchinExponent_zero τ₁
    · intro t
      -- Proof comment: the first representation identifies `charFun μ` with `exp ∘ Ψ₁`.
      simpa [Ψ₁] using (hτ₁.charFun_eq_exp t).symm
  have hΨ₂ :
      Ψ₂ 0 = 0 ∧ ∀ t : ℝ, Complex.exp (Ψ₂ t) = charFun (μ : Measure ℝ) t := by
    constructor
    · -- Proof comment: the second exponent has the same normalization.
      simpa [Ψ₂] using levyKhinchinExponent_zero τ₂
    · intro t
      -- Proof comment: the second representation gives the same characteristic function lift.
      simpa [Ψ₂] using (hτ₂.charFun_eq_exp t).symm
  have hEq₁ : Ψ₁ = Ψ := huniq Ψ₁ hΨ₁
  have hEq₂ : Ψ₂ = Ψ := huniq Ψ₂ hΨ₂
  intro t
  -- Proof comment: evaluate the common continuous lift at the requested frequency.
  exact congrArg (fun f : C(ℝ, ℂ) ↦ f t) (hEq₁.trans hEq₂.symm)

-- The block below was a theorem-local reimplementation of the Lévy--Khintchin
-- existence/uniqueness machinery. It currently does not elaborate in this workspace
-- and is replaced just below by the shorter public Chapter 16 API route.
/-- Helper for Theorem 16.22: the Gaussian recovery kernel isolates the Gaussian coefficient in a
Lévy--Khintchin representation. -/
private def gaussianRecoveryKernel (x : ℝ) : ℝ :=
  1 - Real.exp (-(x ^ (2 : ℕ) / 2))

/-- Helper for Theorem 16.22: the Gaussian recovery kernel is measurable. -/
private lemma measurable_gaussianRecoveryKernel :
    Measurable gaussianRecoveryKernel := by
  -- Proof comment: the Gaussian recovery kernel is built from measurable polynomial and
  -- exponential pieces.
  have hArg : Measurable (fun x : ℝ ↦ -(x ^ (2 : ℕ) / 2 : ℝ)) := by
    fun_prop
  simpa [gaussianRecoveryKernel] using
    measurable_const.sub (Real.measurable_exp.comp hArg)

/-- Helper for Theorem 16.22: the Gaussian recovery kernel vanishes at the origin. -/
private lemma gaussianRecoveryKernel_zero :
    gaussianRecoveryKernel 0 = 0 := by
  -- Proof comment: at the origin, the Gaussian damping factor is `exp 0 = 1`.
  simp [gaussianRecoveryKernel]

/-- Helper for Theorem 16.22: the Gaussian recovery kernel is nonnegative. -/
private lemma gaussianRecoveryKernel_nonneg (x : ℝ) :
    0 ≤ gaussianRecoveryKernel x := by
  -- Proof comment: the exponential term lies in `(0, 1]`, so subtracting it from `1` is
  -- nonnegative.
  refine sub_nonneg.mpr ?_
  refine Real.exp_le_one_iff.mpr ?_
  have hsq_nonneg : 0 ≤ x ^ (2 : ℕ) / 2 := by positivity
  linarith

/-- Helper for Theorem 16.22: the Gaussian recovery kernel is bounded above by `1`. -/
private lemma gaussianRecoveryKernel_le_one (x : ℝ) :
    gaussianRecoveryKernel x ≤ 1 := by
  -- Proof comment: the exponential term is nonnegative, so removing it cannot exceed `1`.
  dsimp [gaussianRecoveryKernel]
  have hExp : 0 ≤ Real.exp (-(x ^ (2 : ℕ) / 2)) := (Real.exp_pos _).le
  linarith

/-- Helper for Theorem 16.22: the Gaussian recovery kernel is controlled by `x²`. -/
private lemma gaussianRecoveryKernel_le_sq (x : ℝ) :
    gaussianRecoveryKernel x ≤ x ^ (2 : ℕ) := by
  -- Proof comment: the elementary inequality `1 - y ≤ exp (-y)` gives the quadratic bound.
  have hStep : gaussianRecoveryKernel x ≤ x ^ (2 : ℕ) / 2 := by
    have hExp : 1 - (x ^ (2 : ℕ) / 2) ≤ Real.exp (-(x ^ (2 : ℕ) / 2)) := by
      simpa using Real.one_sub_le_exp_neg (x ^ (2 : ℕ) / 2)
    dsimp [gaussianRecoveryKernel]
    linarith
  have hHalf_le : x ^ (2 : ℕ) / 2 ≤ x ^ (2 : ℕ) := by
    nlinarith [sq_nonneg x]
  exact le_trans hStep hHalf_le

/-- Helper for Theorem 16.22: the Gaussian recovery kernel is dominated by the canonical
integrand `x ↦ min (x², 1)`. -/
private lemma gaussianRecoveryKernel_le_sqMinOne (x : ℝ) :
    gaussianRecoveryKernel x ≤ min (x ^ (2 : ℕ)) 1 := by
  -- Proof comment: the kernel is simultaneously bounded by `x²` and by `1`.
  exact le_min (gaussianRecoveryKernel_le_sq x) (gaussianRecoveryKernel_le_one x)

/-- Helper for Theorem 16.22: the Gaussian recovery kernel is strictly positive away from `0`. -/
private lemma gaussianRecoveryKernel_ne_zero {x : ℝ} (hx : x ≠ 0) :
    gaussianRecoveryKernel x ≠ 0 := by
  -- Proof comment: `exp y = 1` forces `y = 0`, so the kernel only vanishes at the origin.
  intro hKernel
  have hExp : Real.exp (-(x ^ (2 : ℕ) / 2)) = 1 := by
    dsimp [gaussianRecoveryKernel] at hKernel
    linarith
  have hArg : -(x ^ (2 : ℕ) / 2) = 0 := (Real.exp_eq_one_iff _).mp hExp
  have hSq : x ^ (2 : ℕ) = 0 := by
    nlinarith
  exact hx (eq_zero_of_pow_eq_zero hSq)

/-- Helper for Theorem 16.22: every canonical Lévy measure integrates the Gaussian recovery
kernel. -/
private lemma integrable_gaussianRecoveryKernel {ν : Measure ℝ}
    (hν : IsCanonicalMeasure ν) :
    Integrable gaussianRecoveryKernel ν := by
  -- Proof comment: the Gaussian recovery kernel is dominated by the canonical integrand
  -- `min (x², 1)`.
  refine hν.integrable_sq_min_one.mono' measurable_gaussianRecoveryKernel.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    have hnonneg : 0 ≤ gaussianRecoveryKernel x := gaussianRecoveryKernel_nonneg x
    rw [Real.norm_of_nonneg hnonneg]
    exact gaussianRecoveryKernel_le_sqMinOne x

/-- Helper for Theorem 16.22: the Gaussian-smoothed auxiliary measure is finite. -/
private theorem gaussianRecoveryAuxFiniteMeasure_isFinite
    (α : NNReal) (ν : Measure ℝ)
    (h_int : Integrable gaussianRecoveryKernel ν) :
    IsFiniteMeasure
      ((α : ENNReal) • Measure.dirac 0 +
        ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) := by
  -- Proof comment: both the Dirac atom and the Gaussian-damped Lévy part are finite.
  have hDirac :
      IsFiniteMeasure (((α : ENNReal) • Measure.dirac (0 : ℝ) : Measure ℝ)) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, Measure.dirac_apply_of_mem (by simp)]
    have hα : (α : ENNReal) < ⊤ := ENNReal.coe_lt_top
    simpa [smul_eq_mul] using hα
  have hTilt :
      IsFiniteMeasure
        (ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) := by
    simpa using
      (MeasureTheory.isFiniteMeasure_withDensity_ofReal (μ := ν) h_int.hasFiniteIntegral)
  letI : IsFiniteMeasure (((α : ENNReal) • Measure.dirac (0 : ℝ) : Measure ℝ)) := hDirac
  letI :
      IsFiniteMeasure
        (ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) := hTilt
  simpa using
    (inferInstance :
      IsFiniteMeasure
        ((((α : ENNReal) • Measure.dirac (0 : ℝ) : Measure ℝ) +
          ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x)))))

/-- Helper for Theorem 16.22: the Gaussian-smoothed auxiliary finite measure
`α δ₀ + (1 - exp (-(x² / 2))) ν(dx)`. -/
private noncomputable def gaussianRecoveryAuxFiniteMeasure
    (α : NNReal) (ν : Measure ℝ) (h_int : Integrable gaussianRecoveryKernel ν) :
    FiniteMeasure ℝ :=
  ⟨(α : ENNReal) • Measure.dirac 0 +
      ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x)),
    gaussianRecoveryAuxFiniteMeasure_isFinite α ν h_int⟩

/-- Helper for Theorem 16.22: the Gaussian-damped Lévy part contributes no atom at `0`. -/
private lemma gaussianRecoveryAuxFiniteMeasure_apply_zero
    (α : NNReal) {ν : Measure ℝ}
    (h_int : Integrable gaussianRecoveryKernel ν) :
    (((gaussianRecoveryAuxFiniteMeasure α ν h_int : FiniteMeasure ℝ) : Measure ℝ) {0}) = α := by
  -- Proof comment: the Gaussian recovery kernel vanishes at `0`, so only the Dirac atom remains.
  have hTiltZero :
      (ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) {0} = 0 := by
    rw [withDensity_apply _ (measurableSet_singleton 0)]
    simp [gaussianRecoveryKernel_zero]
  change ((((α : ENNReal) • Measure.dirac (0 : ℝ) : Measure ℝ) +
      ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) {0}) = α
  rw [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (by simp), hTiltZero,
    add_zero]
  simpa [smul_eq_mul] using (mul_one (α : ENNReal))

/-- Helper for Theorem 16.22: the Gaussian recovery kernel is almost everywhere nonzero under a
measure with no atom at `0`. -/
private lemma gaussianRecoveryKernel_ae_ne_zero
    {ν : Measure ℝ} (hν0 : ν ({0} : Set ℝ) = 0) :
    ∀ᵐ x ∂ν, gaussianRecoveryKernel x ≠ 0 := by
  -- Proof comment: the Gaussian recovery kernel only vanishes at the origin.
  have hzero : ∀ᵐ x ∂ν, x ≠ 0 := by
    simpa [ae_iff, hν0]
  filter_upwards [hzero] with x hx
  exact gaussianRecoveryKernel_ne_zero hx

/-- Helper for Theorem 16.22: the ENNReal Gaussian recovery density is finite everywhere. -/
private lemma gaussianRecoveryKernel_ae_ne_top {ν : Measure ℝ} :
    ∀ᵐ x ∂ν, (ENNReal.ofReal (gaussianRecoveryKernel x)) ≠ ⊤ := by
  -- Proof comment: `ENNReal.ofReal` is finite on every real input.
  filter_upwards with x
  simp

/-- Helper for Theorem 16.22: on the punctured restriction `η.restrict ({0}ᶜ)`, the Gaussian
recovery kernel never vanishes. -/
private lemma gaussianRecoveryKernel_ae_ne_zero_restrict_compl_singleton
    (η : Measure ℝ) :
    ∀ᵐ x ∂η.restrict ({0}ᶜ : Set ℝ), gaussianRecoveryKernel x ≠ 0 := by
  rw [ae_restrict_iff' ((measurableSet_singleton (0 : ℝ)).compl)]
  filter_upwards with x hx
  -- Proof comment: removing the origin removes the only zero of the Gaussian recovery kernel.
  exact gaussianRecoveryKernel_ne_zero (by simpa using hx)

/-- Helper for Theorem 16.22: the pure oscillatory Fourier kernel is integrable against every
finite measure. -/
private lemma integrable_fourierKernel_of_isFiniteMeasure
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) ν := by
  -- Proof comment: the oscillatory factor has norm `1`, so finiteness of the measure gives
  -- integrability immediately.
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    simpa [mul_assoc] using (le_of_eq (Complex.norm_exp_ofReal_mul_I (t * x)))

/-- Helper for Theorem 16.22: inverting the Gaussian recovery density on the punctured restriction
recovers the original punctured measure. -/
private lemma withDensity_gaussianRecoveryKernel_inv_same_restrict_compl_singleton
    (η : Measure ℝ) :
    (((η.restrict ({0}ᶜ : Set ℝ)).withDensity
        (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).withDensity
      (fun x ↦ (ENNReal.ofReal (gaussianRecoveryKernel x))⁻¹)) =
      η.restrict ({0}ᶜ : Set ℝ) := by
  let f : ℝ → ENNReal := fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x)
  have hf_meas : Measurable f := measurable_gaussianRecoveryKernel.ennreal_ofReal
  have hf_ne_zero :
      ∀ᵐ x ∂η.restrict ({0}ᶜ : Set ℝ), f x ≠ 0 :=
    by
      filter_upwards [gaussianRecoveryKernel_ae_ne_zero_restrict_compl_singleton η] with x hx
      have hpos : 0 < gaussianRecoveryKernel x :=
        lt_of_le_of_ne (gaussianRecoveryKernel_nonneg x) (by simpa [eq_comm] using hx)
      simpa [f, ENNReal.ofReal_eq_zero, not_le_of_gt hpos]
  have hf_ne_top :
      ∀ᵐ x ∂η.restrict ({0}ᶜ : Set ℝ), f x ≠ (⊤ : ENNReal) :=
    by
      simpa [f] using
        gaussianRecoveryKernel_ae_ne_top (ν := η.restrict ({0}ᶜ : Set ℝ))
  -- Proof comment: the Gaussian auxiliary measure is built by weighting the punctured jump measure
  -- with this density, so a second `withDensity` by its inverse removes the tilt.
  simpa [f] using MeasureTheory.withDensity_inv_same hf_meas hf_ne_zero hf_ne_top

/-- Helper for Theorem 16.22: the Gaussian-smoothed auxiliary finite measure has characteristic
function `α + ∫ e^{itx} gaussianRecoveryKernel(x) ν(dx)`. -/
private lemma gaussianRecoveryKernel_smul_fourier_eq (t x : ℝ) :
    (ENNReal.toReal (ENNReal.ofReal (gaussianRecoveryKernel x))) •
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x := by
  -- Proof comment: `withDensity` contributes the real scalar
  -- `ENNReal.toReal (ofReal (gaussianRecoveryKernel x))`, which is exactly
  -- `gaussianRecoveryKernel x` because the kernel is nonnegative.
  have htoReal :
      ENNReal.toReal (ENNReal.ofReal (gaussianRecoveryKernel x)) = gaussianRecoveryKernel x := by
    simp [gaussianRecoveryKernel_nonneg x]
  simpa [Algebra.smul_def, htoReal, mul_comm]

/-- Helper for Theorem 16.22: the Gaussian-smoothed auxiliary finite measure has characteristic
function `α + ∫ e^{itx} gaussianRecoveryKernel(x) ν(dx)`. -/
private lemma gaussianRecoveryWeightedFourierIntegral_eq_local
    {ν : Measure ℝ} (t : ℝ) :
    ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
        ∂ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x)) =
      ∫ x : ℝ,
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x ∂ν := by
  -- Proof comment: rewrite the weighted auxiliary measure integral back to the original measure
  -- by exposing the `toReal` density factor explicitly.
  rw [integral_withDensity_eq_integral_toReal_smul measurable_gaussianRecoveryKernel.ennreal_ofReal
    (by
      filter_upwards [gaussianRecoveryKernel_ae_ne_top (ν := ν)] with x hx
      exact lt_of_le_of_ne le_top hx)]
  refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
  simpa using gaussianRecoveryKernel_smul_fourier_eq t x

/-- Helper for Theorem 16.22: the Gaussian-smoothed auxiliary finite measure has characteristic
function `α + ∫ e^{itx} gaussianRecoveryKernel(x) ν(dx)`. -/
private lemma gaussianRecoveryAuxFiniteMeasure_charFun
    (α : NNReal) {ν : Measure ℝ}
    (h_int : Integrable gaussianRecoveryKernel ν) (t : ℝ) :
    charFun (((gaussianRecoveryAuxFiniteMeasure α ν h_int : FiniteMeasure ℝ) : Measure ℝ)) t =
      (α : ℂ) +
        ∫ x : ℝ,
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x ∂ν := by
  let μdirac : Measure ℝ := ((α : ENNReal) • Measure.dirac 0 : Measure ℝ)
  let μtilt : Measure ℝ :=
    ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))
  have hDiracFinite : IsFiniteMeasure μdirac := by
    refine ⟨?_⟩
    change (((α : ENNReal) • Measure.dirac (0 : ℝ)) Set.univ) < ⊤
    rw [Measure.smul_apply, Measure.dirac_apply_of_mem (by simp)]
    simp [smul_eq_mul]
  have hTiltFinite : IsFiniteMeasure μtilt := by
    dsimp [μtilt]
    simpa using
      (MeasureTheory.isFiniteMeasure_withDensity_ofReal (μ := ν) h_int.hasFiniteIntegral)
  letI : IsFiniteMeasure μdirac := hDiracFinite
  letI : IsFiniteMeasure μtilt := hTiltFinite
  have hDiracInt :
      Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) μdirac :=
    integrable_fourierKernel_of_isFiniteMeasure μdirac t
  have hTiltInt :
      Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) μtilt :=
    integrable_fourierKernel_of_isFiniteMeasure μtilt t
  have hDiracInt' :
      Integrable (fun x : ℝ ↦ Complex.exp (((t : ℂ) * x) * Complex.I)) μdirac := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hDiracInt
  have hTiltInt' :
      Integrable (fun x : ℝ ↦ Complex.exp (((t : ℂ) * x) * Complex.I)) μtilt := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hTiltInt
  have hDirac :
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂μdirac = α := by
    change
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂((α : ENNReal) • Measure.dirac 0) =
        α
    rw [integral_smul_measure, integral_dirac]
    have hsmul :
        ((α : ℝ) • Complex.exp ((((t * (0 : ℝ) : ℝ) : ℂ) * Complex.I))) = (α : ℂ) := by
      simp
    exact hsmul
  have hTilt :
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂μtilt =
        ∫ x : ℝ,
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x ∂ν := by
    dsimp [μtilt]
    rw [integral_withDensity_eq_integral_toReal_smul measurable_gaussianRecoveryKernel.ennreal_ofReal
      (by
        filter_upwards [gaussianRecoveryKernel_ae_ne_top (ν := ν)] with x hx
        exact lt_of_le_of_ne le_top hx)]
    refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
    simpa using gaussianRecoveryKernel_smul_fourier_eq t x
  have hDirac' :
      ∫ x : ℝ, Complex.exp (((t : ℂ) * x) * Complex.I) ∂μdirac = α := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hDirac
  have hTilt' :
      ∫ x : ℝ, Complex.exp (((t : ℂ) * x) * Complex.I) ∂μtilt =
        ∫ x : ℝ,
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x ∂ν := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hTilt
  have hAdd :
      ∫ x : ℝ, Complex.exp (((t : ℂ) * x) * Complex.I) ∂(μdirac + μtilt) =
        ∫ x : ℝ, Complex.exp (((t : ℂ) * x) * Complex.I) ∂μdirac +
          ∫ x : ℝ, Complex.exp (((t : ℂ) * x) * Complex.I) ∂μtilt := by
    simpa using integral_add_measure hDiracInt' hTiltInt'
  -- Proof comment: split the auxiliary measure into the Dirac atom at `0` and the weighted jump
  -- part, then rewrite both integrals explicitly.
  rw [gaussianRecoveryAuxFiniteMeasure, charFun_apply_real]
  change ∫ x : ℝ, Complex.exp (((t : ℂ) * x) * Complex.I) ∂(μdirac + μtilt) =
      (α : ℂ) + ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x ∂ν
  rw [hAdd, hDirac', hTilt']

/-- Helper for Theorem 16.22: the identity map is complex-integrable under the standard Gaussian
law. -/
private lemma integrable_complexId_gaussianReal_zero_one :
    Integrable (fun s : ℝ ↦ (s : ℂ)) (gaussianReal 0 1) := by
  have hmem : MemLp id 2 (gaussianReal 0 1) := by
    -- Proof comment: the standard Gaussian has finite second moment, so the identity belongs to
    -- `L²`.
    simpa using
      (ProbabilityTheory.memLp_id_gaussianReal'
        (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2 (by simp))
  have hint : Integrable (fun s : ℝ ↦ s) (gaussianReal 0 1) := by
    -- Proof comment: on the probability measure `gaussianReal 0 1`, `L²` control implies `L¹`
    -- integrability.
    exact hmem.integrable (by norm_num)
  -- Proof comment: complexification preserves integrability of the real-valued identity map.
  simpa using hint.ofReal

/-- Helper for Theorem 16.22: the centered standard Gaussian has vanishing complex first
moment. -/
private lemma integral_complexId_gaussianReal_zero_one :
    ∫ s : ℝ, (s : ℂ) ∂gaussianReal 0 1 = 0 := by
  -- Proof comment: convert the complex integral to the real one and use the centered Gaussian
  -- mean formula.
  rw [integral_complex_ofReal]
  rw [ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))]
  simp

/-- Helper for Theorem 16.22: the standard Gaussian has second moment `1`. -/
private lemma integral_sq_gaussianReal_zero_one :
    ∫ s : ℝ, s ^ (2 : ℕ) ∂gaussianReal 0 1 = 1 := by
  have hmem : MemLp id 2 (gaussianReal 0 1) := by
    -- Proof comment: use the standard Gaussian `L²` package to access the variance identity.
    simpa using
      (ProbabilityTheory.memLp_id_gaussianReal'
        (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2 (by simp))
  have hvariance :
      Var[id; gaussianReal 0 1] =
        ∫ s : ℝ, s ^ (2 : ℕ) ∂gaussianReal 0 1 - (∫ s : ℝ, s ∂gaussianReal 0 1) ^ (2 : ℕ) := by
    -- Proof comment: rewrite the Gaussian variance into second moment minus squared mean.
    simpa using (variance_eq_sub (μ := gaussianReal 0 1) (X := id) hmem)
  -- Proof comment: the standard Gaussian has variance `1` and mean `0`.
  rw [ProbabilityTheory.variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))] at hvariance
  simpa [ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))] using
    hvariance.symm

/-- Helper for Theorem 16.22: the real identity map is integrable under the standard Gaussian. -/
private lemma integrable_id_gaussianReal_zero_one :
    Integrable (fun s : ℝ ↦ s) (gaussianReal 0 1) := by
  have hmem : MemLp id 2 (gaussianReal 0 1) := by
    -- Proof comment: the standard Gaussian identity map lies in `L²`.
    simpa using
      (ProbabilityTheory.memLp_id_gaussianReal'
        (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2 (by simp))
  -- Proof comment: on a probability space, `L²` membership implies Bochner integrability.
  exact hmem.integrable (by norm_num)

/-- Helper for Theorem 16.22: the square function is integrable under the standard Gaussian. -/
private lemma integrable_sq_gaussianReal_zero_one :
    Integrable (fun s : ℝ ↦ s ^ (2 : ℕ)) (gaussianReal 0 1) := by
  have hmem : MemLp id 2 (gaussianReal 0 1) := by
    -- Proof comment: the standard Gaussian identity map lies in `L²`.
    simpa using
      (ProbabilityTheory.memLp_id_gaussianReal'
        (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2 (by simp))
  -- Proof comment: `L²` membership of the identity is exactly integrability of the square.
  simpa using hmem.integrable_sq

/-- Helper for Theorem 16.22: the shifted square remains integrable under the standard Gaussian. -/
private lemma integrable_shiftedSq_gaussianReal_zero_one (t : ℝ) :
    Integrable (fun s : ℝ ↦ (t + s) ^ (2 : ℕ)) (gaussianReal 0 1) := by
  have hpoly :
      Integrable (fun s : ℝ ↦ t ^ (2 : ℕ) + (2 * t) * s + s ^ (2 : ℕ)) (gaussianReal 0 1) := by
    -- Proof comment: expand the shifted square into constant, linear, and quadratic pieces.
    have hConst : Integrable (fun _ : ℝ ↦ t ^ (2 : ℕ)) (gaussianReal 0 1) := integrable_const _
    have hLinear : Integrable (fun s : ℝ ↦ (2 * t) * s) (gaussianReal 0 1) :=
      integrable_id_gaussianReal_zero_one.const_mul (2 * t)
    simpa [add_assoc] using (hConst.add hLinear).add integrable_sq_gaussianReal_zero_one
  -- Proof comment: rewrite `(t + s)²` into the polynomial normal form above.
  refine hpoly.congr ?_
  filter_upwards with s
  ring

/-- Helper for Theorem 16.22: the shifted square has Gaussian expectation `t² + 1`. -/
private lemma integral_shiftedSq_gaussianReal_zero_one (t : ℝ) :
    ∫ s : ℝ, (t + s) ^ (2 : ℕ) ∂gaussianReal 0 1 = t ^ (2 : ℕ) + 1 := by
  have hlin :
      Integrable (fun s : ℝ ↦ t ^ (2 : ℕ) + (2 * t) * s) (gaussianReal 0 1) := by
    -- Proof comment: the linearized part of the shifted square is integrable by previous lemmas.
    exact (integrable_const (t ^ (2 : ℕ))).add
      (integrable_id_gaussianReal_zero_one.const_mul (2 * t))
  calc
    ∫ s : ℝ, (t + s) ^ (2 : ℕ) ∂gaussianReal 0 1
        = ∫ s : ℝ, (t ^ (2 : ℕ) + (2 * t) * s + s ^ (2 : ℕ)) ∂gaussianReal 0 1 := by
            refine integral_congr_ae ?_
            filter_upwards with s
            ring
    _ =
        ∫ s : ℝ, (t ^ (2 : ℕ) + (2 * t) * s) ∂gaussianReal 0 1 +
          ∫ s : ℝ, s ^ (2 : ℕ) ∂gaussianReal 0 1 := by
            rw [integral_add hlin integrable_sq_gaussianReal_zero_one]
    _ =
        (∫ s : ℝ, (t ^ (2 : ℕ) : ℝ) ∂gaussianReal 0 1 +
            ∫ s : ℝ, (2 * t) * s ∂gaussianReal 0 1) +
          ∫ s : ℝ, s ^ (2 : ℕ) ∂gaussianReal 0 1 := by
            rw [integral_add (integrable_const (t ^ (2 : ℕ)))
              (integrable_id_gaussianReal_zero_one.const_mul (2 * t))]
    _ = t ^ (2 : ℕ) + (2 * t) * ∫ s : ℝ, s ∂gaussianReal 0 1 + 1 := by
          rw [integral_const, integral_const_mul, integral_sq_gaussianReal_zero_one]
          simp
    _ = t ^ (2 : ℕ) + 1 := by
          rw [ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))]
          ring

/-- Helper for Theorem 16.22: the shifted canonical-kernel weight is controlled by one
Gaussian-integrable quadratic factor. -/
private lemma max_shiftedKernelWeight_le_separableQuadratic (t s : ℝ) :
    max (3 * |t + s| ^ (2 : ℕ)) 2 ≤
      (6 * |t| ^ (2 : ℕ) + 6) * (s ^ (2 : ℕ) + 1) := by
  have hquad :
      3 * |t + s| ^ (2 : ℕ) ≤ (6 * |t| ^ (2 : ℕ) + 6) * (s ^ (2 : ℕ) + 1) := by
    have hsq :
        |t + s| ^ (2 : ℕ) ≤ 2 * (|t| ^ (2 : ℕ) + s ^ (2 : ℕ)) := by
      calc
        |t + s| ^ (2 : ℕ) ≤ (|t| + |s|) ^ (2 : ℕ) := by
          gcongr
          exact abs_add_le _ _
        _ ≤ 2 * (|t| ^ (2 : ℕ) + |s| ^ (2 : ℕ)) := by
          nlinarith [sq_nonneg (|t| - |s|)]
        _ = 2 * (|t| ^ (2 : ℕ) + s ^ (2 : ℕ)) := by
          simp [sq_abs]
    have hprod :
        |t| ^ (2 : ℕ) + s ^ (2 : ℕ) ≤ (|t| ^ (2 : ℕ) + 1) * (s ^ (2 : ℕ) + 1) := by
      nlinarith
    calc
      3 * |t + s| ^ (2 : ℕ) ≤ 3 * (2 * (|t| ^ (2 : ℕ) + s ^ (2 : ℕ))) := by
        gcongr
      _ = 6 * (|t| ^ (2 : ℕ) + s ^ (2 : ℕ)) := by ring
      _ ≤ 6 * ((|t| ^ (2 : ℕ) + 1) * (s ^ (2 : ℕ) + 1)) := by
        gcongr
      _ = (6 * |t| ^ (2 : ℕ) + 6) * (s ^ (2 : ℕ) + 1) := by ring
  have hconst :
      2 ≤ (6 * |t| ^ (2 : ℕ) + 6) * (s ^ (2 : ℕ) + 1) := by
    calc
      2 ≤ 6 := by norm_num
      _ ≤ 6 * (s ^ (2 : ℕ) + 1) := by nlinarith
      _ ≤ (6 * |t| ^ (2 : ℕ) + 6) * (s ^ (2 : ℕ) + 1) := by
        nlinarith [sq_nonneg t, sq_nonneg s]
  exact max_le_iff.2 ⟨hquad, hconst⟩

/-- Helper for Theorem 16.22: the Gaussian-shifted canonical jump kernel is integrable on the
product space needed for Fubini. -/
private lemma integrable_shiftedCanonicalKernel_prod
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) (t : ℝ) :
    Integrable
      (fun z : ℝ × ℝ ↦ levyKhinchinCanonicalKernelLocal (t + z.1) z.2)
      (((gaussianReal 0 1) : Measure ℝ).prod τ.ν) := by
  have hWeight :
      Integrable
        (fun s : ℝ ↦ (6 * |t| ^ (2 : ℕ) + 6) * (s ^ (2 : ℕ) + 1))
        (gaussianReal 0 1) := by
    -- Proof comment: the separable quadratic weight is a constant multiple of a second-moment
    -- integrand for the standard Gaussian.
    exact
      ((integrable_sq_gaussianReal_zero_one.add (integrable_const (1 : ℝ)))).const_mul
        (6 * |t| ^ (2 : ℕ) + 6)
  have hDom :
      Integrable
        (fun z : ℝ × ℝ ↦
          ((6 * |t| ^ (2 : ℕ) + 6) * (z.1 ^ (2 : ℕ) + 1)) * min (z.2 ^ (2 : ℕ)) 1)
        (((gaussianReal 0 1) : Measure ℝ).prod τ.ν) := by
    -- Proof comment: the product dominating function separates into the Gaussian and canonical
    -- factors, so Fubini applies directly.
    exact hWeight.smul_prod hτ.isCanonicalMeasure.integrable_sq_min_one
  have hMeas :
      Measurable (fun z : ℝ × ℝ ↦ levyKhinchinCanonicalKernelLocal (t + z.1) z.2) := by
    -- Proof comment: the shifted kernel is measurable because both coordinate maps are.
    have hExp :
        Measurable
          (fun z : ℝ × ℝ ↦
            Complex.exp ((((t + z.1) * z.2 : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    have hCenter :
        Measurable
          (fun z : ℝ × ℝ ↦
            ((((t + z.1) * levyKhinchinCanonicalCentering z.2 : ℝ) : ℂ) * Complex.I)) := by
      exact
        (Complex.measurable_ofReal.comp
          ((measurable_const.add measurable_fst).mul
            (measurable_levyKhinchinCanonicalCentering.comp measurable_snd))).mul_const Complex.I
    simpa [levyKhinchinCanonicalKernelLocal] using (hExp.sub measurable_const).sub hCenter
  refine Integrable.mono' hDom hMeas.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun z ↦ by
    -- Proof comment: the pointwise kernel bound reduces to the separable quadratic estimate.
    exact
      (norm_levyKhinchinCanonicalKernelLocal_le (t + z.1) z.2).trans <|
        mul_le_mul_of_nonneg_right
          (max_shiftedKernelWeight_le_separableQuadratic t z.1) (by positivity)

/-- Helper for Theorem 16.22: averaging the centered jump kernel against the standard Gaussian
replaces the oscillatory factor by the Gaussian damping factor and kills the linear correction. -/
private lemma integral_gaussianRecovery_shiftedCanonicalKernel
    (t x : ℝ) :
    ∫ s : ℝ, levyKhinchinCanonicalKernelLocal (t + s) x ∂gaussianReal 0 1 =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) -
        1 - (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) := by
  let c : ℝ := levyKhinchinCanonicalCentering x
  have hOscInt :
      Integrable
        (fun s : ℝ ↦ Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I))
        (gaussianReal 0 1) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun s ↦ by
      simpa using (le_of_eq (Complex.norm_exp_ofReal_mul_I ((t + s) * x)))
  have hLinearInt :
      Integrable
        (fun s : ℝ ↦ ((((t + s) * c : ℝ) : ℂ) * Complex.I))
        (gaussianReal 0 1) := by
    have hConst :
        Integrable (fun _ : ℝ ↦ (((t * c : ℝ) : ℂ) * Complex.I)) (gaussianReal 0 1) :=
      integrable_const _
    have hId :
        Integrable (fun s : ℝ ↦ (s : ℂ) * (((c : ℂ)) * Complex.I)) (gaussianReal 0 1) :=
      integrable_complexId_gaussianReal_zero_one.mul_const (((c : ℂ)) * Complex.I)
    refine (hConst.add hId).congr ?_
    filter_upwards with s
    simp [c]
    ring
  have hOscAvg :
      ∫ s : ℝ, Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) := by
    have hBase :
        Integrable
          (fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I))
          (gaussianReal 0 1) := by
      refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
      exact Filter.Eventually.of_forall fun s ↦ by
        simpa using (le_of_eq (Complex.norm_exp_ofReal_mul_I (s * x)))
    calc
      ∫ s : ℝ, Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
          ∫ s : ℝ,
            Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 := by
                refine integral_congr_ae <| Filter.Eventually.of_forall fun s ↦ ?_
                have hsplit :
                    ((((t + s) * x : ℝ) : ℂ) * Complex.I) =
                      ((((t * x : ℝ) : ℂ) + (((s * x : ℝ) : ℂ))) * Complex.I) := by
                  calc
                    ((((t + s) * x : ℝ) : ℂ) * Complex.I)
                        = ((((t * x : ℝ) + s * x : ℝ) : ℂ) * Complex.I) := by
                            congr 1
                            ring
                    _ = ((((t * x : ℝ) : ℂ) + (((s * x : ℝ) : ℂ))) * Complex.I) := by
                          norm_num
                calc
                  Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I)
                      = Complex.exp
                          ((((t * x : ℝ) : ℂ) + (((s * x : ℝ) : ℂ))) * Complex.I) := by
                              rw [hsplit]
                  _ =
                      Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I) +
                        (((s * x : ℝ) : ℂ) * Complex.I)) := by
                          rw [add_mul]
                  _ =
                      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                        Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by
                          rw [Complex.exp_add]
                  _ =
                      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                        Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by rfl
      _ = Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
            ∫ s : ℝ, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 := by
              simpa using
                (integral_const_mul (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I))
                  (fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I))
                  (μ := gaussianReal 0 1))
      _ = Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) := by
              have hGaussianChar :
                  ∫ s : ℝ, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
                    Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) := by
                simpa [MeasureTheory.charFun_apply_real, mul_comm] using
                  (ProbabilityTheory.charFun_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) x)
              rw [hGaussianChar]
  have hLinearAvg :
      ∫ s : ℝ, ((((t + s) * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
        (((t * c : ℝ) : ℂ) * Complex.I) := by
    calc
      ∫ s : ℝ, ((((t + s) * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
          ∫ s : ℝ,
            ((((t * c : ℝ) : ℂ) * Complex.I) + (s : ℂ) * (((c : ℂ)) * Complex.I))
              ∂gaussianReal 0 1 := by
                refine integral_congr_ae <| Filter.Eventually.of_forall fun s ↦ ?_
                simp [c]
                ring
      _ =
          ∫ s : ℝ, (((t * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 +
            ∫ s : ℝ, (s : ℂ) * (((c : ℂ)) * Complex.I) ∂gaussianReal 0 1 := by
              rw [integral_add (integrable_const _)
                (integrable_complexId_gaussianReal_zero_one.mul_const (((c : ℂ)) * Complex.I))]
      _ = (((t * c : ℝ) : ℂ) * Complex.I) := by
            have hMulConst :
                ∫ s : ℝ, (s : ℂ) * (((c : ℂ)) * Complex.I) ∂gaussianReal 0 1 =
                  (∫ s : ℝ, (s : ℂ) ∂gaussianReal 0 1) * (((c : ℂ)) * Complex.I) := by
              simpa using
                (integral_mul_const (((c : ℂ)) * Complex.I) (fun s : ℝ ↦ (s : ℂ))
                  (μ := gaussianReal 0 1))
            rw [integral_const, hMulConst, integral_complexId_gaussianReal_zero_one]
            simp
  -- Proof comment: split the shifted kernel into oscillatory, constant, and linear parts.
  change
    ∫ s : ℝ,
        (Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1 -
          ((((t + s) * c : ℝ) : ℂ) * Complex.I)) ∂gaussianReal 0 1 =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) -
        1 - (((t * c : ℝ) : ℂ) * Complex.I)
  have hSplitIntegral :
      ∫ s : ℝ,
          (Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1 -
            ((((t + s) * c : ℝ) : ℂ) * Complex.I)) ∂gaussianReal 0 1 =
        ∫ s : ℝ, (Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1) ∂gaussianReal 0 1 -
          ∫ s : ℝ, ((((t + s) * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 := by
    simpa [sub_eq_add_neg, add_assoc] using
      (integral_sub (hOscInt.sub (integrable_const (1 : ℂ))) hLinearInt)
  rw [hSplitIntegral, integral_sub hOscInt (integrable_const (1 : ℂ))]
  rw [hOscAvg, integral_const, hLinearAvg]
  simp [c]

/-- Helper for Theorem 16.22: Gaussian averaging of the quadratic Lévy term adds the unit
variance contribution. -/
private lemma integral_shiftedLevyQuadratic_gaussianReal_zero_one (σ2 t : ℝ) :
    ∫ s : ℝ, (((-(σ2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)) ∂gaussianReal 0 1 =
      (((-(σ2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) := by
  -- Proof comment: pull out the scalar coefficient and use the Gaussian second-moment identity.
  rw [integral_complex_ofReal, integral_const_mul, integral_shiftedSq_gaussianReal_zero_one]

/-- Helper for Theorem 16.22: Gaussian averaging kills the centered linear correction term. -/
private lemma integral_shiftedLinearComplex_gaussianReal_zero_one (c t : ℝ) :
    ∫ s : ℝ, ((((t + s) * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
      (((t * c : ℝ) : ℂ) * Complex.I) := by
  -- Proof comment: split the shifted linear term into a constant part and the centered Gaussian
  -- first moment, which vanishes.
  calc
    ∫ s : ℝ, ((((t + s) * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
        ∫ s : ℝ,
          ((((t * c : ℝ) : ℂ) * Complex.I) + (s : ℂ) * (((c : ℂ)) * Complex.I))
            ∂gaussianReal 0 1 := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun s ↦ ?_
              simp
              ring
    _ =
        ∫ s : ℝ, (((t * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 +
          ∫ s : ℝ, (s : ℂ) * (((c : ℂ)) * Complex.I) ∂gaussianReal 0 1 := by
            rw [integral_add (integrable_const _)
              (integrable_complexId_gaussianReal_zero_one.mul_const (((c : ℂ)) * Complex.I))]
    _ = (((t * c : ℝ) : ℂ) * Complex.I) := by
          have hMulConst :
              ∫ s : ℝ, (s : ℂ) * (((c : ℂ)) * Complex.I) ∂gaussianReal 0 1 =
                (∫ s : ℝ, (s : ℂ) ∂gaussianReal 0 1) * (((c : ℂ)) * Complex.I) := by
            simpa using
              (integral_mul_const (((c : ℂ)) * Complex.I) (fun s : ℝ ↦ (s : ℂ))
                (μ := gaussianReal 0 1))
          calc
            ∫ s : ℝ, (((t * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 +
                ∫ s : ℝ, (s : ℂ) * (((c : ℂ)) * Complex.I) ∂gaussianReal 0 1
                =
              (((t * c : ℝ) : ℂ) * Complex.I) +
                (∫ s : ℝ, (s : ℂ) ∂gaussianReal 0 1) * (((c : ℂ)) * Complex.I) := by
                  rw [integral_const, hMulConst]
                  simp [probReal_univ]
            _ = (((t * c : ℝ) : ℂ) * Complex.I) := by
                  rw [integral_complexId_gaussianReal_zero_one]
                  simp

/-- Helper for Theorem 16.22: Gaussian averaging rewrites the Lévy--Khintchin exponent in a fixed
normal form. -/
private lemma averageLevyKhinchinExponent_eq_normalForm_local
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) (t : ℝ) :
    ∫ s : ℝ, levyKhinchinExponent τ (t + s) ∂gaussianReal 0 1 =
      (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) +
        (((τ.b * t : ℝ) : ℂ) * Complex.I) +
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
              (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν := by
  have hKernelProd := integrable_shiftedCanonicalKernel_prod hτ t
  have hKernelSectionInt :
      Integrable
        (fun s : ℝ ↦ ∫ x : ℝ, levyKhinchinCanonicalKernelLocal (t + s) x ∂τ.ν)
        (gaussianReal 0 1) :=
    hKernelProd.integral_prod_left
  have hKernelSwap :
      ∫ s : ℝ, ∫ x : ℝ, levyKhinchinCanonicalKernelLocal (t + s) x ∂τ.ν ∂gaussianReal 0 1 =
        ∫ x : ℝ, ∫ s : ℝ, levyKhinchinCanonicalKernelLocal (t + s) x ∂gaussianReal 0 1 ∂τ.ν := by
    -- Proof comment: Fubini moves the Gaussian averaging inside the Lévy measure integral once
    -- the product kernel is shown integrable.
    simpa [Function.uncurry] using
      (integral_integral_swap
        (μ := gaussianReal 0 1) (ν := τ.ν)
        (f := fun s x ↦ levyKhinchinCanonicalKernelLocal (t + s) x)
        hKernelProd)
  have hKernelAvg :
      ∫ s : ℝ, ∫ x : ℝ, levyKhinchinCanonicalKernelLocal (t + s) x ∂τ.ν ∂gaussianReal 0 1 =
        ∫ x : ℝ,
          (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
            (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν := by
    -- Proof comment: the previously isolated Gaussian kernel average fixes one canonical spelling
    -- for the jump term and avoids reopening `levyKhinchinExponentWithCentering`.
    rw [hKernelSwap]
    refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
    exact integral_gaussianRecovery_shiftedCanonicalKernel t x
  have hQuadInt :
      Integrable
        (fun s : ℝ ↦ (((-(τ.sigma2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)))
        (gaussianReal 0 1) := by
    simpa [mul_assoc] using
      (((integrable_shiftedSq_gaussianReal_zero_one t).ofReal).const_mul
        (((( -(τ.sigma2 / 2) : ℝ) : ℂ))))
  have hLinearInt :
      Integrable
        (fun s : ℝ ↦ (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I))
        (gaussianReal 0 1) := by
    have hConst :
        Integrable (fun _ : ℝ ↦ (((τ.b * t : ℝ) : ℂ) * Complex.I)) (gaussianReal 0 1) :=
      integrable_const _
    have hId :
        Integrable (fun s : ℝ ↦ (s : ℂ) * (((τ.b : ℂ)) * Complex.I)) (gaussianReal 0 1) := by
      simpa [mul_comm] using
        integrable_complexId_gaussianReal_zero_one.const_mul (((τ.b : ℂ)) * Complex.I)
    refine (hConst.add hId).congr ?_
    filter_upwards with s
    simp
    ring
  -- Proof comment: average the quadratic, linear, and jump contributions separately, then
  -- reassemble the exponent in the fixed normal form used below.
  change
    ∫ s : ℝ,
        (((-(τ.sigma2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)) +
          (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I) +
            ∫ x : ℝ, levyKhinchinCanonicalKernelLocal (t + s) x ∂τ.ν
        ∂gaussianReal 0 1 =
      (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) +
        (((τ.b * t : ℝ) : ℂ) * Complex.I) +
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
              (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν
  have hSplit₁ :
      ∫ s : ℝ,
          ((((-(τ.sigma2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)) +
            (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I) +
            ∫ x : ℝ, levyKhinchinCanonicalKernelLocal (t + s) x ∂τ.ν) ∂gaussianReal 0 1 =
        ∫ s : ℝ,
            ((((-(τ.sigma2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)) +
              (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I)) ∂gaussianReal 0 1 +
          ∫ s : ℝ, ∫ x : ℝ, levyKhinchinCanonicalKernelLocal (t + s) x ∂τ.ν ∂gaussianReal 0 1 := by
    simpa [add_assoc] using
      (integral_add (hQuadInt.add hLinearInt) hKernelSectionInt)
  have hSplit₂ :
      ∫ s : ℝ,
          ((((-(τ.sigma2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)) +
            (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I)) ∂gaussianReal 0 1 =
        ∫ s : ℝ, (((-(τ.sigma2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)) ∂gaussianReal 0 1 +
          ∫ s : ℝ, (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 := by
    exact integral_add hQuadInt hLinearInt
  have hLinearAvg' :
      ∫ s : ℝ, (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
        (((τ.b * t : ℝ) : ℂ) * Complex.I) := by
    simpa [mul_comm] using integral_shiftedLinearComplex_gaussianReal_zero_one τ.b t
  rw [hSplit₁, hSplit₂]
  rw [integral_shiftedLevyQuadratic_gaussianReal_zero_one]
  calc
    (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) +
          ∫ s : ℝ, (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 +
          ∫ s : ℝ, ∫ x : ℝ, levyKhinchinCanonicalKernelLocal (t + s) x ∂τ.ν ∂gaussianReal 0 1
        =
      (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) +
          (((τ.b * t : ℝ) : ℂ) * Complex.I) +
          ∫ s : ℝ, ∫ x : ℝ, levyKhinchinCanonicalKernelLocal (t + s) x ∂τ.ν ∂gaussianReal 0 1 := by
            simpa [add_assoc] using
              congrArg
                (fun z : ℂ ↦
                  (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) + z +
                    ∫ s : ℝ, ∫ x : ℝ, levyKhinchinCanonicalKernelLocal (t + s) x ∂τ.ν
                      ∂gaussianReal 0 1)
                hLinearAvg'
    _ =
      (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) +
        (((τ.b * t : ℝ) : ℂ) * Complex.I) +
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
              (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν := by
            rw [hKernelAvg]

/-- Helper for Theorem 16.22: subtracting the Gaussian-smoothed jump kernel leaves exactly the
recovery kernel term. -/
private lemma canonicalKernel_sub_gaussianSmoothed_eq_recoveryKernel_local
    (t x : ℝ) :
    levyKhinchinCanonicalKernelLocal t x -
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
          (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x := by
  -- Proof comment: this is the one-line algebraic bridge between the canonical jump kernel and
  -- the Gaussian-damped kernel.
  simp [levyKhinchinCanonicalKernelLocal, gaussianRecoveryKernel]
  ring_nf

/-- Helper for Theorem 16.22: Gaussian smoothing converts the Lévy--Khintchin exponent into the
characteristic function of the auxiliary finite measure. -/
private lemma gaussianSmoothedExponent_eq_auxCharFun
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) (t : ℝ) :
    let α : NNReal := ⟨τ.sigma2 / 2, by
      exact div_nonneg hτ.sigma2_nonneg (by positivity)⟩
    charFun (((gaussianRecoveryAuxFiniteMeasure α τ.ν
      (integrable_gaussianRecoveryKernel hτ.isCanonicalMeasure) : FiniteMeasure ℝ) :
        Measure ℝ)) t =
      levyKhinchinExponent τ t -
        ∫ s : ℝ, levyKhinchinExponent τ (t + s) ∂gaussianReal 0 1 := by
  let α : NNReal := ⟨τ.sigma2 / 2, by
    exact div_nonneg hτ.sigma2_nonneg (by positivity)⟩
  have hAverage := averageLevyKhinchinExponent_eq_normalForm_local hτ t
  have hKernelInt :
      Integrable (levyKhinchinCanonicalKernelLocal t) τ.ν :=
    integrable_levyKhinchinCanonicalKernelLocal hτ.isCanonicalMeasure t
  have hRecoveryInt :
      Integrable
        (fun x : ℝ ↦
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x)
        τ.ν := by
    have hExpMeas :
        Measurable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) := by
      exact
        Complex.continuous_exp.measurable.comp <|
          (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const
            Complex.I
    have hKernelMeas : Measurable (fun x : ℝ ↦ (gaussianRecoveryKernel x : ℂ)) := by
      exact Complex.measurable_ofReal.comp measurable_gaussianRecoveryKernel
    refine (integrable_gaussianRecoveryKernel hτ.isCanonicalMeasure).mono'
      (hExpMeas.mul hKernelMeas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      have hnormExp : ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ = 1 := by
        simpa using (Complex.norm_exp_ofReal_mul_I (t * x))
      have hnonneg : 0 ≤ gaussianRecoveryKernel x := gaussianRecoveryKernel_nonneg x
      calc
        ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x‖
            = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ * ‖gaussianRecoveryKernel x‖ := by
                simp
        _ ≤ gaussianRecoveryKernel x := by
              rw [hnormExp]
              simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hAvgKernelInt :
      Integrable
        (fun x : ℝ ↦
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
            (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I))
        τ.ν := by
    refine (hKernelInt.sub hRecoveryInt).congr ?_
    filter_upwards with x
    simp [levyKhinchinCanonicalKernelLocal, gaussianRecoveryKernel]
    ring_nf
  have hKernelDiff :
      ∫ x : ℝ, levyKhinchinCanonicalKernelLocal t x ∂τ.ν -
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
              (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν =
        ∫ x : ℝ,
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x ∂τ.ν := by
    rw [← integral_sub hKernelInt hAvgKernelInt]
    refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
    exact canonicalKernel_sub_gaussianSmoothed_eq_recoveryKernel_local t x
  have hKernelExpand :
      ∫ x : ℝ, levyKhinchinCanonicalKernelLocal t x ∂τ.ν =
        ∫ x : ℝ,
          (-1 - Complex.I * ↑(t * levyKhinchinCanonicalCentering x) +
            Complex.exp (Complex.I * ↑(t * x))) ∂τ.ν := by
    refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
    simp [levyKhinchinCanonicalKernelLocal, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      mul_assoc, mul_left_comm, mul_comm]
  -- Proof comment: Gaussian averaging contributes the extra atom `σ² / 2` and replaces the jump
  -- kernel by the damped test function `gaussianRecoveryKernel`.
  calc
    charFun (((gaussianRecoveryAuxFiniteMeasure α τ.ν
      (integrable_gaussianRecoveryKernel hτ.isCanonicalMeasure) : FiniteMeasure ℝ) :
        Measure ℝ)) t =
        (α : ℂ) +
          ∫ x : ℝ,
            Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x ∂τ.ν := by
              exact
                gaussianRecoveryAuxFiniteMeasure_charFun α
                  (integrable_gaussianRecoveryKernel hτ.isCanonicalMeasure) t
    _ = levyKhinchinExponent τ t -
          ∫ s : ℝ, levyKhinchinExponent τ (t + s) ∂gaussianReal 0 1 := by
            rw [hAverage, levyKhinchinExponent, levyKhinchinExponentWithCentering]
            rw [← hKernelDiff]
            have hAlpha :
                (α : ℂ) =
                  (((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) -
                    (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) := by
              simp [α]
              ring
            rw [hAlpha]
            rw [hKernelExpand]
            ring_nf

/-- Helper for Theorem 16.22: equality of the Lévy--Khintchin exponents identifies the
Gaussian-smoothed auxiliary finite measures. -/
private lemma gaussianRecoveryAuxFiniteMeasure_eq_of_exponentEq
    {τ₁ τ₂ : LevyKhinchinTriple}
    (hτ₁ : IsCanonicalTriple τ₁) (hτ₂ : IsCanonicalTriple τ₂)
    (hExp : ∀ t : ℝ, levyKhinchinExponent τ₁ t = levyKhinchinExponent τ₂ t) :
    let α₁ : NNReal := ⟨τ₁.sigma2 / 2, by
      exact div_nonneg hτ₁.sigma2_nonneg (by positivity)⟩
    let α₂ : NNReal := ⟨τ₂.sigma2 / 2, by
      exact div_nonneg hτ₂.sigma2_nonneg (by positivity)⟩
    gaussianRecoveryAuxFiniteMeasure α₁ τ₁.ν
        (integrable_gaussianRecoveryKernel hτ₁.isCanonicalMeasure) =
      gaussianRecoveryAuxFiniteMeasure α₂ τ₂.ν
        (integrable_gaussianRecoveryKernel hτ₂.isCanonicalMeasure) := by
  let α₁ : NNReal := ⟨τ₁.sigma2 / 2, by
    exact div_nonneg hτ₁.sigma2_nonneg (by positivity)⟩
  let α₂ : NNReal := ⟨τ₂.sigma2 / 2, by
    exact div_nonneg hτ₂.sigma2_nonneg (by positivity)⟩
  apply FiniteMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  have hDiff :
      levyKhinchinExponent τ₁ t -
          ∫ s : ℝ, levyKhinchinExponent τ₁ (t + s) ∂gaussianReal 0 1 =
        levyKhinchinExponent τ₂ t -
          ∫ s : ℝ, levyKhinchinExponent τ₂ (t + s) ∂gaussianReal 0 1 := by
    rw [hExp t]
    congr 1
    refine integral_congr_ae <| Filter.Eventually.of_forall fun s ↦ ?_
    exact hExp (t + s)
  -- Proof comment: after rewriting both sides by the Gaussian smoothing identity, pointwise
  -- equality of exponents gives equality of the auxiliary characteristic functions.
  calc
    charFun (((gaussianRecoveryAuxFiniteMeasure α₁ τ₁.ν
      (integrable_gaussianRecoveryKernel hτ₁.isCanonicalMeasure) : FiniteMeasure ℝ) :
        Measure ℝ)) t =
        levyKhinchinExponent τ₁ t -
          ∫ s : ℝ, levyKhinchinExponent τ₁ (t + s) ∂gaussianReal 0 1 := by
            exact gaussianSmoothedExponent_eq_auxCharFun hτ₁ t
    _ =
        levyKhinchinExponent τ₂ t -
          ∫ s : ℝ, levyKhinchinExponent τ₂ (t + s) ∂gaussianReal 0 1 := hDiff
    _ =
        charFun (((gaussianRecoveryAuxFiniteMeasure α₂ τ₂.ν
          (integrable_gaussianRecoveryKernel hτ₂.isCanonicalMeasure) : FiniteMeasure ℝ) :
            Measure ℝ)) t := by
              exact (gaussianSmoothedExponent_eq_auxCharFun hτ₂ t).symm

/-- Helper for Theorem 16.22: for the current theorem, same-law Lévy--Khintchin representations
already need only the Gaussian coefficient and Lévy measure to agree. -/
private lemma sigma2_levyMeasure_eq_of_sameRepresentation
    {μ : ProbabilityMeasure ℝ} {τ₁ τ₂ : LevyKhinchinTriple}
    (hτ₁ : HasLevyKhinchinRepresentation μ τ₁)
    (hτ₂ : HasLevyKhinchinRepresentation μ τ₂) :
    τ₁.sigma2 = τ₂.sigma2 ∧ τ₁.ν = τ₂.ν := by
  have hExp :
      ∀ t : ℝ, levyKhinchinExponent τ₁ t = levyKhinchinExponent τ₂ t :=
    levyKhinchinExponent_eq_of_sameRepresentation_of_continuous
      hτ₁
      hτ₂
      (continuousLevyKhinchinExponentLocal hτ₁.isCanonicalTriple)
      (continuousLevyKhinchinExponentLocal hτ₂.isCanonicalTriple)
  let α₁ : NNReal := ⟨τ₁.sigma2 / 2, by
    exact div_nonneg hτ₁.isCanonicalTriple.sigma2_nonneg (by positivity)⟩
  let α₂ : NNReal := ⟨τ₂.sigma2 / 2, by
    exact div_nonneg hτ₂.isCanonicalTriple.sigma2_nonneg (by positivity)⟩
  have hAuxEq :
      gaussianRecoveryAuxFiniteMeasure α₁ τ₁.ν
          (integrable_gaussianRecoveryKernel hτ₁.isCanonicalTriple.isCanonicalMeasure) =
        gaussianRecoveryAuxFiniteMeasure α₂ τ₂.ν
          (integrable_gaussianRecoveryKernel hτ₂.isCanonicalTriple.isCanonicalMeasure) := by
    simpa [α₁, α₂] using
      gaussianRecoveryAuxFiniteMeasure_eq_of_exponentEq
        hτ₁.isCanonicalTriple hτ₂.isCanonicalTriple hExp
  have hAlpha :
      (α₁ : ENNReal) = α₂ := by
    have hZero :=
      congrArg
        (fun ν : FiniteMeasure ℝ ↦ ((ν : Measure ℝ) ({0} : Set ℝ)))
        hAuxEq
    simpa [gaussianRecoveryAuxFiniteMeasure_apply_zero] using hZero
  have hAlphaNN : α₁ = α₂ := ENNReal.coe_inj.mp hAlpha
  have hSigmaHalf : τ₁.sigma2 / 2 = τ₂.sigma2 / 2 := by
    simpa [α₁, α₂] using congrArg (fun a : NNReal ↦ (a : ℝ)) hAlphaNN
  have hSigma : τ₁.sigma2 = τ₂.sigma2 := by
    linarith
  have hTiltRestrict :
      ((τ₁.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
          (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) =
        ((τ₂.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
          (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) := by
    have hRestrict :=
      congrArg
        (fun ν : FiniteMeasure ℝ ↦ ((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ)))
        hAuxEq
    change
      ((((α₁ : ENNReal) • Measure.dirac 0 +
          τ₁.ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).restrict
          ({0}ᶜ : Set ℝ))) =
        ((((α₂ : ENNReal) • Measure.dirac 0 +
          τ₂.ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).restrict
          ({0}ᶜ : Set ℝ))) at hRestrict
    rw [Measure.restrict_add, Measure.restrict_smul,
      restrict_dirac' ((measurableSet_singleton (0 : ℝ)).compl), if_neg (by simp),
      smul_zero, zero_add, MeasureTheory.restrict_withDensity
        ((measurableSet_singleton (0 : ℝ)).compl),
      Measure.restrict_add, Measure.restrict_smul,
      restrict_dirac' ((measurableSet_singleton (0 : ℝ)).compl), if_neg (by simp),
      smul_zero, zero_add, MeasureTheory.restrict_withDensity
        ((measurableSet_singleton (0 : ℝ)).compl)] at hRestrict
    exact hRestrict
  have hNuRestrict :
      τ₁.ν.restrict ({0}ᶜ : Set ℝ) = τ₂.ν.restrict ({0}ᶜ : Set ℝ) := by
    have hInv :=
      congrArg
        (fun η : Measure ℝ ↦
          η.withDensity (fun x ↦ (ENNReal.ofReal (gaussianRecoveryKernel x))⁻¹))
        hTiltRestrict
    -- Proof comment: on `{0}ᶜ`, the Gaussian recovery density is strictly positive, so a second
    -- `withDensity` by its inverse removes the tilt and recovers the punctured jump measure.
    calc
      τ₁.ν.restrict ({0}ᶜ : Set ℝ) =
          (((τ₁.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
              (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).withDensity
            (fun x ↦ (ENNReal.ofReal (gaussianRecoveryKernel x))⁻¹)) := by
              symm
              exact
                withDensity_gaussianRecoveryKernel_inv_same_restrict_compl_singleton τ₁.ν
      _ =
          (((τ₂.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
              (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).withDensity
            (fun x ↦ (ENNReal.ofReal (gaussianRecoveryKernel x))⁻¹)) := hInv
      _ = τ₂.ν.restrict ({0}ᶜ : Set ℝ) := by
            exact
              withDensity_gaussianRecoveryKernel_inv_same_restrict_compl_singleton τ₂.ν
  have hNu : τ₁.ν = τ₂.ν := by
    have hZeroRestrict :
        τ₁.ν.restrict ({0} : Set ℝ) = τ₂.ν.restrict ({0} : Set ℝ) := by
      rw [Measure.restrict_singleton, hτ₁.isCanonicalTriple.isCanonicalMeasure.measure_singleton_zero,
        zero_smul, Measure.restrict_singleton,
        hτ₂.isCanonicalTriple.isCanonicalMeasure.measure_singleton_zero, zero_smul]
    rw [← Measure.restrict_add_restrict_compl (μ := τ₁.ν) (measurableSet_singleton (0 : ℝ)),
      ← Measure.restrict_add_restrict_compl (μ := τ₂.ν) (measurableSet_singleton (0 : ℝ)),
      hZeroRestrict]
    exact congrArg (fun η : Measure ℝ ↦ τ₂.ν.restrict ({0} : Set ℝ) + η) hNuRestrict
  exact ⟨hSigma, hNu⟩
/-- Helper for Theorem 16.22: the exact-root compound-Poisson approximant intensity is obtained
by puncturing the scaled root law at `0`. -/
private noncomputable def exactRootApproxIntensity
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    FiniteMeasure ℝ :=
  (puncturedIntensity
      (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
        FiniteMeasure ℝ))).map Subtype.val

/-- Helper for Theorem 16.22: deleting the zero atom does not change the exact-root
compound-Poisson approximant law. -/
private theorem exactRootApproxLaw_eq_fullCompoundPoisson_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    compoundPoissonMeasure (exactRootApproxIntensity μroot n) =
      compoundPoissonMeasure
        (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
          FiniteMeasure ℝ)) := by
  let νFinite : FiniteMeasure ℝ :=
    (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
      FiniteMeasure ℝ))
  -- Proof comment: the deleted mass sits at the irrelevant atom `0`, so both intensities define
  -- the same compound-Poisson law.
  simpa [exactRootApproxIntensity, νFinite] using
    (compoundPoissonMeasure_ignoreZeroAtom νFinite)

/-- Helper for Theorem 16.22: after puncturing the exact-root intensities, the compound-Poisson
approximants still converge weakly to `μ`. -/
private theorem exactRootApproxLaw_tendsto_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ) :
    Tendsto
      (fun n : ℕ ↦ compoundPoissonMeasure (exactRootApproxIntensity μroot n))
      atTop
      (𝓝 μ) := by
  -- Proof comment: pointwise equality with the full exact-root approximants lets us reuse the
  -- earlier convergence theorem unchanged.
  refine Tendsto.congr' ?_ (exactRootCompoundPoissonApproximation_local μroot hroot)
  exact Filter.Eventually.of_forall fun n ↦ by
    simpa using (exactRootApproxLaw_eq_fullCompoundPoisson_local μroot n).symm

/-- Helper for Theorem 16.22: the punctured exact-root approximation carries its canonical
compound-Poisson Lévy--Khintchin triple. -/
private noncomputable def exactRootApproxTriple
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    LevyKhinchinTriple :=
  { sigma2 := 0
    b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂(exactRootApproxIntensity μroot n : Measure ℝ)
    ν := (exactRootApproxIntensity μroot n : Measure ℝ) }

/-- Helper for Theorem 16.22: each punctured exact-root approximant already has its canonical
compound-Poisson Lévy--Khintchin representation. -/
private lemma exactRootApproxTriple_hasLevyKhinchinRepresentation_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    HasLevyKhinchinRepresentation
      (compoundPoissonMeasure (exactRootApproxIntensity μroot n))
      (exactRootApproxTriple μroot n) := by
  let νPunctured : FiniteMeasure {x : ℝ // x ≠ 0} :=
    puncturedIntensity
      (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
        FiniteMeasure ℝ))
  -- Proof comment: once the zero atom is removed, the remaining finite jump intensity is already
  -- a canonical compound-Poisson Lévy measure.
  simpa [exactRootApproxTriple, exactRootApproxIntensity, νPunctured] using
    compoundPoisson_hasLevyKhinchinRepresentation
      ((νPunctured.map Subtype.val : FiniteMeasure ℝ) : Measure ℝ)
      (map_puncturedFiniteMeasure_apply_singleton_zero νPunctured)

/-- Helper for Theorem 16.22: the Gaussian-recovery auxiliary finite measure attached to the
`n`th exact-root approximant triple. -/
private noncomputable def exactRootApproxAuxFiniteMeasure
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) : FiniteMeasure ℝ :=
  gaussianRecoveryAuxFiniteMeasure 0
    (exactRootApproxTriple μroot n).ν
    (integrable_gaussianRecoveryKernel (
      (exactRootApproxTriple_hasLevyKhinchinRepresentation_local μroot n).isCanonicalTriple.isCanonicalMeasure))

/-- Helper for Theorem 16.22: the exact-root auxiliary finite measure realizes the
Gaussian-smoothed exponent of the `n`th approximant. -/
private lemma exactRootApproxAuxFiniteMeasure_charFun_eq_smoothedExponent_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t =
      levyKhinchinExponent (exactRootApproxTriple μroot n) t -
        ∫ s : ℝ, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
          ∂gaussianReal 0 1 := by
  -- Proof comment: specialize the general Gaussian-smoothing identity to the finite exact-root
  -- approximant triple, whose Gaussian coefficient is already `0`.
  simpa [exactRootApproxAuxFiniteMeasure, exactRootApproxTriple] using
    gaussianSmoothedExponent_eq_auxCharFun
      (exactRootApproxTriple_hasLevyKhinchinRepresentation_local μroot n).isCanonicalTriple t

/-- Helper for Theorem 16.22: the exact-root approximant exponent already has the fixed
`Ψ`-normal form `((n + 1) * (exp (Ψ / (n + 1)) - 1))`. -/
private lemma exactRootApproxExponent_eq_expLiftIncrement_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (n : ℕ) (t : ℝ) :
    levyKhinchinExponent (exactRootApproxTriple μroot n) t =
      ((n + 1 : ℕ) : ℂ) * (Complex.exp (Ψ t / (((n + 1 : ℕ) : ℂ))) - 1) := by
  let μn : ProbabilityMeasure ℝ := compoundPoissonMeasure (exactRootApproxIntensity μroot n)
  let Λ : C(ℝ, ℂ) :=
    ⟨fun s : ℝ ↦ ((n + 1 : ℕ) : ℂ) * (charFun (μroot (Nat.succPNat n) : Measure ℝ) s - 1), by
      -- Proof comment: continuity of the root characteristic function keeps the linearized lift
      -- continuous.
      simpa using
        ((MeasureTheory.continuous_charFun : Continuous
          (charFun (μroot (Nat.succPNat n) : Measure ℝ))).sub continuous_const).const_mul
          ((n + 1 : ℕ) : ℂ)⟩
  obtain ⟨Lift, hLift, hLiftUnique⟩ :=
    existsUniqueContinuousExpLift
      (MeasureTheory.continuous_charFun : Continuous (charFun (μn : Measure ℝ)))
      (by
        intro s
        rw [(exactRootApproxTriple_hasLevyKhinchinRepresentation_local μroot n).charFun_eq_exp s]
        exact Complex.exp_ne_zero _)
      (by simpa [μn] using (MeasureTheory.charFun_zero (μ := (μn : Measure ℝ))))
  have hExponentLift :
      (⟨levyKhinchinExponent (exactRootApproxTriple μroot n),
          continuousLevyKhinchinExponentLocal
            (exactRootApproxTriple_hasLevyKhinchinRepresentation_local μroot n).isCanonicalTriple⟩ :
        C(ℝ, ℂ)) = Lift := by
    apply hLiftUnique
    constructor
    · -- Proof comment: the exact-root approximant exponent keeps the standard normalization at
      -- the origin.
      simpa using levyKhinchinExponent_zero (exactRootApproxTriple μroot n)
    · intro s
      -- Proof comment: the exact-root approximant triple represents `μn` by construction.
      simpa [μn] using
        ((exactRootApproxTriple_hasLevyKhinchinRepresentation_local μroot n).charFun_eq_exp s).symm
  have hLinearizedLift : Λ = Lift := by
    apply hLiftUnique
    constructor
    · -- Proof comment: the explicit linearized lift also vanishes at the origin.
      simp [Λ]
    · intro s
      let νFinite : FiniteMeasure ℝ :=
        (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
          FiniteMeasure ℝ))
      have hμnEq :
          μn = compoundPoissonMeasure νFinite := by
        -- Proof comment: puncturing the zero atom leaves the exact-root compound-Poisson law
        -- unchanged.
        simpa [μn, exactRootApproxIntensity, νFinite] using
          (compoundPoissonMeasure_ignoreZeroAtom νFinite)
      calc
        Complex.exp (Λ s)
            = charFun (compoundPoissonMeasure νFinite : Measure ℝ) s := by
                simpa [Λ, νFinite] using
                  (charFun_compoundPoissonMeasure_natSmulProbability
                    (μroot (Nat.succPNat n)) (n + 1) s).symm
        _ = charFun (μn : Measure ℝ) s := by simpa [hμnEq]
  have hRootChar :
      charFun (μroot (Nat.succPNat n) : Measure ℝ) t =
        Complex.exp (Ψ t / (((n + 1 : ℕ) : ℂ))) := by
    have hcfp :
        ∀ m : ℕ+, IsCFP (fun s : ℝ ↦ charFun (μroot m : Measure ℝ) s) := by
      intro m
      simpa using ProbabilityMeasure.isCFP_charFun (μroot m)
    have hpow :
        ∀ m : ℕ+, ∀ s : ℝ,
          (charFun (μroot m : Measure ℝ) s) ^ (m : ℕ) = charFun (μ : Measure ℝ) s := by
      intro m s
      calc
        (charFun (μroot m : Measure ℝ) s) ^ (m : ℕ)
            = charFun ((μroot m ^ (m : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) s := by
                simpa using
                  (congrArg (fun f : ℝ → ℂ ↦ f s)
                    (ProbabilityMeasure.charFun_pow (μroot m) (m : ℕ))).symm
        _ = charFun (μ : Measure ℝ) s := by
              simpa using
                congrArg (fun ν : ProbabilityMeasure ℝ ↦ charFun (ν : Measure ℝ) s) (hroot m)
    -- Proof comment: the exact-root lift theorem rewrites the root characteristic function into
    -- the fixed logarithmic-lift spelling `exp (Ψ / (n + 1))`.
    simpa [Nat.succPNat_coe] using
      exactRoot_eq_expDivLift
        (φ := charFun (μ : Measure ℝ))
        (φs := fun m s ↦ charFun (μroot m : Measure ℝ) s)
        hcfp hpow hΨ0 hΨexp (Nat.succPNat n) t
  have hLiftEq :
      levyKhinchinExponent (exactRootApproxTriple μroot n) t =
        ((n + 1 : ℕ) : ℂ) * (charFun (μroot (Nat.succPNat n) : Measure ℝ) t - 1) := by
    -- Proof comment: both candidate formulas are the unique normalized continuous lifts of the
    -- same exact-root approximant characteristic function.
    exact congrArg (fun f : C(ℝ, ℂ) ↦ f t) (hExponentLift.trans hLinearizedLift.symm)
  calc
    levyKhinchinExponent (exactRootApproxTriple μroot n) t
        = ((n + 1 : ℕ) : ℂ) * (charFun (μroot (Nat.succPNat n) : Measure ℝ) t - 1) := hLiftEq
    _ = ((n + 1 : ℕ) : ℂ) * (Complex.exp (Ψ t / (((n + 1 : ℕ) : ℂ))) - 1) := by
          rw [hRootChar]

/-- Helper for Theorem 16.22: for fixed `w : ℂ`, the scaled exponential increment
`(n + 1) * (exp (w / (n + 1)) - 1)` converges to `w`. -/
private lemma natSuccMulExpDivSubOne_norm_le_local (w : ℂ) (n : ℕ)
    (hsmall : ‖w / ((n + 1 : ℕ) : ℂ)‖ ≤ 1) :
    ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w‖ ≤
      ‖w‖ ^ (2 : ℕ) / (n + 1 : ℝ) := by
  have hn0C : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hn0R : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hrew :
      ((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w =
        ((n + 1 : ℕ) : ℂ) *
          (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1 - w / ((n + 1 : ℕ) : ℂ)) := by
    -- Proof comment: factor the difference so the quadratic exponential remainder estimate applies
    -- directly to `w / (n + 1)`.
    field_simp [hn0C]
  calc
    ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w‖
        =
      ‖((n + 1 : ℕ) : ℂ) *
          (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1 - w / ((n + 1 : ℕ) : ℂ))‖ := by
            rw [hrew]
    _ ≤ ‖((n + 1 : ℕ) : ℂ)‖ * ‖w / ((n + 1 : ℕ) : ℂ)‖ ^ (2 : ℕ) := by
          -- Proof comment: on the unit ball, the exponential remainder is quadratic in the
          -- argument size.
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (Complex.norm_exp_sub_one_sub_id_le hsmall) (norm_nonneg _)
    _ = (n + 1 : ℝ) * (‖w‖ / (n + 1 : ℝ)) ^ (2 : ℕ) := by
          rw [Complex.norm_natCast, norm_div, Complex.norm_natCast]
          norm_num
    _ = ‖w‖ ^ (2 : ℕ) / (n + 1 : ℝ) := by
          field_simp [hn0R]

/-- Helper for Theorem 16.22: the scalar exact-root linearization converges uniformly on every
bounded complex ball. -/
private lemma natSucc_mul_expDiv_sub_one_tendstoUniformlyOn_ball_local (R : ℝ) :
    TendstoUniformlyOn
      (fun n : ℕ ↦ fun w : ℂ ↦
        ((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1))
      (fun w : ℂ ↦ w) atTop (Metric.ball (0 : ℂ) R) := by
  by_cases hR : 0 < R
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hzero :
        Tendsto (fun n : ℕ ↦ R ^ (2 : ℕ) / (n + 1 : ℝ)) atTop (𝓝 0) := by
      have hden :
          Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
        simpa [Nat.cast_add] using
          tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
      have hinv :
          Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hden
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ R ^ (2 : ℕ)) atTop (𝓝 (R ^ (2 : ℕ)))).mul
          hinv
    have hsmallEventually :
        ∀ᶠ n : ℕ in atTop, R ^ (2 : ℕ) / (n + 1 : ℝ) < ε := by
      exact hzero (Iio_mem_nhds hε)
    filter_upwards [Filter.eventually_ge_atTop (Nat.ceil R), hsmallEventually] with n hnR hnε w hw
    have hwR : ‖w‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hsmallNum : ‖w‖ / (n + 1 : ℝ) ≤ 1 := by
      have hRle : R ≤ (n + 1 : ℝ) := by
        calc
          R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil _
          _ ≤ n := by exact_mod_cast hnR
          _ ≤ n + 1 := by linarith
      exact
        (div_le_iff₀ (show (0 : ℝ) < n + 1 by positivity)).2
          (by simpa [one_mul] using le_trans (le_of_lt hwR) hRle)
    have hsmall :
        ‖w / ((n + 1 : ℕ) : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_natCast]
      simpa using hsmallNum
    have hbound := natSuccMulExpDivSubOne_norm_le_local w n hsmall
    have hboundR :
        ‖w‖ ^ (2 : ℕ) / (n + 1 : ℝ) ≤ R ^ (2 : ℕ) / (n + 1 : ℝ) := by
      have hwRle : ‖w‖ ≤ R := le_of_lt hwR
      have hsq : ‖w‖ ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hR.le] using hwRle
      exact div_le_div_of_nonneg_right hsq (by positivity)
    have hdist :
        dist w (((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1)) =
          ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w‖ := by
      rw [dist_eq_norm, norm_sub_rev]
    exact
      lt_of_le_of_lt
        (hdist ▸ hbound.trans hboundR)
        hnε
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [] with n w hw
    exfalso
    have hposR : 0 < R := by
      exact lt_of_le_of_lt (by simpa using norm_nonneg w) hw
    exact hR hposR

/-- Helper for Theorem 16.22: the exact-root compound-Poisson approximant exponents converge
uniformly on every compact interval to the retained lift `Ψ`. -/
private lemma exactRootApproxExponent_tendstoUniformlyOn_interval_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (a b : ℝ) :
    TendstoUniformlyOn
      (fun n t ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) t)
      (fun t ↦ Ψ t) atTop (Set.Icc a b) := by
  rcases
      (isCompact_Icc.image Ψ.continuous).isBounded.subset_ball (0 : ℂ) with
    ⟨R, hR⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hball :
      ∀ᶠ n : ℕ in atTop,
        ∀ w ∈ Metric.ball (0 : ℂ) R,
          dist w (((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1)) < ε := by
    exact
      (Metric.tendstoUniformlyOn_iff.1
        (natSucc_mul_expDiv_sub_one_tendstoUniformlyOn_ball_local R)) ε hε
  filter_upwards [hball] with n hn t ht
  have hΨt : Ψ t ∈ Metric.ball (0 : ℂ) R := hR ⟨t, ht, rfl⟩
  -- Proof comment: on the compact interval, the exact-root exponent is exactly the scalar
  -- linearization evaluated at the bounded lift value `Ψ t`.
  simpa [exactRootApproxExponent_eq_expLiftIncrement_local
    (μroot := μroot) (μ := μ) hroot (Ψ := Ψ) hΨ0 hΨexp n t] using hn (Ψ t) hΨt

/-- Helper for Theorem 16.22: for fixed `w : ℂ`, the scaled exponential increment
`(n + 1) * (exp (w / (n + 1)) - 1)` converges to `w`. -/
private lemma natSucc_mul_expDiv_sub_one_tendsto_local (w : ℂ) :
    Tendsto
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1))
      atTop
      (𝓝 w) := by
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w‖ ≤
          ‖w‖ ^ (2 : ℕ) / (n + 1 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (Nat.ceil ‖w‖)] with n hn
    have hn0C : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have hn0R : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have hsmallNum : ‖w‖ / (n + 1 : ℝ) ≤ 1 := by
      have hwle : ‖w‖ ≤ (n + 1 : ℝ) := by
        calc
          ‖w‖ ≤ (Nat.ceil ‖w‖ : ℝ) := Nat.le_ceil _
          _ ≤ n := by exact_mod_cast hn
          _ ≤ n + 1 := by linarith
      have hwle' : ‖w‖ ≤ 1 * (n + 1 : ℝ) := by simpa using hwle
      exact (div_le_iff₀ (show (0 : ℝ) < n + 1 by positivity)).2 hwle'
    have hsmall :
        ‖w / ((n + 1 : ℕ) : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_natCast]
      simpa using hsmallNum
    have hrew :
        ((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w =
          ((n + 1 : ℕ) : ℂ) *
            (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1 - w / ((n + 1 : ℕ) : ℂ)) := by
      field_simp [hn0C]
    calc
      ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w‖
          =
        ‖((n + 1 : ℕ) : ℂ) *
            (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1 - w / ((n + 1 : ℕ) : ℂ))‖ := by
              rw [hrew]
      _ ≤ ‖((n + 1 : ℕ) : ℂ)‖ *
            ‖w / ((n + 1 : ℕ) : ℂ)‖ ^ (2 : ℕ) := by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left
                (Complex.norm_exp_sub_one_sub_id_le hsmall) (norm_nonneg _)
      _ = ((n : ℝ) + 1) * (‖w‖ / ((n : ℝ) + 1)) ^ (2 : ℕ) := by
            have hnorm : ‖((n + 1 : ℕ) : ℂ)‖ = (n : ℝ) + 1 := by
              simpa [Nat.cast_add] using Complex.norm_natCast (n + 1)
            rw [norm_div, hnorm]
      _ = ‖w‖ ^ (2 : ℕ) / (n + 1 : ℝ) := by
            field_simp [hn0R]
  have hzero :
      Tendsto (fun n : ℕ ↦ ‖w‖ ^ (2 : ℕ) / (n + 1 : ℝ)) atTop (𝓝 0) := by
    have hdenCast :
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hden :
        Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
      simpa [Nat.cast_add] using hdenCast
    have hinv :
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hden
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ‖w‖ ^ (2 : ℕ)) atTop (𝓝 (‖w‖ ^ (2 : ℕ)))).mul
        hinv
  have hdiff :
      Tendsto
        (fun n : ℕ ↦
          ((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w)
        atTop
        (𝓝 0) := by
    have hnorm :
        Tendsto
          (fun n : ℕ ↦
            ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w‖)
          atTop
          (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
        hbound hzero
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  -- Proof comment: the scaled exponential remainder is `o(1)`, so adding back the fixed limit
  -- `w` yields the desired convergence.
  simpa [sub_eq_add_neg, add_assoc] using
    (hdiff.add (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ w) atTop (𝓝 w)))

/-- Helper for Theorem 16.22: the exact-root compound-Poisson approximant exponents converge
pointwise to the retained logarithmic lift `Ψ`. -/
private lemma compoundPoissonApproxExponent_tendsto_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    ∀ t : ℝ,
      Tendsto
        (fun n : ℕ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) t)
        atTop
        (𝓝 (Ψ t)) := by
  intro t
  refine Tendsto.congr' ?_ (natSucc_mul_expDiv_sub_one_tendsto_local (Ψ t))
  exact Filter.Eventually.of_forall fun n ↦ by
    -- Proof comment: the exact-root approximant exponent is already in the fixed
    -- `exp (Ψ / (n + 1))` normal form.
    simpa [exactRootApproxExponent_eq_expLiftIncrement_local
      (μroot := μroot) (μ := μ) hroot (Ψ := Ψ) hΨ0 hΨexp n t]

/-- Helper for Theorem 16.22: the chosen continuous exponential lift has nonpositive real part,
because it exponentiates to a characteristic function. -/
private lemma continuousExpLift_re_nonpos_local
    {μ : ProbabilityMeasure ℝ} {Ψ : C(ℝ, ℂ)}
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    ∀ t : ℝ, Complex.re (Ψ t) ≤ 0 := by
  intro t
  have hnormExp : Real.exp (Complex.re (Ψ t)) = ‖charFun (μ : Measure ℝ) t‖ := by
    simpa [Complex.norm_exp] using congrArg norm (hΨexp t)
  have hnormLe : Real.exp (Complex.re (Ψ t)) ≤ 1 := by
    rw [hnormExp]
    exact MeasureTheory.norm_charFun_le_one (μ := (μ : Measure ℝ)) t
  exact Real.exp_le_one_iff.mp hnormLe

/-- Helper for Theorem 16.22: evaluating the exact-root auxiliary characteristic function at
frequency `0` reads off the Gaussian-recovery mass integral. -/
private lemma exactRootApproxAuxFiniteMeasure_charFun_zero_eq_integral_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) 0 =
      ((∫ x : ℝ, gaussianRecoveryKernel x ∂(exactRootApproxTriple μroot n).ν : ℝ) : ℂ) := by
  have hcanon :
      IsCanonicalMeasure ((exactRootApproxTriple μroot n).ν) := by
    letI := (exactRootApproxTriple_hasLevyKhinchinRepresentation_local μroot n).isCanonicalTriple
    exact inferInstance
  have hchar :=
    gaussianRecoveryAuxFiniteMeasure_charFun
      (α := 0)
      (ν := (exactRootApproxTriple μroot n).ν)
      (integrable_gaussianRecoveryKernel hcanon)
      0
  -- Proof comment: specialize the Gaussian-smoothing characteristic-function identity at
  -- frequency `0`, where the oscillatory factor is identically `1`.
  calc
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) 0
        =
          (0 : ℂ) +
            ∫ x : ℝ,
              Complex.exp (((0 * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x
                ∂(exactRootApproxTriple μroot n).ν := by
                  simpa [exactRootApproxAuxFiniteMeasure] using hchar
    _ = ∫ x : ℝ, ((gaussianRecoveryKernel x : ℝ) : ℂ) ∂(exactRootApproxTriple μroot n).ν := by
          simp
    _ = ((∫ x : ℝ, gaussianRecoveryKernel x ∂(exactRootApproxTriple μroot n).ν : ℝ) : ℂ) := by
          rw [integral_complex_ofReal]

/-- Helper for Theorem 16.22: the zero-frequency value of the exact-root auxiliary
characteristic function is a nonnegative real mass. -/
private lemma exactRootApproxAuxFiniteMeasure_charFun_zero_re_nonneg_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    0 ≤ Complex.re (charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) :
      Measure ℝ) 0) := by
  -- Proof comment: the auxiliary mass is the integral of the nonnegative Gaussian-recovery
  -- kernel against the finite exact-root Lévy measure.
  rw [exactRootApproxAuxFiniteMeasure_charFun_zero_eq_integral_local]
  simp only [Complex.ofReal_re]
  exact integral_nonneg fun x ↦ gaussianRecoveryKernel_nonneg x

/-- Helper for Theorem 16.22: the exact-root compound-Poisson exponent is already the raw
finite-jump Fourier integral against its punctured intensity. -/
private lemma exactRootApproxExponent_eq_rawKernelIntegral_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    levyKhinchinExponent (exactRootApproxTriple μroot n) t =
      ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1)
        ∂(exactRootApproxTriple μroot n).ν := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  letI : IsFiniteMeasure ν := by
    change IsFiniteMeasure (((exactRootApproxIntensity μroot n : FiniteMeasure ℝ) : Measure ℝ))
    infer_instance
  have hkernel :
      Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ν :=
    integrable_compoundPoissonKernel_of_isFiniteMeasure ν t
  have hcorr :
      Integrable
        (fun x : ℝ ↦ (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ν :=
    integrable_complexCenteringCorrection_of_isFiniteMeasure ν t
  have hsplit :
      ∫ x : ℝ,
          (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂ν =
        ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
          ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν := by
    -- Proof comment: split the exact-root canonical kernel into the raw oscillatory term minus
    -- the canonical centering correction.
    rw [integral_sub hkernel hcorr]
  -- Proof comment: the exact-root triple has `σ² = 0`, and its chosen drift is exactly the
  -- centering integral. Those two pieces cancel, leaving the raw finite-jump Fourier integral.
  calc
    levyKhinchinExponent (exactRootApproxTriple μroot n) t
        =
          ((((∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) * t : ℝ) : ℂ) * Complex.I) +
            ∫ x : ℝ,
              (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
                (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂ν := by
            simp [exactRootApproxTriple, ν, levyKhinchinExponent, levyKhinchinExponentWithCentering,
              mul_comm]
    _ =
          ((((∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) * t : ℝ) : ℂ) * Complex.I) +
            (∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
              ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν) := by
            rw [hsplit]
    _ =
          ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) * Complex.I) +
            (∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
              ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) * Complex.I)) := by
            rw [integral_complexCenteringCorrection_eq]
            congr 1
            ring
    _ = ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν := by
          ring

/-- Helper for Theorem 16.22: each exact-root exponent splits into a sin-centered finite-jump
kernel plus one explicit linear residual term. -/
private lemma exactRootApproxExponent_eq_sinCenteredKernelIntegral_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    levyKhinchinExponent (exactRootApproxTriple μroot n) t =
      ((((t * ∫ x : ℝ, Real.sin x ∂(exactRootApproxTriple μroot n).ν : ℝ) : ℂ)) * Complex.I) +
        ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
          (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ∂(exactRootApproxTriple μroot n).ν := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  letI : IsFiniteMeasure ν := by
    change IsFiniteMeasure (((exactRootApproxIntensity μroot n : FiniteMeasure ℝ) : Measure ℝ))
    infer_instance
  have hkernel :
      Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ν :=
    integrable_compoundPoissonKernel_of_isFiniteMeasure ν t
  have hsin :
      Integrable (fun x : ℝ ↦ (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ν :=
    integrable_complexSinCorrection_of_isFiniteMeasure_local ν t
  have hsplit :
      ∫ x : ℝ,
          (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ∂ν =
        ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
          ∫ x : ℝ, (((t * Real.sin x : ℝ) : ℂ) * Complex.I) ∂ν := by
    -- Proof comment: split the raw exact-root kernel into the sin-centered kernel plus the
    -- bounded linear correction.
    rw [integral_sub hkernel hsin]
  calc
    levyKhinchinExponent (exactRootApproxTriple μroot n) t
        = ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν := by
            simpa [ν] using exactRootApproxExponent_eq_rawKernelIntegral_local μroot n t
    _ =
        ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ∂ν +
          ∫ x : ℝ, (((t * Real.sin x : ℝ) : ℂ) * Complex.I) ∂ν := by
            rw [hsplit]
            ring
    _ =
        ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ∂ν +
          ((((t * ∫ x : ℝ, Real.sin x ∂ν : ℝ) : ℂ)) * Complex.I) := by
            rw [integral_complexSinCorrection_eq_local]
    _ =
        ((((t * ∫ x : ℝ, Real.sin x ∂ν : ℝ) : ℂ)) * Complex.I) +
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ∂ν := by
            ring

/-- Helper for Theorem 16.22: the shifted exact-root exponent is Gaussian-integrable because the
raw finite-jump kernel is uniformly bounded by `2`. -/
private lemma integrable_exactRootApproxExponent_shift_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    Integrable
      (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
      (gaussianReal 0 1) := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  letI : IsFiniteMeasure ν := by
    change IsFiniteMeasure (((exactRootApproxIntensity μroot n : FiniteMeasure ℝ) : Measure ℝ))
    infer_instance
  have hconst :
      Integrable (fun _ : ℝ ↦ ∫ x : ℝ, (2 : ℝ) ∂ν) (gaussianReal 0 1) :=
    integrable_const _
  refine hconst.mono' ?_ ?_
  · -- Proof comment: the shifted exact-root exponent is continuous in the Gaussian variable.
    exact
      ((continuousLevyKhinchinExponentLocal
        (exactRootApproxTriple_hasLevyKhinchinRepresentation_local μroot n).isCanonicalTriple).comp
        (continuous_const.add continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun s ↦ by
      have hkernel :
          Integrable (fun x : ℝ ↦ Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1) ν :=
        integrable_compoundPoissonKernel_of_isFiniteMeasure ν (t + s)
      calc
        ‖levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)‖
            =
              ‖∫ x : ℝ, (Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν‖ := by
                rw [exactRootApproxExponent_eq_rawKernelIntegral_local]
        _ ≤ ∫ x : ℝ, ‖Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1‖ ∂ν := by
              simpa using (norm_integral_le_integral_norm
                (f := fun x : ℝ ↦ Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1))
        _ ≤ ∫ x : ℝ, (2 : ℝ) ∂ν := by
              exact
                integral_mono_ae hkernel.norm (integrable_const (2 : ℝ))
                  (Filter.Eventually.of_forall fun x ↦
                    norm_exp_sub_one_mul_I_le_two_local (t + s) x)

/-- Helper for Theorem 16.22: after truncating the Gaussian average to `[-R, R]`, the remaining
error is exactly the complementary Gaussian tail average of the exact-root exponent. -/
private lemma exactRootApproxAuxSmoothedTail_eq_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (R t : ℝ) :
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t -
        (levyKhinchinExponent (exactRootApproxTriple μroot n) t -
          ∫ s in Set.Icc (-R) R, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1) =
      - ∫ s in (Set.Icc (-R) R)ᶜ,
          levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) ∂gaussianReal 0 1 := by
  let S : Set ℝ := Set.Icc (-R) R
  have hInt := integrable_exactRootApproxExponent_shift_local μroot n t
  -- Proof comment: split the full Gaussian average into its compact part on `[-R, R]` and the
  -- complementary tail contribution.
  calc
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t -
        (levyKhinchinExponent (exactRootApproxTriple μroot n) t -
          ∫ s in Set.Icc (-R) R, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1)
        =
          - (∫ s : ℝ, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
              ∂gaussianReal 0 1 -
            ∫ s in S, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
              ∂gaussianReal 0 1) := by
            rw [exactRootApproxAuxFiniteMeasure_charFun_eq_smoothedExponent_local]
            ring
    _ =
          - ∫ s in Sᶜ, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1 := by
            have hCompl :
                ∫ s : ℝ, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
                    ∂gaussianReal 0 1 -
                    ∫ s in S, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
                      ∂gaussianReal 0 1 =
                  ∫ s in Sᶜ, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
                    ∂gaussianReal 0 1 := by
              have hSmeas : MeasurableSet S := by
                simp [S]
              simpa using
                (MeasureTheory.setIntegral_compl
                  (μ := gaussianReal 0 1)
                  (s := S)
                  (f := fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
                  hSmeas
                  hInt).symm
            rw [hCompl]

/-- Helper for Theorem 16.22: the Gaussian-tail truncation error can already be rewritten as a
tail integral of the raw finite-jump Fourier kernel. -/
private lemma exactRootApproxAuxSmoothedTail_eq_rawKernelTail_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (R t : ℝ) :
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t -
        (levyKhinchinExponent (exactRootApproxTriple μroot n) t -
          ∫ s in Set.Icc (-R) R, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1) =
      - ∫ s in (Set.Icc (-R) R)ᶜ,
          ∫ x : ℝ, (Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1)
            ∂(exactRootApproxTriple μroot n).ν ∂gaussianReal 0 1 := by
  let S : Set ℝ := Set.Icc (-R) R
  -- Proof comment: after the complementary-tail split, rewrite each exponent value by the raw
  -- finite-jump Fourier integral from the exact-root approximant.
  calc
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t -
        (levyKhinchinExponent (exactRootApproxTriple μroot n) t -
          ∫ s in Set.Icc (-R) R, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1)
        =
          - ∫ s in Sᶜ, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1 :=
      exactRootApproxAuxSmoothedTail_eq_local μroot n R t
    _ =
          - ∫ s in Sᶜ,
              ∫ x : ℝ, (Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1)
                ∂(exactRootApproxTriple μroot n).ν ∂gaussianReal 0 1 := by
            change
              - ∫ s : ℝ, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
                  ∂((gaussianReal 0 1).restrict Sᶜ) =
                - ∫ s : ℝ,
                    ∫ x : ℝ, (Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1)
                      ∂(exactRootApproxTriple μroot n).ν ∂((gaussianReal 0 1).restrict Sᶜ)
            congr 1
            refine integral_congr_ae <| Filter.Eventually.of_forall fun s ↦ ?_
            simpa using
              exactRootApproxExponent_eq_rawKernelIntegral_local
                (μroot := μroot) (n := n) (t := t + s)

/-- Helper for Theorem 16.22: on every compact Gaussian truncation window, the exact-root
smoothed exponents converge to the corresponding truncated lift average. -/
private lemma exactRootApproxAuxSmoothedTrunc_tendsto_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (R t : ℝ) :
    Tendsto
      (fun n : ℕ ↦
        levyKhinchinExponent (exactRootApproxTriple μroot n) t -
          ∫ s in Set.Icc (-R) R,
            levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) ∂gaussianReal 0 1)
      atTop
      (𝓝
        (Ψ t - ∫ s in Set.Icc (-R) R, Ψ (t + s) ∂gaussianReal 0 1)) := by
  let S : Set ℝ := Set.Icc (-R) R
  have hUniform :
      ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          ∀ s ∈ S,
            dist (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) (Ψ (t + s)) <
              ε := by
    intro ε hε
    have hInterval :=
      (Metric.tendstoUniformlyOn_iff.1
        (exactRootApproxExponent_tendstoUniformlyOn_interval_local
          μroot hroot hΨ0 hΨexp (t - R) (t + R))) ε hε
    filter_upwards [hInterval] with n hn s hs
    have hts : t + s ∈ Set.Icc (t - R) (t + R) := by
      constructor <;> linarith [hs.1, hs.2]
    simpa [dist_comm] using hn (t + s) hts
  have hIntegrableApprox :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
          S (gaussianReal 0 1) := by
    intro n
    have hcont :
        Continuous (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) := by
      -- Proof comment: the exact-root exponent is continuous, and the truncation window only
      -- shifts the frequency variable by the fixed base point `t`.
      exact
        (continuousLevyKhinchinExponentLocal
          (exactRootApproxTriple_hasLevyKhinchinRepresentation_local μroot n).isCanonicalTriple).comp
          (continuous_const.add continuous_id)
    simpa [S] using hcont.integrableOn_Icc (μ := gaussianReal 0 1) (a := -R) (b := R)
  have hIntegrableLimit :
      IntegrableOn (fun s : ℝ ↦ Ψ (t + s)) S (gaussianReal 0 1) := by
    have hcont : Continuous (fun s : ℝ ↦ Ψ (t + s)) :=
      Ψ.continuous.comp (continuous_const.add continuous_id)
    simpa [S] using hcont.integrableOn_Icc (μ := gaussianReal 0 1) (a := -R) (b := R)
  have hMeasureReal_le_one :
      (gaussianReal 0 1 : Measure ℝ).real S ≤ 1 := by
    have hRealUniv : (gaussianReal 0 1 : Measure ℝ).real Set.univ = 1 := by
      rw [Measure.real_def]
      simp
    calc
      (gaussianReal 0 1 : Measure ℝ).real S ≤ (gaussianReal 0 1 : Measure ℝ).real Set.univ := by
        exact measureReal_mono (Set.subset_univ S)
      _ = 1 := hRealUniv
  have hIntegral :
      Tendsto
        (fun n : ℕ ↦
          ∫ s in S, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1)
        atTop
        (𝓝 (∫ s in S, Ψ (t + s) ∂gaussianReal 0 1)) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    have hHalf : 0 < ε / 2 := by positivity
    filter_upwards [hUniform (ε / 2) hHalf] with n hn
    have hDistEq :
        dist
            (∫ s in S, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
              ∂gaussianReal 0 1)
            (∫ s in S, Ψ (t + s) ∂gaussianReal 0 1) =
          ‖∫ s in S,
              (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) - Ψ (t + s))
              ∂gaussianReal 0 1‖ := by
      -- Proof comment: compare the two set integrals by integrating their pointwise difference on
      -- the fixed truncation window.
      rw [dist_eq_norm, ← integral_sub (hIntegrableApprox n) hIntegrableLimit]
    have hNormLe :
        ‖∫ s in S,
            (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) - Ψ (t + s))
            ∂gaussianReal 0 1‖ ≤
          (ε / 2) * (gaussianReal 0 1 : Measure ℝ).real S := by
      refine norm_setIntegral_le_of_norm_le_const ?_ ?_
      · simpa [S] using measure_lt_top (μ := (gaussianReal 0 1 : Measure ℝ)) S
      · intro s hs
        simpa [dist_eq_norm] using le_of_lt (hn s hs)
    have hHalfMulLt :
        (ε / 2) * (gaussianReal 0 1 : Measure ℝ).real S < ε := by
      have hHalfMulLe : (ε / 2) * (gaussianReal 0 1 : Measure ℝ).real S ≤ ε / 2 := by
        have hεhalf_nonneg : 0 ≤ ε / 2 := by linarith
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left hMeasureReal_le_one hεhalf_nonneg
      have hHalfLt : ε / 2 < ε := by linarith
      exact lt_of_le_of_lt hHalfMulLe hHalfLt
    exact lt_of_le_of_lt (hDistEq ▸ hNormLe) hHalfMulLt
  -- Proof comment: the exact-root exponent at `t` already converges pointwise to `Ψ t`, and the
  -- truncated Gaussian average converges separately on the compact window `[-R,R]`.
  exact
    (compoundPoissonApproxExponent_tendsto_local μroot hroot hΨ0 hΨexp t).sub hIntegral

/-- Helper for Theorem 16.22: the compact-average kernel appearing in the uniqueness and
existence argument. -/
private def compactAverageKernel (x : ℝ) : ℝ :=
  1 - Real.sinc x

/-- Helper for Theorem 16.22: the compact-average kernel is measurable. -/
private lemma measurable_compactAverageKernel :
    Measurable compactAverageKernel := by
  -- Proof comment: the kernel is the difference between the constant function `1` and `sinc`.
  simpa [compactAverageKernel] using measurable_const.sub Real.measurable_sinc

/-- Helper for Theorem 16.22: the compact-average kernel is continuous. -/
private lemma continuous_compactAverageKernel :
    Continuous compactAverageKernel := by
  -- Proof comment: continuity follows immediately from continuity of `Real.sinc`.
  simpa [compactAverageKernel] using continuous_const.sub Real.continuous_sinc

/-- Helper for Theorem 16.22: the compact-average kernel vanishes at the origin. -/
private lemma compactAverageKernel_zero :
    compactAverageKernel 0 = 0 := by
  -- Proof comment: `sinc 0 = 1`, so the compact-average correction disappears at `0`.
  simp [compactAverageKernel]

/-- Helper for Theorem 16.22: the compact-average kernel is nonnegative. -/
private lemma compactAverageKernel_nonneg (x : ℝ) :
    0 ≤ compactAverageKernel x := by
  -- Proof comment: `sinc x ≤ 1` everywhere, so subtracting it from `1` stays nonnegative.
  dsimp [compactAverageKernel]
  linarith [Real.sinc_le_one x]

/-- Helper for Theorem 16.22: away from `0`, the compact-average kernel is strictly positive. -/
private lemma compactAverageKernel_pos_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    0 < compactAverageKernel x := by
  have hxAbs : 0 < |x| := abs_pos.mpr hx
  have hsincAbsLtOne : |Real.sinc x| < 1 := by
    rw [Real.sinc_of_ne_zero hx, abs_div]
    exact (div_lt_iff₀ hxAbs).2 (by simpa using Real.abs_sin_lt_abs hx)
  have hsincLtOne : Real.sinc x < 1 := lt_of_le_of_lt (le_abs_self _) hsincAbsLtOne
  -- Proof comment: strict inequality `|sinc x| < 1` away from `0` upgrades the nonnegative
  -- kernel to a strictly positive one.
  dsimp [compactAverageKernel]
  linarith

/-- Helper for Theorem 16.22: the compact-average kernel is bounded above by `2`. -/
private lemma compactAverageKernel_le_two (x : ℝ) :
    compactAverageKernel x ≤ 2 := by
  -- Proof comment: `sinc x ≥ -1`, so `1 - sinc x` is at most `2`.
  dsimp [compactAverageKernel]
  linarith [Real.neg_one_le_sinc x]

/-- Helper for Theorem 16.22: on the punctured restriction `η.restrict ({0}ᶜ)`, the
compact-average kernel never vanishes. -/
private lemma compactAverageKernel_ae_ne_zero_restrict_compl_singleton
    (η : Measure ℝ) :
    ∀ᵐ x ∂η.restrict ({0}ᶜ : Set ℝ), compactAverageKernel x ≠ 0 := by
  rw [ae_restrict_iff' ((measurableSet_singleton (0 : ℝ)).compl)]
  filter_upwards with x hx
  -- Proof comment: removing the origin removes the only zero of `compactAverageKernel`.
  exact ne_of_gt (compactAverageKernel_pos_of_ne_zero (by simpa using hx))

/-- Helper for Theorem 16.22: the ENNReal compact-average density is finite everywhere. -/
private lemma compactAverageKernel_ae_ne_top {ν : Measure ℝ} :
    ∀ᵐ x ∂ν, (ENNReal.ofReal (compactAverageKernel x)) ≠ ⊤ := by
  -- Proof comment: `ENNReal.ofReal` is finite on every real input.
  filter_upwards with x
  simp

/-- Helper for Theorem 16.22: inverting the compact-average density on the punctured restriction
recovers the original punctured measure. -/
private lemma withDensity_compactAverageKernel_inv_same_restrict_compl_singleton
    (η : Measure ℝ) :
    (((η.restrict ({0}ᶜ : Set ℝ)).withDensity
        (fun x ↦ ENNReal.ofReal (compactAverageKernel x))).withDensity
      (fun x ↦ (ENNReal.ofReal (compactAverageKernel x))⁻¹)) =
      η.restrict ({0}ᶜ : Set ℝ) := by
  let f : ℝ → ENNReal := fun x ↦ ENNReal.ofReal (compactAverageKernel x)
  have hf_meas : Measurable f := measurable_compactAverageKernel.ennreal_ofReal
  have hf_ne_zero :
      ∀ᵐ x ∂η.restrict ({0}ᶜ : Set ℝ), f x ≠ 0 := by
    filter_upwards [compactAverageKernel_ae_ne_zero_restrict_compl_singleton η] with x hx
    have hpos : 0 < compactAverageKernel x :=
      lt_of_le_of_ne (compactAverageKernel_nonneg x) (by simpa [eq_comm] using hx)
    simpa [f, ENNReal.ofReal_eq_zero, not_le_of_gt hpos]
  have hf_ne_top :
      ∀ᵐ x ∂η.restrict ({0}ᶜ : Set ℝ), f x ≠ (⊤ : ENNReal) := by
    simpa [f] using compactAverageKernel_ae_ne_top (ν := η.restrict ({0}ᶜ : Set ℝ))
  -- Proof comment: weighting by the compact-average kernel and then by its inverse cancels on
  -- the punctured restriction where the density never vanishes.
  simpa [f] using MeasureTheory.withDensity_inv_same hf_meas hf_ne_zero hf_ne_top

/-- Helper for Theorem 16.22: recover the punctured jump measure of a compact-average auxiliary
finite measure by inverting the compact-average density away from `0`. -/
private noncomputable def compactAverageRecoveredJumpMeasure_local
    (η : FiniteMeasure ℝ) : Measure ℝ :=
  (((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ)).withDensity
    (fun x ↦ (ENNReal.ofReal (compactAverageKernel x))⁻¹))

/-- Helper for Theorem 16.22: weighting the recovered compact-average jump measure by the kernel
restores the punctured auxiliary measure. -/
private lemma compactAverageRecoveredJumpMeasure_weighted_eq_restrict_compl_local
    (η : FiniteMeasure ℝ) :
    (compactAverageRecoveredJumpMeasure_local η).withDensity
      (fun x ↦ ENNReal.ofReal (compactAverageKernel x)) =
      ((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) := by
  let μ : Measure ℝ := ((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ))
  let f : ℝ → ENNReal := fun x ↦ (ENNReal.ofReal (compactAverageKernel x))⁻¹
  let g : ℝ → ENNReal := fun x ↦ ENNReal.ofReal (compactAverageKernel x)
  have hf : Measurable f := measurable_compactAverageKernel.ennreal_ofReal.inv
  have hg : Measurable g := measurable_compactAverageKernel.ennreal_ofReal
  have hfg :
      f * g =ᵐ[μ] 1 := by
    filter_upwards [compactAverageKernel_ae_ne_zero_restrict_compl_singleton (η : Measure ℝ),
      compactAverageKernel_ae_ne_top (ν := μ)] with x hx0 hxtop
    have hpos : 0 < compactAverageKernel x :=
      lt_of_le_of_ne (compactAverageKernel_nonneg x) (by simpa [eq_comm] using hx0)
    have hx0' : ENNReal.ofReal (compactAverageKernel x) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le_of_gt hpos]
    change
      ((ENNReal.ofReal (compactAverageKernel x))⁻¹ *
        ENNReal.ofReal (compactAverageKernel x) = 1)
    exact ENNReal.inv_mul_cancel hx0' hxtop
  -- Proof comment: on `{0}ᶜ`, the compact-average kernel is strictly positive and finite, so
  -- applying `withDensity` by the inverse density and then by the original density is the identity.
  calc
    (compactAverageRecoveredJumpMeasure_local η).withDensity
        (fun x ↦ ENNReal.ofReal (compactAverageKernel x))
        = (μ.withDensity f).withDensity g := by
            rfl
    _ = μ.withDensity (f * g) := by
          symm
          exact MeasureTheory.withDensity_mul (μ := μ) hf hg
    _ = μ.withDensity 1 := by
          exact MeasureTheory.withDensity_congr_ae hfg
    _ = μ := by
          rw [MeasureTheory.withDensity_one]

/-- Helper for Theorem 16.22: the compact-average auxiliary finite measure splits into its atom
at `0` and the weighted punctured recovered jump measure. -/
private lemma compactAverageRecoveredJumpMeasure_decomposition_local
    (η : FiniteMeasure ℝ) :
    (η : Measure ℝ) =
      ((η : Measure ℝ) ({0} : Set ℝ)) • Measure.dirac 0 +
        (compactAverageRecoveredJumpMeasure_local η).withDensity
          (fun x ↦ ENNReal.ofReal (compactAverageKernel x)) := by
  -- Proof comment: split `η` into its singleton and punctured restrictions, then rewrite the
  -- punctured part through the recovered compact-average jump measure.
  calc
    (η : Measure ℝ)
        = ((η : Measure ℝ).restrict ({0} : Set ℝ)) +
            ((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) := by
              symm
              simpa using
                (Measure.restrict_add_restrict_compl
                  (μ := (η : Measure ℝ)) (measurableSet_singleton (0 : ℝ)))
    _ = ((η : Measure ℝ) ({0} : Set ℝ)) • Measure.dirac 0 +
          ((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) := by
            rw [Measure.restrict_singleton]
    _ = ((η : Measure ℝ) ({0} : Set ℝ)) • Measure.dirac 0 +
          (compactAverageRecoveredJumpMeasure_local η).withDensity
            (fun x ↦ ENNReal.ofReal (compactAverageKernel x)) := by
            rw [compactAverageRecoveredJumpMeasure_weighted_eq_restrict_compl_local]
/-- Helper for Theorem 16.22: the compact-average correction of a continuous lift is again
continuous. -/
private lemma continuous_compactAverageExpLift_local
    (Ψ : C(ℝ, ℂ)) :
    Continuous fun t : ℝ ↦
      Ψ t - ((1 / 2 : ℂ) * ∫ s in (-1 : ℝ)..1, Ψ (t + s)) := by
  have hIntegral :
      Continuous fun t : ℝ ↦ ∫ s in (-1 : ℝ)..1, Ψ (t + s) := by
    -- Proof comment: the integrand `(t,s) ↦ Ψ (t + s)` is jointly continuous, so the compact
    -- interval integral depends continuously on the parameter `t`.
    have hUncurry : Continuous (Function.uncurry fun t s : ℝ ↦ Ψ (t + s)) := by
      simpa [Function.uncurry] using Ψ.continuous.comp (continuous_fst.add continuous_snd)
    simpa [Function.uncurry] using
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume) (f := fun t s : ℝ ↦ Ψ (t + s)) hUncurry (-1 : ℝ) 1)
  -- Proof comment: subtract the continuous compact-average correction from the original lift.
  simpa using Ψ.continuous.sub (hIntegral.const_mul (1 / 2 : ℂ))

/-- Helper for Theorem 16.22: compact averaging preserves continuity of the retained logarithmic
lift. -/
private noncomputable def compactAverageExpLift (Ψ : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t : ℝ ↦ Ψ t - ((1 / 2 : ℂ) * ∫ s in (-1 : ℝ)..1, Ψ (t + s)),
    continuous_compactAverageExpLift_local Ψ⟩

/-- Helper for Theorem 16.22: compact averaging commutes with the exact-root exponent limit on
every fixed frequency. -/
private lemma exactRootApproxCompactAverageExponent_tendsto_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    ∀ t : ℝ,
      Tendsto
        (fun n : ℕ ↦
          levyKhinchinExponent (exactRootApproxTriple μroot n) t -
            ((1 / 2 : ℂ) *
              ∫ s in (-1 : ℝ)..1, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)))
        atTop
        (𝓝 ((compactAverageExpLift Ψ) t)) := by
  intro t
  have hUniform :
      ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          ∀ s ∈ Set.Icc (-1 : ℝ) 1,
            dist (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) (Ψ (t + s)) <
              ε := by
    intro ε hε
    have hInterval :=
      (Metric.tendstoUniformlyOn_iff.1
        (exactRootApproxExponent_tendstoUniformlyOn_interval_local
          μroot hroot hΨ0 hΨexp (t - 1) (t + 1))) ε hε
    filter_upwards [hInterval] with n hn s hs
    have hts : t + s ∈ Set.Icc (t - 1) (t + 1) := by
      constructor <;> linarith [hs.1, hs.2]
    simpa [dist_comm] using hn (t + s) hts
  have hIntegrableApprox :
      ∀ n : ℕ,
        IntervalIntegrable
          (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
          volume (-1) 1 := by
    intro n
    have hcont :
        Continuous (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) := by
      -- Proof comment: the exact-root exponent is continuous, and the compact-average window
      -- only shifts the frequency variable by the fixed base point `t`.
      exact
        (continuousLevyKhinchinExponentLocal
          (exactRootApproxTriple_hasLevyKhinchinRepresentation_local μroot n).isCanonicalTriple).comp
          (continuous_const.add continuous_id)
    exact hcont.intervalIntegrable (-1) 1
  have hIntegrableLimit :
      IntervalIntegrable (fun s : ℝ ↦ Ψ (t + s)) volume (-1) 1 := by
    have hcont : Continuous (fun s : ℝ ↦ Ψ (t + s)) :=
      Ψ.continuous.comp (continuous_const.add continuous_id)
    exact hcont.intervalIntegrable (-1) 1
  have hIntegral :
      Tendsto
        (fun n : ℕ ↦
          ∫ s in (-1 : ℝ)..1, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
        atTop
        (𝓝 (∫ s in (-1 : ℝ)..1, Ψ (t + s))) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    have hQuarter : 0 < ε / 4 := by positivity
    filter_upwards [hUniform (ε / 4) hQuarter] with n hn
    have hDistEq :
        dist
            (∫ s in (-1 : ℝ)..1,
              levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
            (∫ s in (-1 : ℝ)..1, Ψ (t + s)) =
          ‖∫ s in (-1 : ℝ)..1,
              (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) - Ψ (t + s))‖ := by
      -- Proof comment: compare the two interval integrals by integrating the pointwise
      -- difference on the fixed window `[-1, 1]`.
      rw [dist_eq_norm, ← intervalIntegral.integral_sub (hIntegrableApprox n) hIntegrableLimit]
    have hNormLe :
        ‖∫ s in (-1 : ℝ)..1,
            (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) - Ψ (t + s))‖ ≤
          (ε / 4) * |(1 : ℝ) - (-1 : ℝ)| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro s hs
      have hsIoc : s ∈ Set.Ioc (-1 : ℝ) 1 := by
        simpa [Set.uIoc, min_eq_left (show (-1 : ℝ) ≤ 1 by norm_num),
          max_eq_right (show (-1 : ℝ) ≤ 1 by norm_num)] using hs
      have hs' : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hsIoc.1, hsIoc.2⟩
      simpa [dist_eq_norm] using le_of_lt (hn s hs')
    have hQuarterMulLt : (ε / 4) * |(1 : ℝ) - (-1 : ℝ)| < ε := by
      norm_num
      linarith
    exact lt_of_le_of_lt (hDistEq ▸ hNormLe) hQuarterMulLt
  have hScaledIntegral :
      Tendsto
        (fun n : ℕ ↦
          ((1 / 2 : ℂ)) *
            ∫ s in (-1 : ℝ)..1, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
        atTop
        (𝓝 (((1 / 2 : ℂ)) * ∫ s in (-1 : ℝ)..1, Ψ (t + s))) := by
    exact
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 / 2 : ℂ)) atTop (𝓝 (1 / 2 : ℂ))).mul
        hIntegral
  -- Proof comment: the exact-root exponent already converges pointwise to `Ψ t`, and the
  -- compact-average correction converges separately on the fixed interval `[-1, 1]`.
  simpa [compactAverageExpLift] using
    (compoundPoissonApproxExponent_tendsto_local μroot hroot hΨ0 hΨexp t).sub hScaledIntegral

/-- Helper for Theorem 16.22: on the non-Dirac branch, compact averaging leaves strictly positive
mass at the origin. -/
private lemma compactAverageLiftZero_pos_of_notDirac_local
    {μ : ProbabilityMeasure ℝ} {Ψ : C(ℝ, ℂ)}
    (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (hDirac : ¬ ∃ b : ℝ, μ = diracProba b) :
    0 < Complex.re ((compactAverageExpLift Ψ) 0) := by
  let f : ℝ → ℝ := fun s ↦ -Complex.re (Ψ s)
  have hReNonpos : ∀ s : ℝ, Complex.re (Ψ s) ≤ 0 :=
    continuousExpLift_re_nonpos_local hΨexp
  have hfNonneg : ∀ s : ℝ, 0 ≤ f s := by
    intro s
    dsimp [f]
    linarith [hReNonpos s]
  have hfCont : Continuous f := by
    -- Proof comment: `f` is the negative real part of the continuous logarithmic lift.
    simpa [f] using (Complex.continuous_re.comp Ψ.continuous).neg
  have hΨInt : IntervalIntegrable (fun s : ℝ ↦ Ψ s) volume (-1) 1 :=
    Ψ.continuous.intervalIntegrable (-1) 1
  have hfInt : IntervalIntegrable f volume (-1) 1 :=
    hfCont.intervalIntegrable (-1) 1
  have hReFormula :
      Complex.re ((compactAverageExpLift Ψ) 0) =
        (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, f s := by
    -- Proof comment: at `0`, compact averaging is exactly half the interval integral of
    -- `-Re (Ψ s)` because the lift is normalized by `Ψ 0 = 0`.
    have hReFormulaSet :
        Complex.re ((compactAverageExpLift Ψ) 0) =
          (1 / 2 : ℝ) * ∫ s in Set.Ioc (-1 : ℝ) 1, f s := by
      have hReInt :
          (∫ s in Set.Ioc (-1 : ℝ) 1, Ψ s).re =
            ∫ s in Set.Ioc (-1 : ℝ) 1, Complex.re (Ψ s) := by
        simpa using (integral_re hΨInt.1).symm
      rw [compactAverageExpLift]
      simp only [ContinuousMap.coe_mk]
      rw [hΨ0]
      simp only [zero_sub, Complex.neg_re, Complex.mul_re]
      have hZeroShift :
          (∫ x in Set.Ioc (-1 : ℝ) 1, Ψ (0 + x)) = ∫ x in Set.Ioc (-1 : ℝ) 1, Ψ x := by
        simp [zero_add]
      rw [intervalIntegral.integral_of_le (by norm_num), hZeroShift, hReInt]
      simp [f]
      rw [integral_neg]
      ring
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact hReFormulaSet
  have hReNonneg : 0 ≤ Complex.re ((compactAverageExpLift Ψ) 0) := by
    rw [hReFormula]
    refine mul_nonneg (by norm_num) ?_
    exact intervalIntegral.integral_nonneg (by norm_num) fun s _ ↦ hfNonneg s
  by_contra hNotPos
  have hReZero : Complex.re ((compactAverageExpLift Ψ) 0) = 0 := by
    linarith
  have hIntZero : ∫ s in (-1 : ℝ)..1, f s = 0 := by
    rw [hReFormula] at hReZero
    linarith
  have hfZeroOnIoo : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, f s = 0 := by
    intro s hs
    by_contra hsNe
    have hsPos : 0 < f s := lt_of_le_of_ne (hfNonneg s) (Ne.symm hsNe)
    have hsCont : ContinuousAt f s := hfCont.continuousAt
    have hsHalfPos : 0 < f s / 2 := by positivity
    rcases Metric.continuousAt_iff.mp hsCont (f s / 2) hsHalfPos with ⟨δ, hδPos, hδ⟩
    let r : ℝ := min (δ / 2) (min ((s + 1) / 2) ((1 - s) / 2))
    have hrPos : 0 < r := by
      dsimp [r]
      have hsLeftPos : 0 < (s + 1) / 2 := by linarith [hs.1]
      have hsRightPos : 0 < (1 - s) / 2 := by linarith [hs.2]
      refine lt_min ?_ (lt_min hsLeftPos hsRightPos)
      linarith
    have hrLeDelta : r ≤ δ := by
      dsimp [r]
      have hMin : min (δ / 2) (min ((s + 1) / 2) ((1 - s) / 2)) ≤ δ / 2 := min_le_left _ _
      linarith
    have hrLeLeft : r ≤ (s + 1) / 2 := by
      dsimp [r]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hrLeRight : r ≤ (1 - s) / 2 := by
      dsimp [r]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hPosOnSmall : ∀ y ∈ Set.Ioo (s - r) (s + r), 0 < f y := by
      intro y hy
      have hyAbs : |y - s| < r := by
        refine abs_lt.mpr ?_
        constructor <;> linarith [hy.1, hy.2]
      have hyDist : dist y s < δ := by
        simpa [Real.dist_eq, abs_sub_comm] using lt_of_lt_of_le hyAbs hrLeDelta
      have hyClose : |f y - f s| < f s / 2 := by
        simpa [Real.dist_eq] using hδ hyDist
      rcases abs_lt.mp hyClose with ⟨hyLeft, _hyRight⟩
      have hyLower : f s / 2 < f y := by
        linarith
      exact lt_trans hsHalfPos hyLower
    have hSupportSubset :
        Set.Ioo (s - r) (s + r) ⊆ Function.support f ∩ Set.Ioc (-1 : ℝ) 1 := by
      intro y hy
      refine ⟨Function.mem_support.2 (hPosOnSmall y hy).ne', ?_⟩
      constructor
      · linarith [hy.1, hrLeLeft]
      · linarith [hy.2, hrLeRight]
    have hSupportPos : 0 < volume (Function.support f ∩ Set.Ioc (-1 : ℝ) 1) := by
      have hSmallPos : 0 < volume (Set.Ioo (s - r) (s + r)) := by
        rw [Real.volume_Ioo, ENNReal.ofReal_pos]
        linarith
      exact lt_of_lt_of_le hSmallPos (measure_mono hSupportSubset)
    have hIntegralPos : 0 < ∫ x in (-1 : ℝ)..1, f x := by
      rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall hfNonneg) hfInt]
      exact ⟨by norm_num, hSupportPos⟩
    exact hIntegralPos.ne' hIntZero
  let t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 2)
  have htAntitone : Antitone fun k ↦ |t k| := by
    intro m n hmn
    -- Proof comment: the reciprocal sequence `1 / (k + 2)` is decreasing and positive.
    simp only [t]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have hRecip :
        1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / (((m + 1 : ℕ) : ℝ) + 1) :=
      Nat.one_div_le_one_div (Nat.succ_le_succ hmn)
    convert hRecip using 1 <;> norm_num [Nat.cast_add, add_assoc]
  have htZero : Tendsto (fun k ↦ |t k|) atTop (𝓝 0) := by
    -- Proof comment: the reciprocal sequence tends to `0` because its denominator tends to
    -- `+∞`.
    have habs : (fun k ↦ |t k|) = fun k : ℕ ↦ (((k : ℝ) + 2) : ℝ)⁻¹ := by
      funext k
      have hk : 0 ≤ (k : ℝ) + 2 := by positivity
      simp [t, abs_of_nonneg (inv_nonneg.mpr hk)]
    rw [habs]
    have hDen : Tendsto (fun k : ℕ ↦ (k : ℝ) + 2) atTop atTop := by
      simpa using tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hDen
  have htNonzero : ∀ k, t k ≠ 0 := by
    intro k
    have hk : ((k : ℝ) + 2) ≠ 0 := by positivity
    simp [t, hk]
  have hCharUnit : ∀ k, ‖charFun (μ : Measure ℝ) (t k)‖ = 1 := by
    intro k
    have htkPos : 0 < t k := by
      dsimp [t]
      positivity
    have htkLtOne : t k < 1 := by
      dsimp [t]
      have hkPos : 0 < (k : ℝ) + 1 := by positivity
      have hk : 1 < (k : ℝ) + 2 := by linarith
      simpa [one_div] using inv_lt_one_of_one_lt₀ hk
    have htkMem : t k ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor
      · linarith
      · exact htkLtOne
    have hNegReZero : -Complex.re (Ψ (t k)) = 0 := by
      simpa [f] using hfZeroOnIoo (t k) htkMem
    have hReZero : Complex.re (Ψ (t k)) = 0 := by
      linarith
    have hNormExp : ‖Complex.exp (Ψ (t k))‖ = 1 := by
      simpa [Complex.norm_exp, hReZero]
    simpa [hΨexp (t k)] using hNormExp
  obtain ⟨b, hbMeasure⟩ :=
    Measure.eq_dirac_of_charFun_norm_eq_one_along_zero
      (μ := (μ : Measure ℝ)) htAntitone htZero htNonzero hCharUnit
  apply hDirac
  refine ⟨b, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  simpa [MeasureTheory.diracProba] using hbMeasure


local notation "E1" => EuclideanSpace ℝ (Fin 1)

/-- Helper for Theorem 16.22: read the unique coordinate of `ℝ¹` measurably. -/
private lemma measurable_euclidean1ToReal_local :
    Measurable (euclidean1ToReal : E1 → ℝ) := by
  -- Proof comment: `euclidean1ToReal` is evaluation at the sole coordinate of `ℝ¹`.
  simpa [euclidean1ToReal] using
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 1 ↦ ℝ) (0 : Fin 1)).measurable

/-- Helper for Theorem 16.22: continuity at `0` on `ℝ` gives the one-dimensional
`PartiallyContinuousAtZero` condition after transport to `ℝ¹`. -/
private lemma partiallyContinuousAtZero_comp_euclidean1ToReal_local
    {φ : ℝ → ℂ} (hφ0 : ContinuousAt φ 0) :
    PartiallyContinuousAtZero (d := 1) (fun x : E1 ↦ φ (euclidean1ToReal x)) := by
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  -- Proof comment: in dimension one the unique coordinate axis is exactly the original real
  -- line.
  simpa [euclidean1ToReal, realToEuclidean1] using hφ0

/-- Helper for Theorem 16.22: mapping a one-dimensional Euclidean law back to `ℝ` recovers the
real characteristic function by evaluating at `realToEuclidean1`. -/
private lemma charFun_map_euclidean1ToReal_local
    (μ : ProbabilityMeasure E1) (t : ℝ) :
    charFun
      (μ.map measurable_euclidean1ToReal_local.aemeasurable : Measure ℝ) t =
      charFun (μ : Measure E1) (realToEuclidean1 t) := by
  -- Proof comment: rewrite the pushforward characteristic function via `integral_map`, then
  -- identify the one-dimensional inner product with scalar multiplication by `t`.
  change
    charFun (Measure.map euclidean1ToReal (μ : Measure E1)) t =
      charFun (μ : Measure E1) (realToEuclidean1 t)
  rw [MeasureTheory.charFun_apply_real, MeasureTheory.charFun_apply,
    MeasureTheory.integral_map measurable_euclidean1ToReal_local.aemeasurable (by fun_prop)]
  congr with x
  congr 1
  have hinner :
      inner ℝ x (realToEuclidean1 t) = t * euclidean1ToReal x := by
    simpa [euclidean1ToReal, realToEuclidean1] using
      (EuclideanSpace.inner_single_right (i := (0 : Fin 1)) t x)
  exact congrArg (fun z : ℂ ↦ z * Complex.I) (by exact_mod_cast hinner.symm)

/-- Helper for Theorem 16.22: normalizing a nonzero finite measure scales its characteristic
function by the reciprocal total mass. -/
private lemma charFun_normalize_eq_invMass_local
    (η : FiniteMeasure ℝ) (hη : η ≠ 0) (t : ℝ) :
    charFun (η.normalize : Measure ℝ) t =
      (((η.mass⁻¹ : NNReal) : ℂ)) * charFun ((η : FiniteMeasure ℝ) : Measure ℝ) t := by
  -- Proof comment: rewrite the normalized measure as the reciprocal-mass scalar multiple of the
  -- original finite measure and then move the scalar through the characteristic-function integral.
  rw [η.toMeasure_normalize_eq_of_nonzero hη, MeasureTheory.charFun_apply_real,
    MeasureTheory.charFun_apply_real]
  have hIntegral :
      ∫ x : ℝ, Complex.exp (((t : ℂ) * x) * Complex.I) ∂((η.mass⁻¹ : NNReal) • (η : Measure ℝ)) =
        (η.mass⁻¹ : NNReal) • ∫ x : ℝ, Complex.exp (((t : ℂ) * x) * Complex.I) ∂(η : Measure ℝ) := by
    simpa using
      (integral_smul_measure
        (μ := ((η : FiniteMeasure ℝ) : Measure ℝ))
        (c := ((η.mass⁻¹ : NNReal) : ENNReal))
        (f := fun x : ℝ ↦ Complex.exp (((t : ℂ) * x) * Complex.I)))
  rw [hIntegral]
  change
    (((η.mass⁻¹ : NNReal) : ℂ) * ∫ x : ℝ, Complex.exp (((t : ℂ) * x) * Complex.I) ∂(η : Measure ℝ)) =
      (((η.mass⁻¹ : NNReal) : ℂ) * ∫ x : ℝ, Complex.exp (((t : ℂ) * x) * Complex.I) ∂(η : Measure ℝ))
  rfl

/-- Helper for Theorem 16.22: scaling a probability law by a finite mass scales its
characteristic function by the same complex scalar. -/
private lemma charFun_mass_smul_probability_local
    (m : NNReal) (ρ : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (((m • ρ.toFiniteMeasure : FiniteMeasure ℝ) : Measure ℝ)) t =
      (m : ℂ) * charFun (ρ : Measure ℝ) t := by
  -- Proof comment: identify the scaled finite measure with the scalar multiple of the underlying
  -- probability measure and then move the scalar through the Fourier integral.
  rw [MeasureTheory.charFun_apply_real]
  simpa [FiniteMeasure.toMeasure_smul, Algebra.smul_def, MeasureTheory.charFun_apply_real] using
    (integral_smul_measure
      (μ := ((ρ.toFiniteMeasure : FiniteMeasure ℝ) : Measure ℝ))
      (c := m)
      (f := fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)))

/-- Helper for Theorem 16.22: the characteristic function of a finite measure at `0` is its total
mass. -/
private lemma charFun_finiteMeasure_zero_eq_mass_local (η : FiniteMeasure ℝ) :
    charFun ((η : FiniteMeasure ℝ) : Measure ℝ) 0 = (η.mass : ℂ) := by
  -- Proof comment: `charFun μ 0` is the total mass of `μ`, and for a finite measure that mass is
  -- exactly `η.mass`.
  rw [MeasureTheory.charFun_zero, Measure.real_def]
  change ((((η : Measure ℝ) Set.univ).toReal : ℂ) =
    ((((η : Measure ℝ) Set.univ).toNNReal : ℝ≥0) : ℂ))
  simp [ENNReal.coe_toNNReal_eq_toReal]

/-- Helper for Theorem 16.22: extract the scalar factor and swap the compact-average Fourier
integrals in the exact `(s, x)` spelling used downstream. -/
private lemma shiftedFourierCompactAverageBridge_local
    {ν : Measure ℝ} [IsFiniteMeasure ν] (t : ℝ)
    (hShiftProdIntegrable :
      Integrable
        (Function.uncurry fun s x : ℝ ↦
          Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)))
        ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν)) :
    ∫ x : ℝ,
        ((1 / 2 : ℂ) *
          ∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) ∂ν =
      ((1 / 2 : ℂ) *
        ∫ s in (-1 : ℝ)..1,
          ∫ x : ℝ, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) ∂ν) := by
  -- Proof comment: first pull the constant `1 / 2` through the outer integral, then apply
  -- Fubini in the exact binder spelling consumed by the compact-average characteristic-function
  -- identity.
  let f : ℝ → ℝ → ℂ :=
    fun s x : ℝ ↦ Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))
  let g : ℝ → ℂ := fun x : ℝ ↦ ∫ s in (-1 : ℝ)..1, f s x
  have hShiftProdIntegrable' :
      Integrable (Function.uncurry f) ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν) := by
    simpa [f] using hShiftProdIntegrable
  calc
    ∫ x : ℝ,
        ((1 / 2 : ℂ) *
          ∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) ∂ν =
      ∫ x : ℝ, ((1 / 2 : ℂ) * g x) ∂ν := by
        simp [g, f]
    _ =
        ((1 / 2 : ℂ) * ∫ x : ℝ, g x ∂ν) := by
          simpa using (integral_const_mul (μ := ν) (1 / 2 : ℂ) g)
    _ =
        ((1 / 2 : ℂ) * ∫ s in (-1 : ℝ)..1, ∫ x : ℝ, f s x ∂ν) := by
          congr 1
          simpa [g] using
            (intervalIntegral_integral_swap
              (μ := ν)
              (a := (-1 : ℝ))
              (b := (1 : ℝ))
              (f := f)
              hShiftProdIntegrable').symm
    _ =
        ((1 / 2 : ℂ) *
          ∫ s in (-1 : ℝ)..1,
            ∫ x : ℝ, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) ∂ν) := by
          simp [f]

/-- Helper for Theorem 16.22: when finite measures converge after normalization, keep both the
limiting probability law and the reconstructed finite measure in one package. -/
private lemma exists_auxFiniteMeasure_with_normalizedLimit_of_tendsto_charFun_local
    {ηs : ℕ → FiniteMeasure ℝ} {Φ : ℝ → ℂ} {m : NNReal}
    (hmass : Tendsto (fun n : ℕ ↦ (ηs n).mass) atTop (𝓝 m))
    (hm : m ≠ 0)
    (hchar : ∀ t : ℝ,
      Tendsto (fun n : ℕ ↦ charFun ((ηs n : FiniteMeasure ℝ) : Measure ℝ) t) atTop
        (𝓝 (Φ t)))
    (hcont : ContinuousAt (fun t : ℝ ↦ (((m⁻¹ : NNReal) : ℂ)) * Φ t) 0) :
    ∃ ρ : ProbabilityMeasure ℝ, ∃ η : FiniteMeasure ℝ,
      η = m • ρ.toFiniteMeasure ∧
      (∀ t : ℝ, charFun ((η : FiniteMeasure ℝ) : Measure ℝ) t = Φ t) ∧
      Tendsto (fun n : ℕ ↦ (ηs n).normalize) atTop (𝓝 ρ) := by
  let Ps : ℕ → ProbabilityMeasure E1 := fun n ↦ pushRealToEuclidean1 ((ηs n).normalize)
  have hmassInv :
      Tendsto (fun n : ℕ ↦ (ηs n).mass⁻¹) atTop (𝓝 m⁻¹) :=
    Tendsto.inv₀ hmass hm
  have hmassInvC :
      Tendsto (fun n : ℕ ↦ (((ηs n).mass⁻¹ : NNReal) : ℂ)) atTop
        (𝓝 (((m⁻¹ : NNReal) : ℂ))) := by
    exact
      (Complex.continuous_ofReal.continuousAt.tendsto.comp <|
        (NNReal.continuous_coe.continuousAt.tendsto.comp hmassInv))
  have hηne :
      ∀ᶠ n : ℕ in atTop, ηs n ≠ 0 := by
    filter_upwards [hmass (Ioi_mem_nhds (show (0 : NNReal) < m by
      exact pos_iff_ne_zero.mpr hm))] with n hn
    exact fun hzero ↦ by
      simpa [hzero] using hn
  have hcharE1 :
      ∀ x : E1,
        Tendsto (fun n ↦ charFun (Ps n : Measure E1) x) atTop
          (𝓝 ((((m⁻¹ : NNReal) : ℂ)) * Φ (euclidean1ToReal x))) := by
    intro x
    have hnormEq :
        ∀ᶠ n : ℕ in atTop,
          charFun (Ps n : Measure E1) x =
            (((((ηs n).mass)⁻¹ : NNReal) : ℂ)) *
              charFun ((ηs n : FiniteMeasure ℝ) : Measure ℝ) (euclidean1ToReal x) := by
      filter_upwards [hηne] with n hn
      rw [show Ps n = pushRealToEuclidean1 ((ηs n).normalize) by rfl]
      rw [charFun_map_realToEuclidean1]
      simpa using charFun_normalize_eq_invMass_local (ηs n) hn (euclidean1ToReal x)
    refine (hmassInvC.mul (hchar (euclidean1ToReal x))).congr' ?_
    filter_upwards [hnormEq] with n hn
    exact hn.symm
  have hφ0 :
      PartiallyContinuousAtZero (d := 1)
        (fun x : E1 ↦ (((m⁻¹ : NNReal) : ℂ)) * Φ (euclidean1ToReal x)) := by
    exact partiallyContinuousAtZero_comp_euclidean1ToReal_local hcont
  rcases exists_probabilityMeasure_of_tendsto_charFun (d := 1) Ps hcharE1 hφ0 with
    ⟨ρE1, hρE1char, _hPsTendsto⟩
  let ρ : ProbabilityMeasure ℝ := ρE1.map measurable_euclidean1ToReal_local.aemeasurable
  have hρchar :
      ∀ t : ℝ, charFun (ρ : Measure ℝ) t = (((m⁻¹ : NNReal) : ℂ)) * Φ t := by
    intro t
    rw [charFun_map_euclidean1ToReal_local]
    simpa [realToEuclidean1, euclidean1ToReal] using hρE1char (realToEuclidean1 t)
  have hnormChar :
      ∀ t : ℝ,
        Tendsto (fun n : ℕ ↦ charFun ((ηs n).normalize : Measure ℝ) t) atTop
          (𝓝 (charFun (ρ : Measure ℝ) t)) := by
    intro t
    have hnormEq :
        ∀ᶠ n : ℕ in atTop,
          charFun ((ηs n).normalize : Measure ℝ) t =
            (((((ηs n).mass)⁻¹ : NNReal) : ℂ)) *
              charFun ((ηs n : FiniteMeasure ℝ) : Measure ℝ) t := by
      filter_upwards [hηne] with n hn
      exact charFun_normalize_eq_invMass_local (ηs n) hn t
    have hnormScaled :
        Tendsto
          (fun n : ℕ ↦ charFun ((ηs n).normalize : Measure ℝ) t)
          atTop
          (𝓝 ((((m⁻¹ : NNReal) : ℂ)) * Φ t)) := by
      refine (hmassInvC.mul (hchar t)).congr' ?_
      filter_upwards [hnormEq] with n hn
      exact hn.symm
    simpa [hρchar t] using hnormScaled
  have hnormTendsto :
      Tendsto (fun n : ℕ ↦ (ηs n).normalize) atTop (𝓝 ρ) := by
    exact ProbabilityMeasure.tendsto_of_tendsto_charFun hnormChar
  let η : FiniteMeasure ℝ := m • ρ.toFiniteMeasure
  refine ⟨ρ, η, rfl, ?_, hnormTendsto⟩
  intro t
  rw [charFun_mass_smul_probability_local]
  rw [hρchar]
  simp [hm]

/-- Helper for Theorem 16.22: once the auxiliary finite measures have convergent masses and their
normalized characteristic functions satisfy Lévy's continuity theorem, they assemble into one
limiting finite measure realizing the target auxiliary characteristic function. -/
private lemma exists_auxFiniteMeasure_of_tendsto_charFun_local
    {ηs : ℕ → FiniteMeasure ℝ} {Φ : ℝ → ℂ} {m : NNReal}
    (hmass : Tendsto (fun n : ℕ ↦ (ηs n).mass) atTop (𝓝 m))
    (hm : m ≠ 0)
    (hchar : ∀ t : ℝ,
      Tendsto (fun n : ℕ ↦ charFun ((ηs n : FiniteMeasure ℝ) : Measure ℝ) t) atTop
        (𝓝 (Φ t)))
    (hcont : ContinuousAt (fun t : ℝ ↦ (((m⁻¹ : NNReal) : ℂ)) * Φ t) 0) :
    ∃ η : FiniteMeasure ℝ, ∀ t : ℝ, charFun ((η : FiniteMeasure ℝ) : Measure ℝ) t = Φ t := by
  obtain ⟨ρ, η, _hηeq, hηchar, _hnormTendsto⟩ :=
    exists_auxFiniteMeasure_with_normalizedLimit_of_tendsto_charFun_local
      hmass hm hchar hcont
  exact ⟨η, hηchar⟩

/-- Helper for Theorem 16.22: the compact-average kernel is integrable against every finite
measure because it is bounded by `2`. -/
private lemma integrable_compactAverageKernel_of_isFiniteMeasure_local
    (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable compactAverageKernel ν := by
  -- Proof comment: the compact-average kernel is measurable and uniformly bounded by `2`.
  refine (integrable_const (2 : ℝ)).mono' measurable_compactAverageKernel.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    have hnonneg : 0 ≤ compactAverageKernel x := compactAverageKernel_nonneg x
    rw [Real.norm_of_nonneg hnonneg]
    exact compactAverageKernel_le_two x

/-- Helper for Theorem 16.22: the compact-average weighted exact-root jump measure is finite. -/
private theorem exactRootApproxCompactAverageMeasure_isFinite
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    IsFiniteMeasure
      ((exactRootApproxTriple μroot n).ν.withDensity
        (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  letI : IsFiniteMeasure ν := by
    change IsFiniteMeasure (((exactRootApproxIntensity μroot n : FiniteMeasure ℝ) : Measure ℝ))
    infer_instance
  -- Proof comment: bounded compact-average weighting preserves finiteness of the exact-root
  -- jump intensity.
  simpa [ν] using
    (MeasureTheory.isFiniteMeasure_withDensity_ofReal
      (μ := ν)
      (integrable_compactAverageKernel_of_isFiniteMeasure_local ν).hasFiniteIntegral)

/-- Helper for Theorem 16.22: the compact-average weighted exact-root jump measure. -/
private noncomputable def exactRootApproxCompactAverageMeasure
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) : FiniteMeasure ℝ :=
  ⟨(exactRootApproxTriple μroot n).ν.withDensity
      (fun x ↦ ENNReal.ofReal (compactAverageKernel x)),
    exactRootApproxCompactAverageMeasure_isFinite μroot n⟩

/-- Helper for Theorem 16.22: the compact-average exact-root auxiliary measure has no atom at
`0` because the compact-average weight vanishes there. -/
private lemma exactRootApproxCompactAverageMeasure_apply_zero_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    (((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ)
      ({0} : Set ℝ)) = 0 := by
  -- Proof comment: the exact-root auxiliary measure is defined by `withDensity` using
  -- `compactAverageKernel`, and that density is zero at the origin.
  change
    (((exactRootApproxTriple μroot n).ν.withDensity
      (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) ({0} : Set ℝ)) = 0
  rw [withDensity_apply _ (measurableSet_singleton 0)]
  simp [compactAverageKernel_zero]

/-- Helper for Theorem 16.22: the theorem-local quotient kernel used to reconstruct the
sine-centered Lévy kernel from the compact-average auxiliary measure. -/
private def compactAverageReconstructionKernel_local (t : ℝ) : ℝ → ℂ :=
  fun x ↦
    if hx : x = 0 then
      -((3 * t ^ (2 : ℕ) : ℝ) : ℂ)
    else
      levyKhinchinSineKernelLocal t x / compactAverageKernel x

/-- Helper for Theorem 16.22: the compact-average reconstruction kernel is measurable. -/
private lemma measurable_compactAverageReconstructionKernel_local (t : ℝ) :
    Measurable (compactAverageReconstructionKernel_local t) := by
  classical
  have hQuot :
      Measurable
        (fun x : ℝ ↦ levyKhinchinSineKernelLocal t x / compactAverageKernel x) := by
    -- Proof comment: away from the filled value at `0`, the reconstruction kernel is a quotient
    -- of the measurable sine-centered kernel by the measurable compact-average weight.
    have hNum :
        Measurable (fun x : ℝ ↦ levyKhinchinSineKernelLocal t x) := by
      have hExp :
          Measurable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) := by
        fun_prop
      have hCenter :
          Measurable (fun x : ℝ ↦ (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) := by
        exact
          (Complex.measurable_ofReal.comp
            (measurable_const.mul Real.continuous_sin.measurable)).mul_const Complex.I
      simpa [levyKhinchinSineKernelLocal] using (hExp.sub measurable_const).sub hCenter
    have hDen :
        Measurable (fun x : ℝ ↦ ((compactAverageKernel x : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp measurable_compactAverageKernel
    simpa using hNum.div hDen
  -- Proof comment: the only special value is the explicit fill-in at `0`, so measurability is a
  -- single `if`-combination over the measurable singleton.
  let s : Set ℝ := {x : ℝ | x = 0}
  have hs : MeasurableSet s := by
    simpa [s] using measurableSet_singleton (0 : ℝ)
  simpa [compactAverageReconstructionKernel_local, s] using
    measurable_const.piecewise hs hQuot

/-- Helper for Theorem 16.22: averaging the pure oscillatory factor over `[-1,1]` produces
`2 sinc(x)`. This bridge copy is placed before the reconstruction-kernel bound so the bound does
not depend on later declarations. -/
private lemma intervalIntegralExpMulCompactAverageBridge_local (x : ℝ) :
    ∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) =
      2 * (Real.sinc x : ℂ) := by
  calc
    ∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)
        = ∫ s in (-1 : ℝ)..1, charFun (Measure.dirac x) s := by
            refine intervalIntegral.integral_congr fun s _ ↦ ?_
            rw [MeasureTheory.charFun_dirac]
            rw [show inner ℝ x s = x * s by simpa using (RCLike.inner_apply' (𝕜 := ℝ) x s)]
            congr 1
            ring
    _ = 2 * (Real.sinc x : ℂ) := by
          simpa using
            (MeasureTheory.integral_charFun_Icc (μ := Measure.dirac x) (r := (1 : ℝ)) zero_lt_one)

/-- Helper for Theorem 16.22: bridge version of the compact-average interval formula needed by
the reconstruction-kernel bound before the later owner-local copy appears. -/
private lemma compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_bridge_local (x : ℝ) :
    compactAverageKernel x = (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
  have hExpInt :
      IntervalIntegrable
        (fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) volume (-1 : ℝ) 1 := by
    have hExpCont :
        Continuous (fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := by
      continuity
    exact hExpCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hReInt :
      ∫ s in (-1 : ℝ)..1, Complex.re (Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) =
        Complex.re (∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := by
    simpa using
      (Complex.reCLM.intervalIntegral_comp_comm (μ := volume)
        (a := (-1 : ℝ)) (b := (1 : ℝ))
        (f := fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) hExpInt)
  have hCosInt :
      ∫ s in (-1 : ℝ)..1, Real.cos (s * x) = 2 * Real.sinc x := by
    calc
      ∫ s in (-1 : ℝ)..1, Real.cos (s * x)
          = ∫ s in (-1 : ℝ)..1, Complex.re (Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := by
              refine intervalIntegral.integral_congr fun s _ ↦ ?_
              simpa using (Complex.exp_ofReal_mul_I_re (s * x)).symm
      _ = Complex.re
            (∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := hReInt
      _ = 2 * Real.sinc x := by
            rw [intervalIntegralExpMulCompactAverageBridge_local]
            simp
  have hCosCont :
      IntervalIntegrable (fun s : ℝ ↦ Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    have hCosCont' : Continuous (fun s : ℝ ↦ Real.cos (s * x)) := by
      simpa using (Real.continuous_cos.comp (continuous_id.mul continuous_const))
    exact hCosCont'.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hSub :
      ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) =
        (∫ s in (-1 : ℝ)..1, (1 : ℝ)) - ∫ s in (-1 : ℝ)..1, Real.cos (s * x) := by
    rw [intervalIntegral.integral_sub (μ := volume) intervalIntegrable_const hCosCont]
  have hConstIntEval : ∫ s in (-1 : ℝ)..1, (1 : ℝ) = 2 := by
    norm_num [intervalIntegral.integral_const]
  calc
    compactAverageKernel x = 1 - Real.sinc x := by
      simp [compactAverageKernel]
    _ = (1 / 2 : ℝ) * (2 - 2 * Real.sinc x) := by ring
    _ = (1 / 2 : ℝ) *
          ((∫ s in (-1 : ℝ)..1, (1 : ℝ)) - ∫ s in (-1 : ℝ)..1, Real.cos (s * x)) := by
            rw [hConstIntEval, hCosInt]
    _ = (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
          rw [← hSub]

/-- Helper for Theorem 16.22: bridge version of the quadratic upper cosine-defect bound used
before the later compact-average lower-bound block. -/
private lemma one_sub_cos_le_sq_div_two_bridge_local (y : ℝ) :
    1 - Real.cos y ≤ y ^ (2 : ℕ) / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos (x := y)]

/-- Helper for Theorem 16.22: bridge version of the lower cosine-defect bound on `[-1,1]`. -/
private lemma two_div_pi_sq_mul_sq_le_one_sub_cos_bridge_local {y : ℝ} (hy : |y| ≤ 1) :
    (2 / Real.pi ^ (2 : ℕ)) * y ^ (2 : ℕ) ≤ 1 - Real.cos y := by
  have hpi : |y| ≤ Real.pi := by
    linarith [hy, Real.pi_gt_three]
  have hcos := Real.cos_le_one_sub_mul_cos_sq (x := y) hpi
  linarith [hcos]

/-- Helper for Theorem 16.22: bridge version of the upper compact-average kernel bound near `0`.
-/
private lemma compactAverageKernel_le_half_sq_bridge_local {x : ℝ} (_hx : |x| ≤ 1) :
    compactAverageKernel x ≤ x ^ (2 : ℕ) / 2 := by
  have hDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hConstInt :
      IntervalIntegrable (fun _ : ℝ ↦ x ^ (2 : ℕ) / 2) volume (-1 : ℝ) 1 := intervalIntegrable_const
  have hMono :
      ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) ≤
        ∫ s in (-1 : ℝ)..1, (x ^ (2 : ℕ) / 2 : ℝ) := by
    refine intervalIntegral.integral_mono_on (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
      (f := fun s : ℝ ↦ 1 - Real.cos (s * x))
      (g := fun _ : ℝ ↦ x ^ (2 : ℕ) / 2)
      (hab := by norm_num) hDefectInt hConstInt ?_
    intro s hs
    have hsBounds : -1 ≤ s ∧ s ≤ 1 := by
      simpa using hs
    have hsAbs : |s| ≤ 1 := abs_le.mpr hsBounds
    have hDefect := one_sub_cos_le_sq_div_two_bridge_local (s * x)
    have hSq :
        (s * x) ^ (2 : ℕ) / 2 ≤ x ^ (2 : ℕ) / 2 := by
      have hsSq : s ^ (2 : ℕ) ≤ 1 := by
        nlinarith [sq_nonneg s, hsAbs]
      calc
        (s * x) ^ (2 : ℕ) / 2 = (s ^ (2 : ℕ) * x ^ (2 : ℕ)) / 2 := by ring
        _ ≤ (1 * x ^ (2 : ℕ)) / 2 := by
              nlinarith [hsSq, sq_nonneg x]
        _ = x ^ (2 : ℕ) / 2 := by ring
    exact hDefect.trans hSq
  calc
    compactAverageKernel x
        = (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
            rw [compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_bridge_local]
    _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (x ^ (2 : ℕ) / 2 : ℝ) := by
          gcongr
    _ = x ^ (2 : ℕ) / 2 := by
          rw [intervalIntegral.integral_const]
          norm_num
          ring

/-- Helper for Theorem 16.22: bridge version of the lower compact-average kernel bound near `0`.
-/
private lemma two_div_pi_sq_mul_sq_quarter_le_compactAverageKernel_bridge_local {x : ℝ}
    (hx : |x| ≤ 1) :
    x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x := by
  have hDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hLowerInt :
      IntervalIntegrable
        (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) volume (-1 : ℝ) 1 := by
    have hLowerCont : Continuous (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) := by
      continuity
    exact hLowerCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hMono :
      ∫ s in (-1 : ℝ)..1, (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) ≤
        ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
    refine intervalIntegral.integral_mono_on (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
      (f := fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ))
      (g := fun s : ℝ ↦ 1 - Real.cos (s * x))
      (hab := by norm_num) hLowerInt hDefectInt ?_
    intro s hs
    have hsBounds : -1 ≤ s ∧ s ≤ 1 := by
      simpa using hs
    have hsAbs : |s| ≤ 1 := abs_le.mpr hsBounds
    have hsxAbs : |s * x| ≤ 1 := by
      calc
        |s * x| = |s| * |x| := by rw [abs_mul]
        _ ≤ 1 * 1 := by
              gcongr
        _ = 1 := by ring
    simpa using two_div_pi_sq_mul_sq_le_one_sub_cos_bridge_local (y := s * x) hsxAbs
  have hSqHalf : (1 / 2 : ℝ) ≤ ∫ s in (-1 : ℝ)..1, s ^ (2 : ℕ) := by
    rw [integral_pow]
    norm_num
  let c : ℝ := (1 / 2 : ℝ) * ((2 / Real.pi ^ (2 : ℕ)) * x ^ (2 : ℕ))
  have hcNonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hFactor := mul_le_mul_of_nonneg_left hSqHalf hcNonneg
  have hLowerBound :
      x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ)) ≤
        (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) := by
    dsimp [c] at hFactor ⊢
    convert hFactor using 1
    · ring
    · rw [show (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) =
          fun s : ℝ ↦ ((2 / Real.pi ^ (2 : ℕ)) * x ^ (2 : ℕ)) * s ^ (2 : ℕ) by
            funext s
            ring]
      rw [intervalIntegral.integral_const_mul]
      ring
  calc
    x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ))
        ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) :=
          hLowerBound
    _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
          gcongr
    _ = compactAverageKernel x := by
          rw [compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_bridge_local]

/-- Helper for Theorem 16.22: bridge version of the shell lower bound on `compactAverageKernel`.
-/
private lemma one_div_twelve_pi_sq_le_compactAverageKernel_of_one_le_abs_le_two_bridge_local
    {x : ℝ} (hx1 : 1 ≤ |x|) (hx2 : |x| ≤ 2) :
    1 / (12 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x := by
  have hDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hLowerInt :
      IntervalIntegrable
        (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) volume (-1 / 2 : ℝ)
        (1 / 2 : ℝ) := by
    have hLowerCont : Continuous
        (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) := by
      continuity
    exact hLowerCont.intervalIntegrable (μ := volume) (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
  have hSmallDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
  have hNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 1)] fun s : ℝ ↦ 1 - Real.cos (s * x) := by
    exact Filter.Eventually.of_forall fun s ↦ sub_nonneg.mpr (Real.cos_le_one _)
  have hWindowMono :
      ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (1 - Real.cos (s * x)) ≤
        ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
    exact intervalIntegral.integral_mono_interval
      (μ := volume)
      (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (c := (-1 : ℝ)) (d := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) hNonneg hDefectInt
  have hMono :
      ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) ≤
        ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (1 - Real.cos (s * x)) := by
    refine intervalIntegral.integral_mono_on (μ := volume)
      (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (f := fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ))
      (g := fun s : ℝ ↦ 1 - Real.cos (s * x))
      (hab := by norm_num) hLowerInt hSmallDefectInt ?_
    intro s hs
    have hsBounds : -(1 / 2 : ℝ) ≤ s ∧ s ≤ 1 / 2 := by
      rcases hs with ⟨hsLeft, hsRight⟩
      constructor <;> linarith
    have hsAbs : |s| ≤ 1 / 2 := abs_le.mpr hsBounds
    have hsxAbs : |s * x| ≤ 1 := by
      calc
        |s * x| = |s| * |x| := by rw [abs_mul]
        _ ≤ (1 / 2 : ℝ) * 2 := by
              gcongr
        _ = 1 := by ring
    simpa using two_div_pi_sq_mul_sq_le_one_sub_cos_bridge_local (y := s * x) hsxAbs
  have hLowerEval :
      x ^ (2 : ℕ) / (6 * Real.pi ^ (2 : ℕ)) ≤
        ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) := by
    have hEval :
        ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) =
          x ^ (2 : ℕ) / (6 * Real.pi ^ (2 : ℕ)) := by
      rw [show (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) =
          fun s : ℝ ↦ ((2 / Real.pi ^ (2 : ℕ)) * x ^ (2 : ℕ)) * s ^ (2 : ℕ) by
            funext s
            ring]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      ring_nf
    exact le_of_eq hEval.symm
  have hShell :
      x ^ (2 : ℕ) / (12 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x := by
    calc
      x ^ (2 : ℕ) / (12 * Real.pi ^ (2 : ℕ))
          = (1 / 2 : ℝ) * (x ^ (2 : ℕ) / (6 * Real.pi ^ (2 : ℕ))) := by
              field_simp [Real.pi_ne_zero]
              ring
      _ ≤ (1 / 2 : ℝ) *
              ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_left hLowerEval (by norm_num : 0 ≤ (1 / 2 : ℝ))
      _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (1 - Real.cos (s * x)) := by
            gcongr
      _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
            gcongr
      _ = compactAverageKernel x := by
            rw [compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_bridge_local]
  have hxSqOne : 1 ≤ x ^ (2 : ℕ) := by
    have hxSqAbs : 1 ≤ |x| ^ (2 : ℕ) := by
      nlinarith [hx1, abs_nonneg x]
    simpa [sq_abs] using hxSqAbs
  have hOneToSq :
      1 / (12 * Real.pi ^ (2 : ℕ)) ≤ x ^ (2 : ℕ) / (12 * Real.pi ^ (2 : ℕ)) := by
    exact div_le_div_of_nonneg_right hxSqOne (by positivity : 0 ≤ 12 * Real.pi ^ (2 : ℕ))
  exact hOneToSq.trans hShell

/-- Helper for Theorem 16.22: bridge version of the inverse-weight estimate needed before the
later compact-average lower-bound API appears. -/
private lemma compactAverageInverseWeightBound_bridge_local (x : ℝ) :
    min (x ^ (2 : ℕ)) 1 ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
  by_cases hx1 : |x| ≤ 1
  · have hLower :=
      two_div_pi_sq_mul_sq_quarter_le_compactAverageKernel_bridge_local (x := x) hx1
    have hSq :
        x ^ (2 : ℕ) ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
      have hScaled := mul_le_mul_of_nonneg_left hLower (by positivity : 0 ≤ 12 * Real.pi ^ (2 : ℕ))
      calc
        x ^ (2 : ℕ) ≤ 6 * x ^ (2 : ℕ) := by
              nlinarith [sq_nonneg x]
        _ = (12 * Real.pi ^ (2 : ℕ)) * (x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ))) := by
              field_simp [Real.pi_ne_zero]
              ring
        _ ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := hScaled
    exact (min_le_left _ _).trans hSq
  · have hxgt : 1 < |x| := lt_of_not_ge hx1
    by_cases hx2 : |x| ≤ 2
    · have hShell :
          1 / (12 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x :=
        one_div_twelve_pi_sq_le_compactAverageKernel_of_one_le_abs_le_two_bridge_local
          (le_of_lt hxgt) hx2
      have hOne :
          1 ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
        have hScaled := mul_le_mul_of_nonneg_left hShell
          (by positivity : 0 ≤ 12 * Real.pi ^ (2 : ℕ))
        calc
          1 = (12 * Real.pi ^ (2 : ℕ)) * (1 / (12 * Real.pi ^ (2 : ℕ))) := by
                field_simp [Real.pi_ne_zero]
          _ ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := hScaled
      exact (min_le_right _ _).trans hOne
    · have hx2' : 2 < |x| := lt_of_not_ge hx2
      have hsincHalf : |Real.sinc x| ≤ 1 / (2 : ℝ) := by
        have hx0 : x ≠ 0 := by
          intro hx0
          rw [hx0] at hx2'
          norm_num at hx2'
        rw [Real.sinc_of_ne_zero hx0, abs_div]
        have hSin : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
        have hxAbsPos : 0 < |x| := abs_pos.mpr hx0
        have hDiv : |Real.sin x| / |x| ≤ 1 / |x| := by
          exact div_le_div_of_nonneg_right hSin hxAbsPos.le
        have hInv : 1 / |x| ≤ 1 / (2 : ℝ) := by
          exact one_div_le_one_div_of_le (by positivity) (le_of_lt hx2')
        exact hDiv.trans hInv
      have hKernelHalf : (1 / 2 : ℝ) ≤ compactAverageKernel x := by
        have hsincLeHalf : Real.sinc x ≤ 1 / (2 : ℝ) := le_trans (le_abs_self _) hsincHalf
        dsimp [compactAverageKernel]
        linarith
      have hOne :
          1 ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
        calc
          1 ≤ 6 * Real.pi ^ (2 : ℕ) := by
                nlinarith [Real.pi_gt_three]
          _ = (12 * Real.pi ^ (2 : ℕ)) * (1 / 2 : ℝ) := by
                ring
          _ ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
                gcongr
      exact (min_le_right _ _).trans hOne

/-- Helper for Theorem 16.22: the scaled compact-average kernel differs from its quadratic limit
by at most a linear error near `0`. -/
private lemma abs_compactAverageKernel_div_sq_sub_oneSix_le_local
    {x : ℝ} (hx : x ≠ 0) (hsmall : |x| ≤ 1) :
    |compactAverageKernel x / x ^ (2 : ℕ) - 1 / 6| ≤ |x| * (5 / 96) := by
  have hSin := Real.sin_bound hsmall
  have hxpow2 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
  have hxpow3 : x ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 hx
  have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
  calc
    |compactAverageKernel x / x ^ (2 : ℕ) - 1 / 6|
        = |-(Real.sin x - (x - x ^ (3 : ℕ) / 6)) / x ^ (3 : ℕ)| := by
            rw [compactAverageKernel, Real.sinc_of_ne_zero hx]
            congr 1
            field_simp [hxpow2, hxpow3]
            ring
    _ = |Real.sin x - (x - x ^ (3 : ℕ) / 6)| / |x| ^ (3 : ℕ) := by
          rw [abs_div, abs_neg, abs_pow]
    _ ≤ (|x| ^ (4 : ℕ) * (5 / 96)) / |x| ^ (3 : ℕ) := by
          exact div_le_div_of_nonneg_right hSin (by positivity)
    _ = |x| * (5 / 96) := by
          field_simp [hxabs]

/-- Helper for Theorem 16.22: after dividing by `x²`, the compact-average kernel tends to `1/6`
at the origin. -/
private lemma tendsto_compactAverageKernel_div_sq_at_zero_local :
    Tendsto (fun x : ℝ ↦ compactAverageKernel x / x ^ (2 : ℕ)) (𝓝[≠] 0) (𝓝 (1 / 6)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let A : ℝ := 5 / 96
  let δ : ℝ := min 1 (ε / (A + 1))
  have hδpos : 0 < δ := by
    dsimp [δ, A]
    refine lt_min (by norm_num) ?_
    positivity
  refine ⟨δ, hδpos, ?_⟩
  intro x hx hxDist
  have hsmall : |x| ≤ 1 := by
    have hxlt : |x| < δ := by
      simpa [Real.dist_eq, abs_sub_comm, δ] using hxDist
    exact le_of_lt (lt_of_lt_of_le hxlt (min_le_left _ _))
  have hNear :
      |compactAverageKernel x / x ^ (2 : ℕ) - 1 / 6| ≤ A * |x| := by
    simpa [A, mul_comm] using
      abs_compactAverageKernel_div_sq_sub_oneSix_le_local hx hsmall
  have hxlt : |x| < ε / (A + 1) := by
    have hxlt' : |x| < δ := by
      simpa [Real.dist_eq, abs_sub_comm, δ] using hxDist
    exact lt_of_lt_of_le hxlt' (min_le_right _ _)
  have hMul :
      (A + 1) * |x| < ε := by
    have hApos : 0 < A + 1 := by
      dsimp [A]
      positivity
    simpa [mul_comm] using (lt_div_iff₀ hApos).mp hxlt
  have hAle :
      A * |x| ≤ (A + 1) * |x| := by
    have hxnonneg : 0 ≤ |x| := abs_nonneg x
    have hA : A ≤ A + 1 := by
      dsimp [A]
      linarith
    exact mul_le_mul_of_nonneg_right hA hxnonneg
  calc
    dist (compactAverageKernel x / x ^ (2 : ℕ)) (1 / 6)
        = |compactAverageKernel x / x ^ (2 : ℕ) - 1 / 6| := by
            simp [Real.dist_eq]
    _ ≤ A * |x| := hNear
    _ < ε := lt_of_le_of_lt hAle hMul

/-- Helper for Theorem 16.22: the scaled cosine remainder has the expected quadratic limit at
the origin. -/
private lemma abs_cos_sub_one_div_sq_add_half_sq_le_local
    {t x : ℝ} (hx : x ≠ 0) (hsmall : |t * x| ≤ 1) :
    |(Real.cos (t * x) - 1) / x ^ (2 : ℕ) + t ^ (2 : ℕ) / 2| ≤
      (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) := by
  have hCos := Real.cos_bound hsmall
  have hxpow2 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
  have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
  calc
    |(Real.cos (t * x) - 1) / x ^ (2 : ℕ) + t ^ (2 : ℕ) / 2|
        = |(Real.cos (t * x) - (1 - (t * x) ^ (2 : ℕ) / 2)) / x ^ (2 : ℕ)| := by
            congr 1
            field_simp [hxpow2]
            ring
    _ = |Real.cos (t * x) - (1 - (t * x) ^ (2 : ℕ) / 2)| / |x| ^ (2 : ℕ) := by
          rw [abs_div, abs_pow]
    _ ≤ (|t * x| ^ (4 : ℕ) * (5 / 96)) / |x| ^ (2 : ℕ) := by
          exact div_le_div_of_nonneg_right hCos (by positivity)
    _ = (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) := by
          rw [abs_mul, mul_pow]
          field_simp [hxabs]

/-- Helper for Theorem 16.22: the real part of the scaled canonical kernel tends to `-t² / 2`
at the origin. -/
private lemma tendsto_cos_sub_one_div_sq_at_zero_local (t : ℝ) :
    Tendsto (fun x : ℝ ↦ (Real.cos (t * x) - 1) / x ^ (2 : ℕ)) (𝓝[≠] 0)
      (𝓝 (-(t ^ (2 : ℕ) / 2))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let A : ℝ := |t| ^ (4 : ℕ) * (5 / 96)
  let δ : ℝ := min 1 (min ((|t| + 1)⁻¹) (ε / (A + 1)))
  have hδpos : 0 < δ := by
    dsimp [δ]
    refine lt_min (by norm_num) ?_
    refine lt_min ?_ ?_
    · have : 0 < |t| + 1 := by positivity
      exact inv_pos.mpr this
    · positivity
  refine ⟨δ, hδpos, ?_⟩
  intro x hx hxDist
  have hxlt : |x| < δ := by
    simpa [Real.dist_eq, abs_sub_comm, δ] using hxDist
  have hsmallX : |x| ≤ 1 := le_of_lt (lt_of_lt_of_le hxlt (min_le_left _ _))
  have hδinv : δ ≤ (|t| + 1)⁻¹ := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have htxLt : |t * x| < 1 := by
    have hxInv : |x| < (|t| + 1)⁻¹ := lt_of_lt_of_le hxlt hδinv
    by_cases ht : t = 0
    · simp [ht]
    · calc
        |t * x| = |t| * |x| := by rw [abs_mul]
        _ < |t| * ((|t| + 1)⁻¹) := by
              exact mul_lt_mul_of_pos_left hxInv (abs_pos.mpr ht)
        _ = |t| / (|t| + 1) := by
              rw [div_eq_mul_inv]
        _ < 1 := by
              have hpos : 0 < |t| + 1 := by positivity
              have hlt : |t| < |t| + 1 := by linarith
              exact (div_lt_one hpos).2 hlt
  have hNear :
      |(Real.cos (t * x) - 1) / x ^ (2 : ℕ) + t ^ (2 : ℕ) / 2| ≤
        A * |x| ^ (2 : ℕ) :=
    abs_cos_sub_one_div_sq_add_half_sq_le_local hx (le_of_lt htxLt)
  have hNear' :
      |(Real.cos (t * x) - 1) / x ^ (2 : ℕ) + t ^ (2 : ℕ) / 2| ≤ A * |x| := by
    refine hNear.trans ?_
    have hPow : |x| ^ (2 : ℕ) ≤ |x| := by
      simpa using
        (pow_le_pow_of_le_one (abs_nonneg x) hsmallX (by decide : (1 : ℕ) ≤ 2))
    gcongr
  have hxlt' : |x| < ε / (A + 1) := by
    exact lt_of_lt_of_le hxlt (by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _))
  have hMul :
      (A + 1) * |x| < ε := by
    have hApos : 0 < A + 1 := by positivity
    simpa [mul_comm] using (lt_div_iff₀ hApos).mp hxlt'
  have hAle :
      A * |x| ≤ (A + 1) * |x| := by
    have hxnonneg : 0 ≤ |x| := abs_nonneg x
    have hA : A ≤ A + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hA hxnonneg
  calc
    dist ((Real.cos (t * x) - 1) / x ^ (2 : ℕ)) (-(t ^ (2 : ℕ) / 2))
        = |(Real.cos (t * x) - 1) / x ^ (2 : ℕ) + t ^ (2 : ℕ) / 2| := by
            simp [Real.dist_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ ≤ A * |x| := hNear'
    _ < ε := lt_of_le_of_lt hAle hMul

/-- Helper for Theorem 16.22: the scaled sine remainder is at most linear near the origin. -/
private lemma abs_sin_sub_linear_div_sq_le_local
    {t x : ℝ} (hx : x ≠ 0) (hsmall : |t * x| ≤ 1) :
    |(Real.sin (t * x) - t * x) / x ^ (2 : ℕ)| ≤
      |t| ^ (3 : ℕ) * |x| / 6 + (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) := by
  have hSin := Real.sin_bound hsmall
  have hxpow2 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
  have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
  have hErr :
      |(Real.sin (t * x) - ((t * x) - (t * x) ^ (3 : ℕ) / 6)) / x ^ (2 : ℕ)| ≤
        (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) := by
    calc
      |(Real.sin (t * x) - ((t * x) - (t * x) ^ (3 : ℕ) / 6)) / x ^ (2 : ℕ)|
          = |Real.sin (t * x) - ((t * x) - (t * x) ^ (3 : ℕ) / 6)| / |x| ^ (2 : ℕ) := by
              rw [abs_div, abs_pow]
      _ ≤ (|t * x| ^ (4 : ℕ) * (5 / 96)) / |x| ^ (2 : ℕ) := by
            exact div_le_div_of_nonneg_right hSin (by positivity)
      _ = (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) := by
            rw [abs_mul, mul_pow]
            field_simp [hxabs]
  have hDecomp :
      (Real.sin (t * x) - t * x) / x ^ (2 : ℕ) =
        (Real.sin (t * x) - ((t * x) - (t * x) ^ (3 : ℕ) / 6)) / x ^ (2 : ℕ) -
          t ^ (3 : ℕ) * x / 6 := by
    field_simp [hxpow2]
    ring
  calc
    |(Real.sin (t * x) - t * x) / x ^ (2 : ℕ)|
        ≤
          |(Real.sin (t * x) - ((t * x) - (t * x) ^ (3 : ℕ) / 6)) / x ^ (2 : ℕ)| +
            |t ^ (3 : ℕ) * x / 6| := by
              rw [hDecomp]
              simpa [sub_eq_add_neg] using
                (abs_sub_le
                  ((Real.sin (t * x) - ((t * x) - (t * x) ^ (3 : ℕ) / 6)) / x ^ (2 : ℕ))
                  0 (t ^ (3 : ℕ) * x / 6))
    _ ≤ (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) + |t ^ (3 : ℕ) * x / 6| := by
          gcongr
    _ = |t| ^ (3 : ℕ) * |x| / 6 + (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) := by
          rw [abs_div, abs_mul, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (6 : ℝ))]
          ring

/-- Helper for Theorem 16.22: the imaginary part of the scaled canonical kernel tends to `0` at
the origin. -/
private lemma tendsto_sin_sub_linear_div_sq_at_zero_local (t : ℝ) :
    Tendsto (fun x : ℝ ↦ (Real.sin (t * x) - t * x) / x ^ (2 : ℕ)) (𝓝[≠] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let B : ℝ := |t| ^ (3 : ℕ) / 6 + |t| ^ (4 : ℕ) * (5 / 96)
  let δ : ℝ := min 1 (min ((|t| + 1)⁻¹) (ε / (B + 1)))
  have hδpos : 0 < δ := by
    dsimp [δ]
    refine lt_min (by norm_num) ?_
    refine lt_min ?_ ?_
    · have : 0 < |t| + 1 := by positivity
      exact inv_pos.mpr this
    · positivity
  refine ⟨δ, hδpos, ?_⟩
  intro x hx hxDist
  have hxlt : |x| < δ := by
    simpa [Real.dist_eq, abs_sub_comm, δ] using hxDist
  have hsmallX : |x| ≤ 1 := le_of_lt (lt_of_lt_of_le hxlt (min_le_left _ _))
  have hδinv : δ ≤ (|t| + 1)⁻¹ := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have htxLt : |t * x| < 1 := by
    have hxInv : |x| < (|t| + 1)⁻¹ := lt_of_lt_of_le hxlt hδinv
    by_cases ht : t = 0
    · simp [ht]
    · calc
        |t * x| = |t| * |x| := by rw [abs_mul]
        _ < |t| * ((|t| + 1)⁻¹) := by
              exact mul_lt_mul_of_pos_left hxInv (abs_pos.mpr ht)
        _ = |t| / (|t| + 1) := by
              rw [div_eq_mul_inv]
        _ < 1 := by
              have hpos : 0 < |t| + 1 := by positivity
              have hlt : |t| < |t| + 1 := by linarith
              exact (div_lt_one hpos).2 hlt
  have hNear :
      |(Real.sin (t * x) - t * x) / x ^ (2 : ℕ)| ≤
        |t| ^ (3 : ℕ) * |x| / 6 + (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) :=
    abs_sin_sub_linear_div_sq_le_local hx (le_of_lt htxLt)
  have hNear' :
      |(Real.sin (t * x) - t * x) / x ^ (2 : ℕ)| ≤ B * |x| := by
    refine hNear.trans ?_
    have hPow : |x| ^ (2 : ℕ) ≤ |x| := by
      simpa using
        (pow_le_pow_of_le_one (abs_nonneg x) hsmallX (by decide : (1 : ℕ) ≤ 2))
    have hSecond :
        (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) ≤
          (|t| ^ (4 : ℕ) * (5 / 96)) * |x| := by
      gcongr
    calc
      |t| ^ (3 : ℕ) * |x| / 6 + (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ)
          ≤ |t| ^ (3 : ℕ) * |x| / 6 + (|t| ^ (4 : ℕ) * (5 / 96)) * |x| := by
              exact add_le_add le_rfl hSecond
      _ = B * |x| := by
            dsimp [B]
            ring
  have hxlt' : |x| < ε / (B + 1) := by
    exact lt_of_lt_of_le hxlt (by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _))
  have hMul :
      (B + 1) * |x| < ε := by
    have hBpos : 0 < B + 1 := by positivity
    simpa [mul_comm] using (lt_div_iff₀ hBpos).mp hxlt'
  have hBle :
      B * |x| ≤ (B + 1) * |x| := by
    have hxnonneg : 0 ≤ |x| := abs_nonneg x
    have hB : B ≤ B + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hB hxnonneg
  calc
    dist ((Real.sin (t * x) - t * x) / x ^ (2 : ℕ)) 0
        = |(Real.sin (t * x) - t * x) / x ^ (2 : ℕ)| := by
            rw [Real.dist_eq]
            simp
    _ ≤ B * |x| := hNear'
    _ < ε := lt_of_le_of_lt hBle hMul

/-- Helper for Theorem 16.22: the smooth centering `Real.sin` differs from the canonical cutoff by
at most `min (x^2) 1`. -/
private lemma norm_sin_sub_levyKhinchinCanonicalCentering_le_sqMinOne_local (x : ℝ) :
    ‖Real.sin x - levyKhinchinCanonicalCentering x‖ ≤ min (x ^ (2 : ℕ)) 1 := by
  by_cases hx : |x| < 1
  · by_cases hx0 : x = 0
    · subst hx0
      simp [levyKhinchinCanonicalCentering]
    · have hsmall : |(1 : ℝ) * x| ≤ 1 := by
        simpa using le_of_lt hx
      have hTaylor :=
        abs_sin_sub_linear_div_sq_le_local (t := (1 : ℝ)) hx0 hsmall
      have hDivLeOne : |(Real.sin x - x) / x ^ (2 : ℕ)| ≤ 1 := by
        have hTaylor' : |(Real.sin x - x) / x ^ (2 : ℕ)| ≤
            |x| / 6 + (5 / 96 : ℝ) * |x| ^ (2 : ℕ) := by
          simpa using hTaylor
        have hAux :
            |x| / 6 + (5 / 96 : ℝ) * |x| ^ (2 : ℕ) ≤ 1 := by
          have hxle : |x| ≤ 1 := le_of_lt hx
          nlinarith [abs_nonneg x, hxle]
        exact hTaylor'.trans hAux
      have hxSqPos : 0 < x ^ (2 : ℕ) := by
        nlinarith [sq_pos_iff.mpr hx0]
      have hDiv' : |Real.sin x - x| / x ^ (2 : ℕ) ≤ 1 := by
        simpa [abs_div, abs_of_pos hxSqPos, abs_pow] using hDivLeOne
      have hAbs : |Real.sin x - x| ≤ x ^ (2 : ℕ) := by
        simpa using (div_le_iff₀ hxSqPos).mp hDiv'
      simpa [levyKhinchinCanonicalCentering, hx, Real.norm_eq_abs,
        sqMinOne_eq_sq_of_abs_lt_one_local hx, abs_sub_comm] using hAbs
  · have hx' : 1 ≤ |x| := le_of_not_gt hx
    simpa [levyKhinchinCanonicalCentering, hx, Real.norm_eq_abs,
      sqMinOne_eq_one_of_one_le_abs_local hx', abs_sub_comm] using Real.abs_sin_le_one x

/-- Helper for Theorem 16.22: the sine-to-canonical centering correction is integrable against
every canonical Lévy measure. -/
private lemma integrable_sin_sub_levyKhinchinCanonicalCentering_local
    {ν : Measure ℝ} (hν : IsCanonicalMeasure ν) :
    Integrable (fun x : ℝ ↦ Real.sin x - levyKhinchinCanonicalCentering x) ν := by
  have hMeas :
      AEStronglyMeasurable (fun x : ℝ ↦ Real.sin x - levyKhinchinCanonicalCentering x) ν := by
    have hMeasurable :
        Measurable (fun x : ℝ ↦ Real.sin x - levyKhinchinCanonicalCentering x) := by
      exact (Real.continuous_sin.measurable).sub measurable_levyKhinchinCanonicalCentering
    exact hMeasurable.aestronglyMeasurable
  refine hν.integrable_sq_min_one.mono' hMeas ?_
  exact Filter.Eventually.of_forall fun x ↦
    norm_sin_sub_levyKhinchinCanonicalCentering_le_sqMinOne_local x

/-- Helper for Theorem 16.22: the compact-average reconstruction kernel is uniformly bounded by a
`t`-dependent constant. -/
private lemma norm_compactAverageReconstructionKernel_local_le (t x : ℝ) :
    ‖compactAverageReconstructionKernel_local t x‖ ≤
      (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) + 3 * t ^ (2 : ℕ) := by
  by_cases hx : x = 0
  · subst hx
    have hMainNonneg :
        0 ≤ (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) := by
      positivity
    -- Proof comment: at the filled value only the explicit quadratic constant remains.
    simpa [compactAverageReconstructionKernel_local] using
      (le_add_of_nonneg_left hMainNonneg : 3 * t ^ (2 : ℕ) ≤
        (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) + 3 * t ^ (2 : ℕ))
  · have hKernelPos : 0 < compactAverageKernel x := compactAverageKernel_pos_of_ne_zero hx
    have hEq :
        levyKhinchinSineKernelLocal t x =
          levyKhinchinCanonicalKernelLocal t x +
            ((((t * (levyKhinchinCanonicalCentering x - Real.sin x) : ℝ) : ℂ)) * Complex.I) := by
      simp [levyKhinchinSineKernelLocal, levyKhinchinCanonicalKernelLocal]
      ring
    have hCorr :
        ‖((((t * (levyKhinchinCanonicalCentering x - Real.sin x) : ℝ) : ℂ)) * Complex.I)‖ ≤
          |t| * min (x ^ (2 : ℕ)) 1 := by
      calc
        ‖((((t * (levyKhinchinCanonicalCentering x - Real.sin x) : ℝ) : ℂ)) * Complex.I)‖
            = |t * (levyKhinchinCanonicalCentering x - Real.sin x)| := by
              rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        _ = |t| * |levyKhinchinCanonicalCentering x - Real.sin x| := by
              rw [abs_mul]
        _ = |t| * |Real.sin x - levyKhinchinCanonicalCentering x| := by
              rw [abs_sub_comm]
        _ ≤ |t| * min (x ^ (2 : ℕ)) 1 := by
              exact mul_le_mul_of_nonneg_left
                (norm_sin_sub_levyKhinchinCanonicalCentering_le_sqMinOne_local x)
                (abs_nonneg t)
    have hNum :
        ‖levyKhinchinSineKernelLocal t x‖ ≤
          (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) *
            ((12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x) := by
      calc
        ‖levyKhinchinSineKernelLocal t x‖
            = ‖levyKhinchinCanonicalKernelLocal t x +
                ((((t * (levyKhinchinCanonicalCentering x - Real.sin x) : ℝ) : ℂ)) *
                  Complex.I)‖ := by
                  rw [hEq]
        _ ≤ ‖levyKhinchinCanonicalKernelLocal t x‖ +
              ‖((((t * (levyKhinchinCanonicalCentering x - Real.sin x) : ℝ) : ℂ)) *
                Complex.I)‖ := norm_add_le _ _
        _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 + |t| * min (x ^ (2 : ℕ)) 1 := by
              exact add_le_add (norm_levyKhinchinCanonicalKernelLocal_le t x) hCorr
        _ = (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * min (x ^ (2 : ℕ)) 1 := by ring
        _ ≤ (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) *
              ((12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x) := by
              gcongr
              exact compactAverageInverseWeightBound_bridge_local x
    have hQuot :
        ‖levyKhinchinSineKernelLocal t x‖ / compactAverageKernel x ≤
          (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) := by
      exact (div_le_iff₀ hKernelPos).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hNum)
    have hFillNonneg : 0 ≤ 3 * t ^ (2 : ℕ) := by
      positivity
    calc
      ‖compactAverageReconstructionKernel_local t x‖
          = ‖levyKhinchinSineKernelLocal t x‖ / compactAverageKernel x := by
              simp [compactAverageReconstructionKernel_local, hx, Complex.norm_real,
                Real.norm_eq_abs, abs_of_pos hKernelPos]
      _ ≤ (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) := hQuot
      _ ≤ (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) + 3 * t ^ (2 : ℕ) :=
            le_add_of_nonneg_right hFillNonneg

/-- Helper for Theorem 16.22: the quotient kernel used to reconstruct the sine-centered kernel has
the correct filled value at `0`. -/
private lemma tendsto_compactAverageReconstructionQuotient_at_zero_local (t : ℝ) :
    Tendsto (fun x : ℝ ↦ levyKhinchinSineKernelLocal t x / ((compactAverageKernel x : ℝ) : ℂ))
      (𝓝[≠] 0)
      (𝓝 (-((3 * t ^ (2 : ℕ) : ℝ) : ℂ))) := by
  let num : ℝ → ℂ := fun x ↦
    (((Real.cos (t * x) - 1) / x ^ (2 : ℕ) : ℝ) : ℂ) +
      ((((Real.sin (t * x) - t * Real.sin x) / x ^ (2 : ℕ) : ℝ) : ℂ) * Complex.I)
  have hNum :
      Tendsto num (𝓝[≠] 0) (𝓝 (-((t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
    have hRe :
        Tendsto (fun x : ℝ ↦ ((Real.cos (t * x) - 1) / x ^ (2 : ℕ) : ℂ))
          (𝓝[≠] 0) (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
      convert
        (Complex.continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_cos_sub_one_div_sq_at_zero_local t)) using 1
      · ext x
        simp
      · simp
    have hImReal :
        Tendsto
          (fun x : ℝ ↦ (Real.sin (t * x) - t * Real.sin x) / x ^ (2 : ℕ))
          (𝓝[≠] 0) (𝓝 0) := by
      have hMain := tendsto_sin_sub_linear_div_sq_at_zero_local t
      have hBase :
          Tendsto (fun x : ℝ ↦ -((Real.sin x - x) / x ^ (2 : ℕ))) (𝓝[≠] 0) (𝓝 0) := by
        simpa using (tendsto_sin_sub_linear_div_sq_at_zero_local (1 : ℝ)).neg
      have hCorrectionBase :
          Tendsto (fun x : ℝ ↦ (x - Real.sin x) / x ^ (2 : ℕ)) (𝓝[≠] 0) (𝓝 0) := by
        refine hBase.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        have hxpow2 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
        field_simp [hxpow2]
        ring
      have hCorrection :
          Tendsto (fun x : ℝ ↦ t * ((x - Real.sin x) / x ^ (2 : ℕ)))
            (𝓝[≠] 0) (𝓝 0) := by
        simpa using tendsto_const_nhds.mul hCorrectionBase
      have hSum :
          Tendsto
            (fun x : ℝ ↦
              (Real.sin (t * x) - t * x) / x ^ (2 : ℕ) +
                t * ((x - Real.sin x) / x ^ (2 : ℕ)))
            (𝓝[≠] 0) (𝓝 0) := by
        simpa using hMain.add hCorrection
      refine hSum.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hxpow2 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
      field_simp [hxpow2]
      ring
    have hIm :
        Tendsto
          (fun x : ℝ ↦ (((Real.sin (t * x) - t * Real.sin x) / x ^ (2 : ℕ) : ℝ) : ℂ) *
            Complex.I)
          (𝓝[≠] 0) (𝓝 (0 * Complex.I)) := by
      exact ((Complex.continuous_ofReal.continuousAt.tendsto.comp hImReal).mul tendsto_const_nhds)
    simpa [num] using hRe.add hIm
  have hDen :
      Tendsto (fun x : ℝ ↦ ((compactAverageKernel x / x ^ (2 : ℕ) : ℝ) : ℂ))
        (𝓝[≠] 0) (𝓝 (((1 / 6 : ℝ) : ℂ))) := by
    exact
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_compactAverageKernel_div_sq_at_zero_local)
  have hScaled :
      Tendsto (fun x : ℝ ↦ num x / ((compactAverageKernel x / x ^ (2 : ℕ) : ℝ) : ℂ))
        (𝓝[≠] 0) (𝓝 ((-((t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) / (((1 / 6 : ℝ) : ℂ)))) := by
    exact hNum.div hDen (by norm_num)
  have hQuot :
      Tendsto (fun x : ℝ ↦ levyKhinchinSineKernelLocal t x / ((compactAverageKernel x : ℝ) : ℂ))
        (𝓝[≠] 0) (𝓝 ((-((t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) / (((1 / 6 : ℝ) : ℂ)))) := by
    refine hScaled.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with x hx hxBall
    have hxpow2 : ((x : ℂ) ^ (2 : ℕ)) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 hx
    have hKernelNe : ((compactAverageKernel x : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (compactAverageKernel_pos_of_ne_zero hx)
    have hNumEq :
        num x * (x : ℂ) ^ (2 : ℕ) = levyKhinchinSineKernelLocal t x := by
      have hx0 : x ≠ 0 := by simpa using hx
      dsimp [num, levyKhinchinSineKernelLocal]
      rw [Complex.exp_ofReal_mul_I]
      simp [div_eq_mul_inv]
      field_simp [hx0]
      ring_nf
    have hDenEq :
        ((compactAverageKernel x / x ^ (2 : ℕ) : ℝ) : ℂ) =
          ((compactAverageKernel x : ℝ) : ℂ) / (x : ℂ) ^ (2 : ℕ) := by
      norm_num [div_eq_mul_inv]
    calc
      num x / ((compactAverageKernel x / x ^ (2 : ℕ) : ℝ) : ℂ)
          = num x / (((compactAverageKernel x : ℝ) : ℂ) / (x : ℂ) ^ (2 : ℕ)) := by
              rw [hDenEq]
      _ = num x * (x : ℂ) ^ (2 : ℕ) / ((compactAverageKernel x : ℝ) : ℂ) := by
            field_simp [hxpow2, hKernelNe]
      _ = levyKhinchinSineKernelLocal t x / ((compactAverageKernel x : ℝ) : ℂ) := by
            rw [hNumEq]
  have hQuot' :
      Tendsto (fun x : ℝ ↦ levyKhinchinSineKernelLocal t x / ((compactAverageKernel x : ℝ) : ℂ))
        (𝓝[≠] 0) (𝓝 (-(↑t ^ (2 : ℕ) / 2 * 6))) := by
    simpa [div_eq_mul_inv] using hQuot
  have hQuot'' :
      Tendsto (fun x : ℝ ↦ levyKhinchinSineKernelLocal t x / ((compactAverageKernel x : ℝ) : ℂ))
        (𝓝[≠] 0) (𝓝 (-(((t ^ (2 : ℕ)) * 3 : ℝ) : ℂ))) := by
    convert hQuot' using 1
    congr 1
    calc
      -(((t ^ (2 : ℕ)) * 3 : ℝ) : ℂ) = -(↑t ^ (2 : ℕ) * 3) := by simp
      _ = -(↑t ^ (2 : ℕ) * ((1 / 2 : ℂ) * 6)) := by norm_num
      _ = -(↑t ^ (2 : ℕ) / 2 * 6) := by ring_nf
  simpa [mul_comm] using hQuot''

/-- Helper for Theorem 16.22: the compact-average reconstruction kernel is continuous. -/
private lemma continuous_compactAverageReconstructionKernel_local (t : ℝ) :
    Continuous (compactAverageReconstructionKernel_local t) := by
  refine continuous_iff_continuousAt.2 ?_
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [Metric.continuousAt_iff]
    intro ε hε
    rcases (Metric.tendsto_nhdsWithin_nhds.mp
        (tendsto_compactAverageReconstructionQuotient_at_zero_local t)) ε hε with
      ⟨δ, hδpos, hδ⟩
    refine ⟨δ, hδpos, ?_⟩
    intro y hyDist
    by_cases hy : y = 0
    · subst hy
      simpa [compactAverageReconstructionKernel_local] using hε
    · simpa [compactAverageReconstructionKernel_local, hy] using hδ hy hyDist
  · have hQuot :
      ContinuousAt (fun y : ℝ ↦ levyKhinchinSineKernelLocal t y / compactAverageKernel y) x :=
      by
        have hNum :
            ContinuousAt
              (fun y : ℝ ↦
                Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) - 1 -
                  (((t * Real.sin y : ℝ) : ℂ) * Complex.I)) x := by
          fun_prop
        have hNum' : ContinuousAt (fun y : ℝ ↦ levyKhinchinSineKernelLocal t y) x := by
          simpa [levyKhinchinSineKernelLocal] using hNum
        have hDen :
            ContinuousAt (fun y : ℝ ↦ ((compactAverageKernel y : ℝ) : ℂ)) x := by
          exact
            Complex.continuous_ofReal.continuousAt.comp
              continuous_compactAverageKernel.continuousAt
        have hDenNe : (((compactAverageKernel x : ℝ) : ℂ)) ≠ 0 := by
          exact_mod_cast (compactAverageKernel_pos_of_ne_zero hx).ne'
        exact ContinuousAt.div hNum' hDen hDenNe
    have hAway : ∀ᶠ y in 𝓝 x, y ≠ 0 := by
      filter_upwards [Metric.ball_mem_nhds x (half_pos (abs_pos.mpr hx))] with y hy
      have hyDist : |y - x| < |x| / 2 := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hy
      intro hy0
      subst hy0
      have hxabs : 0 < |x| := abs_pos.mpr hx
      have : |x| < |x| / 2 := by simpa using hyDist
      nlinarith
    exact hQuot.congr_of_eventuallyEq <|
      hAway.mono fun y hy ↦ by simp [compactAverageReconstructionKernel_local, hy]

/-- Helper for Theorem 16.22: every finite measure integrates the compact-average reconstruction
kernel because the kernel is measurable and uniformly bounded. -/
private lemma integrable_compactAverageReconstructionKernel_of_isFiniteMeasure_local
    (t : ℝ) (η : Measure ℝ) [IsFiniteMeasure η] :
    Integrable (compactAverageReconstructionKernel_local t) η := by
  let C : ℝ := (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) + 3 * t ^ (2 : ℕ)
  have hBound : Integrable (fun _ : ℝ ↦ C) η := integrable_const C
  -- Proof comment: a measurable complex-valued function dominated by one real constant is
  -- integrable against every finite measure.
  refine hBound.mono' (measurable_compactAverageReconstructionKernel_local t).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    have hCNonneg : 0 ≤ C := by
      dsimp [C]
      positivity
    simpa [C, Real.norm_eq_abs, abs_of_nonneg hCNonneg] using
      norm_compactAverageReconstructionKernel_local_le t x

/-- Helper for Theorem 16.22: multiplying the reconstruction quotient kernel by
`compactAverageKernel` recovers the smooth sine-centered Lévy kernel pointwise. -/
private lemma compactAverageReconstructionKernel_mul_kernel_local
    (t x : ℝ) :
    ((compactAverageKernel x : ℝ) : ℂ) * compactAverageReconstructionKernel_local t x =
      levyKhinchinSineKernelLocal t x := by
  by_cases hx : x = 0
  · subst hx
    -- Proof comment: at the origin both sides vanish because the canonical kernel and the
    -- compact-average weight are zero there.
    simp [compactAverageReconstructionKernel_local, compactAverageKernel_zero,
      levyKhinchinSineKernelLocal]
  · have hkernelNe : ((compactAverageKernel x : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (compactAverageKernel_pos_of_ne_zero hx)
    -- Proof comment: away from `0`, the quotient definition is exact and cancellation is legal.
    simp [compactAverageReconstructionKernel_local, hx]
    field_simp [hkernelNe]

/-- Helper for Theorem 16.22: integrating the reconstruction quotient kernel against the
compact-average exact-root auxiliary measure rewrites to the sine-centered kernel integral against
the exact-root Lévy measure. -/
private lemma integral_compactAverageReconstructionKernel_exactRootApprox_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
      ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) =
      ∫ x : ℝ, levyKhinchinSineKernelLocal t x ∂(exactRootApproxTriple μroot n).ν := by
  -- Proof comment: unfold the `withDensity` definition of the exact-root auxiliary measure and
  -- absorb the compact-average weight into the quotient kernel.
  change
    ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
      ((exactRootApproxTriple μroot n).ν.withDensity
        (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) =
      ∫ x : ℝ, levyKhinchinSineKernelLocal t x ∂(exactRootApproxTriple μroot n).ν
  rw [integral_withDensity_eq_integral_toReal_smul
    measurable_compactAverageKernel.ennreal_ofReal
    (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
  have hnonneg : 0 ≤ compactAverageKernel x := compactAverageKernel_nonneg x
  calc
    (ENNReal.ofReal (compactAverageKernel x)).toReal • compactAverageReconstructionKernel_local t x
        = ((compactAverageKernel x : ℝ) : ℂ) * compactAverageReconstructionKernel_local t x := by
            simp [hnonneg, smul_eq_mul]
    _ = levyKhinchinSineKernelLocal t x :=
          compactAverageReconstructionKernel_mul_kernel_local t x

/-- Helper for Theorem 16.22: recovering the jump measure from the exact-root compact-average
auxiliary measure returns the original exact-root jump intensity. -/
private lemma compactAverageRecoveredJumpMeasure_exactRootApprox_eq_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    compactAverageRecoveredJumpMeasure_local (exactRootApproxCompactAverageMeasure μroot n) =
      (exactRootApproxTriple μroot n).ν := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  have hν : IsCanonicalMeasure ν :=
    (exactRootApproxTriple_hasLevyKhinchinRepresentation_local μroot n).isCanonicalTriple.isCanonicalMeasure
  -- Proof comment: puncturing the exact-root compact-average auxiliary measure leaves precisely
  -- the compact-average weighted jump intensity, and the inverse density then removes that weight.
  calc
    compactAverageRecoveredJumpMeasure_local (exactRootApproxCompactAverageMeasure μroot n)
        =
      (((ν.restrict ({0}ᶜ : Set ℝ)).withDensity
          (fun x ↦ ENNReal.ofReal (compactAverageKernel x))).withDensity
        (fun x ↦ (ENNReal.ofReal (compactAverageKernel x))⁻¹)) := by
          rw [compactAverageRecoveredJumpMeasure_local, exactRootApproxCompactAverageMeasure]
          exact congrArg
            (fun μ : Measure ℝ ↦
              μ.withDensity (fun x ↦ (ENNReal.ofReal (compactAverageKernel x))⁻¹))
            (MeasureTheory.restrict_withDensity ((measurableSet_singleton (0 : ℝ)).compl)
              (μ := ν) (f := fun x ↦ ENNReal.ofReal (compactAverageKernel x)))
    _ = ν.restrict ({0}ᶜ : Set ℝ) := by
          exact withDensity_compactAverageKernel_inv_same_restrict_compl_singleton ν
    _ = ν.restrict ({0} : Set ℝ) + ν.restrict ({0}ᶜ : Set ℝ) := by
          rw [Measure.restrict_singleton, hν.measure_singleton_zero, zero_smul, zero_add]
    _ = ν := by
          simpa using
            (Measure.restrict_add_restrict_compl (μ := ν) (measurableSet_singleton (0 : ℝ)))

/-- Helper for Theorem 16.22: integrating the reconstruction kernel against the weighted
recovered jump measure rewrites to the sine-centered Lévy kernel integral. -/
private lemma integral_compactAverageReconstructionKernel_recovered_local
    (η : FiniteMeasure ℝ) (t : ℝ) :
    ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
      ((compactAverageRecoveredJumpMeasure_local η).withDensity
        (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) =
      ∫ x : ℝ, levyKhinchinSineKernelLocal t x ∂(compactAverageRecoveredJumpMeasure_local η) :=
    by
  -- Proof comment: push the compact-average density back through the integral so the quotient
  -- kernel collapses to the sine-centered Lévy kernel pointwise.
  rw [integral_withDensity_eq_integral_toReal_smul
    measurable_compactAverageKernel.ennreal_ofReal
    (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
  have hnonneg : 0 ≤ compactAverageKernel x := compactAverageKernel_nonneg x
  calc
    (ENNReal.ofReal (compactAverageKernel x)).toReal • compactAverageReconstructionKernel_local t x
        = ((compactAverageKernel x : ℝ) : ℂ) * compactAverageReconstructionKernel_local t x := by
            simp [hnonneg, smul_eq_mul]
    _ = levyKhinchinSineKernelLocal t x :=
          compactAverageReconstructionKernel_mul_kernel_local t x

/-- Helper for Theorem 16.22: the drift adjustment needed to rewrite the exact-root exponent with
the smooth centering `Real.sin`. -/
private noncomputable def exactRootApproxReconstructionDrift_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) : ℝ :=
  (exactRootApproxTriple μroot n).b +
    ∫ x : ℝ, (Real.sin x - levyKhinchinCanonicalCentering x) ∂(exactRootApproxTriple μroot n).ν

/-- Helper for Theorem 16.22: the jump measure recovered from a compact-average auxiliary finite
measure is canonical. -/
private lemma isCanonicalMeasure_compactAverageRecoveredJumpMeasure_local
    (η : FiniteMeasure ℝ) :
    IsCanonicalMeasure (compactAverageRecoveredJumpMeasure_local η) := by
  -- Proof comment: rewrite the recovered measure through the inverse compact-average density on
  -- `η.restrict ({0}ᶜ)`, then use `compactAverageInverseWeightBound_bridge_local` to dominate
  -- `x ↦ min (x^2) 1 / compactAverageKernel x` by one global constant.
  refine ⟨?_, ?_⟩
  · -- Proof comment: the recovered measure is supported on `{0}ᶜ`, so the singleton at `0`
    -- receives zero mass.
    rw [compactAverageRecoveredJumpMeasure_local, withDensity_apply _ (measurableSet_singleton 0)]
    simp
  · let μ : Measure ℝ := (η : Measure ℝ).restrict ({0}ᶜ : Set ℝ)
    let C : ℝ := 12 * Real.pi ^ (2 : ℕ)
    have hInvLtTop :
        ∀ᵐ x ∂μ, (ENNReal.ofReal (compactAverageKernel x))⁻¹ < ⊤ := by
      filter_upwards [compactAverageKernel_ae_ne_zero_restrict_compl_singleton (η : Measure ℝ)] with x hx
      have hKernelPos : 0 < compactAverageKernel x := by
        exact lt_of_le_of_ne (compactAverageKernel_nonneg x) (by simpa [eq_comm] using hx)
      have hx0 : ENNReal.ofReal (compactAverageKernel x) ≠ 0 := by
        exact ne_of_gt (ENNReal.ofReal_pos.mpr hKernelPos)
      simpa [hx0]
    rw [compactAverageRecoveredJumpMeasure_local]
    rw [integrable_withDensity_iff measurable_compactAverageKernel.ennreal_ofReal.inv hInvLtTop]
    letI : IsFiniteMeasure μ := by
      dsimp [μ]
      infer_instance
    have hMeas :
        AEStronglyMeasurable
          (fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1 * ((ENNReal.ofReal (compactAverageKernel x))⁻¹).toReal)
          μ := by
      exact
        (((measurable_id.pow_const 2).min measurable_const).mul
          ((measurable_compactAverageKernel.ennreal_ofReal.inv).ennreal_toReal)).aestronglyMeasurable
    refine (integrable_const C).mono' hMeas ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      by_cases hx : x = 0
      · subst hx
        have hC : 0 ≤ C := by
          dsimp [C]
          positivity
        simpa [C, compactAverageKernel] using hC
      · have hKernelPos : 0 < compactAverageKernel x := by
          exact compactAverageKernel_pos_of_ne_zero hx
        have hMinNonneg : 0 ≤ min (x ^ (2 : ℕ)) 1 := by positivity
        have hToRealInv :
            ((ENNReal.ofReal (compactAverageKernel x))⁻¹).toReal =
              (compactAverageKernel x)⁻¹ := by
          rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal]
          simp [compactAverageKernel_nonneg x]
        have hBound :
            min (x ^ (2 : ℕ)) 1 / compactAverageKernel x ≤ C := by
          exact
            (div_le_iff₀ hKernelPos).2
              (by
                simpa [C, mul_comm, mul_left_comm, mul_assoc] using
                  compactAverageInverseWeightBound_bridge_local x)
        have hInvNonneg : 0 ≤ (compactAverageKernel x)⁻¹ := by positivity
        simpa [C, Real.norm_eq_abs, abs_of_nonneg hMinNonneg, abs_of_nonneg hInvNonneg,
          abs_of_pos hKernelPos, hToRealInv, div_eq_mul_inv, mul_comm, mul_left_comm,
          mul_assoc] using hBound

/-- Helper for Theorem 16.22: the recovered compact-average auxiliary finite measure determines
the zero-drift Gaussian-plus-jump part of the sine-centered Lévy--Khinchin exponent. -/
private lemma compactAverageRecoveredZeroDriftExponent_local
    (η : FiniteMeasure ℝ) (t : ℝ) :
    let σ2 : ℝ := 6 * (((η : Measure ℝ) ({0} : Set ℝ)).toReal)
    let ν := compactAverageRecoveredJumpMeasure_local η
    levyKhinchinExponentWithCentering σ2 0 ν Real.sin t =
      ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(η : Measure ℝ) := by
  -- Proof comment: split `η` into its atom at `0` plus the weighted recovered jump measure,
  -- identify the atom contribution with the Gaussian quadratic term, and rewrite the weighted
  -- contribution through `integral_compactAverageReconstructionKernel_recovered_local`.
  dsimp
  let atomMass : ENNReal := ((η : Measure ℝ) ({0} : Set ℝ))
  let ν := compactAverageRecoveredJumpMeasure_local η
  have hIntAtom :
      Integrable (compactAverageReconstructionKernel_local t) (atomMass • Measure.dirac 0) := by
    letI : IsFiniteMeasure (atomMass • Measure.dirac (0 : ℝ)) := by
      refine ⟨?_⟩
      simp [atomMass]
    exact
      integrable_compactAverageReconstructionKernel_of_isFiniteMeasure_local
        t (atomMass • Measure.dirac 0)
  have hIntWeighted :
      Integrable (compactAverageReconstructionKernel_local t)
        (ν.withDensity (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) := by
    rw [compactAverageRecoveredJumpMeasure_weighted_eq_restrict_compl_local]
    letI : IsFiniteMeasure ((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) := by
      infer_instance
    exact
      integrable_compactAverageReconstructionKernel_of_isFiniteMeasure_local
        t ((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ))
  have hAtomEval :
      ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(atomMass • Measure.dirac 0) =
        (((-(6 * atomMass.toReal / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) := by
    -- Proof comment: the filled value at `0` turns the atom contribution into the Gaussian
    -- quadratic term.
    rw [integral_smul_measure, integral_dirac]
    simp [atomMass, compactAverageReconstructionKernel_local]
    change ((atomMass.toReal : ℂ) * (3 * ↑t ^ (2 : ℕ))) =
      6 * ↑(atomMass.toReal) / 2 * ↑t ^ (2 : ℕ)
    ring
  calc
    levyKhinchinExponentWithCentering (6 * atomMass.toReal) 0 ν Real.sin t =
        (((-(6 * atomMass.toReal / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
          ∫ x : ℝ, levyKhinchinSineKernelLocal t x ∂ν := by
            simp [levyKhinchinExponentWithCentering, levyKhinchinSineKernelLocal, atomMass, ν]
    _ =
        ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(atomMass • Measure.dirac 0) +
          ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
            (ν.withDensity (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) := by
            rw [hAtomEval, integral_compactAverageReconstructionKernel_recovered_local]
    _ =
        ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
          (atomMass • Measure.dirac 0 +
            ν.withDensity (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) := by
            rw [integral_add_measure hIntAtom hIntWeighted]
    _ = ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(η : Measure ℝ) := by
            rw [compactAverageRecoveredJumpMeasure_decomposition_local η]

/-- Helper for Theorem 16.22: adding a drift coefficient to a fixed Gaussian/jump pair
contributes exactly the linear imaginary phase term in the sine-centered Lévy--Khintchin
exponent. -/
private lemma levyKhinchinExponentWithSineCentering_add_drift_eq_local
    (σ2 b : ℝ) (ν : Measure ℝ) (t : ℝ) :
    levyKhinchinExponentWithCentering σ2 b ν Real.sin t =
      levyKhinchinExponentWithCentering σ2 0 ν Real.sin t +
        ((((b * t : ℝ) : ℂ)) * Complex.I) := by
  -- Proof comment: the Gaussian and jump terms stay fixed, so only the explicit drift line
  -- changes.
  simp [levyKhinchinExponentWithCentering]
  ring

/-- Helper for Theorem 16.22: each exact-root exponent splits into its compact-average
reconstruction integral plus the explicit drift line from the centering constant. -/
private lemma exactRootApproxExponent_eq_reconstructionIntegral_add_drift_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    levyKhinchinExponent (exactRootApproxTriple μroot n) t =
      (∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
          ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ)) +
        ((((exactRootApproxReconstructionDrift_local μroot n * t : ℝ) : ℂ) * Complex.I)) := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  have hν : IsCanonicalMeasure ν :=
    (exactRootApproxTriple_hasLevyKhinchinRepresentation_local μroot n).isCanonicalTriple.isCanonicalMeasure
  have hDiffInt :
      Integrable (fun x : ℝ ↦ Real.sin x - levyKhinchinCanonicalCentering x) ν :=
    integrable_sin_sub_levyKhinchinCanonicalCentering_local hν
  have hChange :
      levyKhinchinExponent (exactRootApproxTriple μroot n) t =
        levyKhinchinExponentWithCentering
          0 (exactRootApproxReconstructionDrift_local μroot n) ν Real.sin t := by
    have hChangeFn :=
      levyKhinchinExponentWithCentering_changeCentering
        0 (exactRootApproxTriple μroot n).b ν hν Real.sin hDiffInt
    have hChangeAt := congrArg (fun f : ℝ → ℂ ↦ f t) hChangeFn
    simpa [exactRootApproxReconstructionDrift_local, ν, levyKhinchinExponent] using hChangeAt.symm
  have hZeroDrift :
      levyKhinchinExponentWithCentering 0 0 ν Real.sin t =
        ∫ x : ℝ, levyKhinchinSineKernelLocal t x ∂ν := by
    -- Proof comment: when the Gaussian and drift terms vanish, the exponent is exactly the
    -- sine-centered jump-kernel integral.
    simp [levyKhinchinExponentWithCentering, levyKhinchinSineKernelLocal, ν]
  -- Proof comment: peel off the explicit linear drift, then transport the zero-drift integral
  -- through the compact-average auxiliary measure.
  calc
    levyKhinchinExponent (exactRootApproxTriple μroot n) t =
        levyKhinchinExponentWithCentering 0 0 ν Real.sin t +
          ((((exactRootApproxReconstructionDrift_local μroot n * t : ℝ) : ℂ) * Complex.I)) := by
            rw [hChange]
            rw [levyKhinchinExponentWithSineCentering_add_drift_eq_local]
    _ =
        (∫ x : ℝ, levyKhinchinSineKernelLocal t x ∂ν) +
          ((((exactRootApproxReconstructionDrift_local μroot n * t : ℝ) : ℂ) * Complex.I)) := by
            rw [hZeroDrift]
    _ =
        (∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
            ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ)) +
          ((((exactRootApproxReconstructionDrift_local μroot n * t : ℝ) : ℂ) * Complex.I)) := by
            rw [integral_compactAverageReconstructionKernel_exactRootApprox_local]

/-- Helper for Theorem 16.22: averaging the pure oscillatory factor over `[-1,1]` produces
`2 sinc(x)`. -/
private lemma intervalIntegral_exp_mul_compactAverage_local (x : ℝ) :
    ∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) =
      2 * (Real.sinc x : ℂ) := by
  -- Proof comment: specialize `integral_charFun_Icc` to the Dirac mass at `x`, then rewrite the
  -- resulting characteristic function and Dirac integral explicitly.
  calc
    ∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)
        = ∫ s in (-1 : ℝ)..1, charFun (Measure.dirac x) s := by
            refine intervalIntegral.integral_congr fun s hs ↦ ?_
            rw [MeasureTheory.charFun_dirac]
            rw [show inner ℝ x s = x * s by simpa using (RCLike.inner_apply' (𝕜 := ℝ) x s)]
            congr 1
            ring
    _ = 2 * (Real.sinc x : ℂ) := by
          simpa using
            (MeasureTheory.integral_charFun_Icc (μ := Measure.dirac x) (r := (1 : ℝ)) zero_lt_one)

/-- Helper for Theorem 16.22: `compactAverageKernel` is the half-interval average of
`1 - cos (s * x)` over `[-1, 1]`. -/
private lemma compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_local (x : ℝ) :
    compactAverageKernel x = (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
  -- Route correction: instead of rebuilding the compact-average identity from `sinc` algebra, take
  -- real parts of the already proved complex oscillatory integral.
  have hExpInt :
      IntervalIntegrable
        (fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) volume (-1 : ℝ) 1 := by
    -- Proof comment: the oscillatory phase factor is continuous on the compact interval.
    have hExpCont :
        Continuous (fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := by
      continuity
    exact hExpCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hReInt :
      ∫ s in (-1 : ℝ)..1, Complex.re (Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) =
        Complex.re (∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := by
    simpa using
      (Complex.reCLM.intervalIntegral_comp_comm (μ := volume)
        (a := (-1 : ℝ)) (b := (1 : ℝ))
        (f := fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) hExpInt)
  have hCosInt :
      ∫ s in (-1 : ℝ)..1, Real.cos (s * x) = 2 * Real.sinc x := by
    calc
      ∫ s in (-1 : ℝ)..1, Real.cos (s * x)
          = ∫ s in (-1 : ℝ)..1, Complex.re (Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := by
              refine intervalIntegral.integral_congr fun s _ ↦ ?_
              simpa using (Complex.exp_ofReal_mul_I_re (s * x)).symm
      _ = Complex.re
            (∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := hReInt
      _ = 2 * Real.sinc x := by
            rw [intervalIntegral_exp_mul_compactAverage_local]
            simp
  have hCosCont :
      IntervalIntegrable (fun s : ℝ ↦ Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    -- Proof comment: the real cosine integrand is continuous on the averaging window.
    have hCosCont' : Continuous (fun s : ℝ ↦ Real.cos (s * x)) := by
      simpa using (Real.continuous_cos.comp (continuous_id.mul continuous_const))
    exact hCosCont'.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hSub :
      ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) =
        (∫ s in (-1 : ℝ)..1, (1 : ℝ)) - ∫ s in (-1 : ℝ)..1, Real.cos (s * x) := by
    rw [intervalIntegral.integral_sub (μ := volume) intervalIntegrable_const hCosCont]
  have hConstIntEval : ∫ s in (-1 : ℝ)..1, (1 : ℝ) = 2 := by
    norm_num [intervalIntegral.integral_const]
  calc
    compactAverageKernel x = 1 - Real.sinc x := by
      simp [compactAverageKernel]
    _ = (1 / 2 : ℝ) * (2 - 2 * Real.sinc x) := by ring
    _ = (1 / 2 : ℝ) *
          ((∫ s in (-1 : ℝ)..1, (1 : ℝ)) - ∫ s in (-1 : ℝ)..1, Real.cos (s * x)) := by
            rw [hConstIntEval, hCosInt]
    _ = (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
          rw [← hSub]

/-- Helper for Theorem 16.22: the cosine defect is quadratically bounded above. -/
private lemma one_sub_cos_le_sq_div_two_local (y : ℝ) :
    1 - Real.cos y ≤ y ^ (2 : ℕ) / 2 := by
  -- Proof comment: rearrange the standard quadratic lower bound for `cos`.
  linarith [Real.one_sub_sq_div_two_le_cos (x := y)]

/-- Helper for Theorem 16.22: on `[-1,1]`, the cosine defect is quadratically bounded below by a
uniform multiple of `y²`. -/
private lemma two_div_pi_sq_mul_sq_le_one_sub_cos_local {y : ℝ} (hy : |y| ≤ 1) :
    (2 / Real.pi ^ (2 : ℕ)) * y ^ (2 : ℕ) ≤ 1 - Real.cos y := by
  -- Proof comment: on `[-1, 1]`, Jordan's cosine defect bound is available directly from
  -- `Real.cos_le_one_sub_mul_cos_sq`.
  have hpi : |y| ≤ Real.pi := by
    linarith [hy, Real.pi_gt_three]
  have hcos := Real.cos_le_one_sub_mul_cos_sq (x := y) hpi
  linarith [hcos]

/-- Helper for Theorem 16.22: near `0`, the compact-average kernel is at most a constant multiple
of `x²`. -/
private lemma compactAverageKernel_le_half_sq_local {x : ℝ} (_hx : |x| ≤ 1) :
    compactAverageKernel x ≤ x ^ (2 : ℕ) / 2 := by
  have hDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    -- Proof comment: the compact-average defect is continuous, hence interval-integrable.
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hConstInt :
      IntervalIntegrable (fun _ : ℝ ↦ x ^ (2 : ℕ) / 2) volume (-1 : ℝ) 1 := intervalIntegrable_const
  have hMono :
      ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) ≤
        ∫ s in (-1 : ℝ)..1, (x ^ (2 : ℕ) / 2 : ℝ) := by
    -- Proof comment: on `[-1,1]`, the cosine defect is bounded by `((s x)^2) / 2`, and the
    -- factor `s²` is at most `1`.
    refine intervalIntegral.integral_mono_on (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
      (f := fun s : ℝ ↦ 1 - Real.cos (s * x))
      (g := fun _ : ℝ ↦ x ^ (2 : ℕ) / 2)
      (hab := by norm_num) hDefectInt hConstInt ?_
    intro s hs
    have hsBounds : -1 ≤ s ∧ s ≤ 1 := by
      simpa using hs
    have hsAbs : |s| ≤ 1 := abs_le.mpr hsBounds
    have hDefect := one_sub_cos_le_sq_div_two_local (s * x)
    have hSq :
        (s * x) ^ (2 : ℕ) / 2 ≤ x ^ (2 : ℕ) / 2 := by
      have hsSq : s ^ (2 : ℕ) ≤ 1 := by
        nlinarith [sq_nonneg s, hsAbs]
      calc
        (s * x) ^ (2 : ℕ) / 2 = (s ^ (2 : ℕ) * x ^ (2 : ℕ)) / 2 := by ring
        _ ≤ (1 * x ^ (2 : ℕ)) / 2 := by
              nlinarith [hsSq, sq_nonneg x]
        _ = x ^ (2 : ℕ) / 2 := by ring
    exact hDefect.trans hSq
  calc
    compactAverageKernel x
        = (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
            rw [compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_local]
    _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (x ^ (2 : ℕ) / 2 : ℝ) := by
          gcongr
    _ = x ^ (2 : ℕ) / 2 := by
          rw [intervalIntegral.integral_const]
          norm_num
          ring

/-- Helper for Theorem 16.22: near `0`, the compact-average kernel is bounded below by a fixed
positive multiple of `x²`. -/
private lemma two_div_pi_sq_mul_sq_quarter_le_compactAverageKernel_local {x : ℝ}
    (hx : |x| ≤ 1) :
    x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x := by
  have hDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    -- Proof comment: the compact-average defect is continuous on `[-1,1]`.
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hLowerInt :
      IntervalIntegrable
        (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) volume (-1 : ℝ) 1 := by
    -- Proof comment: the quadratic lower comparison kernel is polynomial, hence continuous.
    have hLowerCont : Continuous (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) := by
      continuity
    exact hLowerCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hMono :
      ∫ s in (-1 : ℝ)..1, (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) ≤
        ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
    -- Proof comment: the lower cosine defect estimate applies because `|s * x| ≤ 1` on the
    -- averaging window whenever `|x| ≤ 1`.
    refine intervalIntegral.integral_mono_on (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
      (f := fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ))
      (g := fun s : ℝ ↦ 1 - Real.cos (s * x))
      (hab := by norm_num) hLowerInt hDefectInt ?_
    intro s hs
    have hsBounds : -1 ≤ s ∧ s ≤ 1 := by
      simpa using hs
    have hsAbs : |s| ≤ 1 := abs_le.mpr hsBounds
    have hsxAbs : |s * x| ≤ 1 := by
      calc
        |s * x| = |s| * |x| := by rw [abs_mul]
        _ ≤ 1 * 1 := by
              gcongr
        _ = 1 := by ring
    simpa using two_div_pi_sq_mul_sq_le_one_sub_cos_local (y := s * x) hsxAbs
  have hSqHalf : (1 / 2 : ℝ) ≤ ∫ s in (-1 : ℝ)..1, s ^ (2 : ℕ) := by
    rw [integral_pow]
    norm_num
  let c : ℝ := (1 / 2 : ℝ) * ((2 / Real.pi ^ (2 : ℕ)) * x ^ (2 : ℕ))
  have hcNonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hFactor := mul_le_mul_of_nonneg_left hSqHalf hcNonneg
  have hLowerBound :
      x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ)) ≤
        (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) := by
    -- Proof comment: `∫_{-1}^1 s² ds ≥ 1 / 2`, and pulling out the constant comparison kernel
    -- converts this into the required lower scalar bound.
    dsimp [c] at hFactor ⊢
    convert hFactor using 1
    · ring
    · rw [show (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) =
          fun s : ℝ ↦ ((2 / Real.pi ^ (2 : ℕ)) * x ^ (2 : ℕ)) * s ^ (2 : ℕ) by
            funext s
            ring]
      rw [intervalIntegral.integral_const_mul]
      ring
  calc
    x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ))
        ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) :=
          hLowerBound
    _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
          gcongr
    _ = compactAverageKernel x := by
          rw [compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_local]

/-- Helper for Theorem 16.22: on the shell `1 ≤ |x| ≤ 2`, the compact-average kernel has a
uniform positive lower bound. -/
private lemma one_div_twelve_pi_sq_le_compactAverageKernel_of_one_le_abs_le_two_local {x : ℝ}
    (hx1 : 1 ≤ |x|) (hx2 : |x| ≤ 2) :
    1 / (12 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x := by
  have hDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    -- Proof comment: the compact-average defect is continuous on the full averaging window.
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hLowerInt :
      IntervalIntegrable
        (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) volume (-1 / 2 : ℝ)
        (1 / 2 : ℝ) := by
    -- Proof comment: the quadratic comparison kernel on the inner shell is polynomial.
    have hLowerCont : Continuous
        (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) := by
      continuity
    exact hLowerCont.intervalIntegrable (μ := volume) (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
  have hSmallDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
    -- Proof comment: the same defect integrand is continuous on the inner shell window.
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
  have hNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 1)] fun s : ℝ ↦ 1 - Real.cos (s * x) := by
    exact Filter.Eventually.of_forall fun s ↦ sub_nonneg.mpr (Real.cos_le_one _)
  have hWindowMono :
      ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (1 - Real.cos (s * x)) ≤
        ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
    exact intervalIntegral.integral_mono_interval
      (μ := volume)
      (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (c := (-1 : ℝ)) (d := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) hNonneg hDefectInt
  have hMono :
      ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) ≤
        ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (1 - Real.cos (s * x)) := by
    -- Proof comment: on `[-1/2, 1/2]` and for `|x| ≤ 2`, the argument `|s * x|` stays within
    -- `[-1, 1]`, so the uniform lower cosine-defect estimate applies pointwise.
    refine intervalIntegral.integral_mono_on (μ := volume)
      (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (f := fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ))
      (g := fun s : ℝ ↦ 1 - Real.cos (s * x))
      (hab := by norm_num) hLowerInt hSmallDefectInt ?_
    intro s hs
    have hsBounds : -(1 / 2 : ℝ) ≤ s ∧ s ≤ 1 / 2 := by
      rcases hs with ⟨hsLeft, hsRight⟩
      constructor <;> linarith
    have hsAbs : |s| ≤ 1 / 2 := abs_le.mpr hsBounds
    have hsxAbs : |s * x| ≤ 1 := by
      calc
        |s * x| = |s| * |x| := by rw [abs_mul]
        _ ≤ (1 / 2 : ℝ) * 2 := by
              gcongr
        _ = 1 := by ring
    simpa using two_div_pi_sq_mul_sq_le_one_sub_cos_local (y := s * x) hsxAbs
  have hLowerEval :
      x ^ (2 : ℕ) / (6 * Real.pi ^ (2 : ℕ)) ≤
        ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) := by
    -- Proof comment: evaluating the inner quadratic comparison integral gives an explicit
    -- multiple of `x²`.
    have hEval :
        ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) =
          x ^ (2 : ℕ) / (6 * Real.pi ^ (2 : ℕ)) := by
      rw [show (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) =
          fun s : ℝ ↦ ((2 / Real.pi ^ (2 : ℕ)) * x ^ (2 : ℕ)) * s ^ (2 : ℕ) by
            funext s
            ring]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      ring_nf
    exact le_of_eq hEval.symm
  have hShell :
      x ^ (2 : ℕ) / (12 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x := by
    calc
      x ^ (2 : ℕ) / (12 * Real.pi ^ (2 : ℕ))
          = (1 / 2 : ℝ) * (x ^ (2 : ℕ) / (6 * Real.pi ^ (2 : ℕ))) := by
              field_simp [Real.pi_ne_zero]
              ring
      _ ≤ (1 / 2 : ℝ) *
              ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_left hLowerEval (by norm_num : 0 ≤ (1 / 2 : ℝ))
      _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (1 - Real.cos (s * x)) := by
            gcongr
      _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
            gcongr
      _ = compactAverageKernel x := by
            rw [compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_local]
  have hxSqOne : 1 ≤ x ^ (2 : ℕ) := by
    have hxSqAbs : 1 ≤ |x| ^ (2 : ℕ) := by
      nlinarith [hx1, abs_nonneg x]
    simpa [sq_abs] using hxSqAbs
  have hOneToSq :
      1 / (12 * Real.pi ^ (2 : ℕ)) ≤ x ^ (2 : ℕ) / (12 * Real.pi ^ (2 : ℕ)) := by
    exact div_le_div_of_nonneg_right hxSqOne (by positivity : 0 ≤ 12 * Real.pi ^ (2 : ℕ))
  exact hOneToSq.trans hShell

/-- Helper for Theorem 16.22: the compact-average kernel globally dominates the canonical
integrand up to one fixed scalar factor. -/
private lemma compactAverageInverseWeightBound_local (x : ℝ) :
    min (x ^ (2 : ℕ)) 1 ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
  by_cases hx1 : |x| ≤ 1
  · have hLower :=
      two_div_pi_sq_mul_sq_quarter_le_compactAverageKernel_local (x := x) hx1
    have hSq :
        x ^ (2 : ℕ) ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
      have hScaled := mul_le_mul_of_nonneg_left hLower (by positivity : 0 ≤ 12 * Real.pi ^ (2 : ℕ))
      calc
        x ^ (2 : ℕ) ≤ 6 * x ^ (2 : ℕ) := by
              nlinarith [sq_nonneg x]
        _ = (12 * Real.pi ^ (2 : ℕ)) * (x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ))) := by
              field_simp [Real.pi_ne_zero]
              ring
        _ ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := hScaled
    exact (min_le_left _ _).trans hSq
  · have hxgt : 1 < |x| := lt_of_not_ge hx1
    by_cases hx2 : |x| ≤ 2
    · have hShell :
          1 / (12 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x :=
        one_div_twelve_pi_sq_le_compactAverageKernel_of_one_le_abs_le_two_local
          (le_of_lt hxgt) hx2
      have hOne :
          1 ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
        have hScaled := mul_le_mul_of_nonneg_left hShell
          (by positivity : 0 ≤ 12 * Real.pi ^ (2 : ℕ))
        calc
          1 = (12 * Real.pi ^ (2 : ℕ)) * (1 / (12 * Real.pi ^ (2 : ℕ))) := by
                field_simp [Real.pi_ne_zero]
          _ ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := hScaled
      exact (min_le_right _ _).trans hOne
    · have hx2' : 2 < |x| := lt_of_not_ge hx2
      have hsincHalf : |Real.sinc x| ≤ 1 / (2 : ℝ) := by
        have hx0 : x ≠ 0 := by
          intro hx0
          rw [hx0] at hx2'
          norm_num at hx2'
        rw [Real.sinc_of_ne_zero hx0, abs_div]
        have hSin : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
        have hxAbsPos : 0 < |x| := abs_pos.mpr hx0
        have hDiv : |Real.sin x| / |x| ≤ 1 / |x| := by
          exact div_le_div_of_nonneg_right hSin hxAbsPos.le
        have hInv : 1 / |x| ≤ 1 / (2 : ℝ) := by
          exact one_div_le_one_div_of_le (by positivity) (le_of_lt hx2')
        exact hDiv.trans hInv
      have hKernelHalf : (1 / 2 : ℝ) ≤ compactAverageKernel x := by
        have hsincLeHalf : Real.sinc x ≤ 1 / (2 : ℝ) := le_trans (le_abs_self _) hsincHalf
        dsimp [compactAverageKernel]
        linarith
      have hOne :
          1 ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
        calc
          1 ≤ 6 * Real.pi ^ (2 : ℕ) := by
                nlinarith [Real.pi_gt_three]
          _ = (12 * Real.pi ^ (2 : ℕ)) * (1 / 2 : ℝ) := by
                ring
          _ ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
                gcongr
      exact (min_le_right _ _).trans hOne

/-
/-- Helper for Theorem 16.22: same-law Lévy--Khintchin representations determine the Gaussian
coefficient and Lévy measure. -/
private lemma sigma2_levyMeasure_eq_of_sameRepresentation
    {μ : ProbabilityMeasure ℝ} {τ₁ τ₂ : LevyKhinchinTriple}
    (hτ₁ : HasLevyKhinchinRepresentation μ τ₁)
    (hτ₂ : HasLevyKhinchinRepresentation μ τ₂) :
    τ₁.sigma2 = τ₂.sigma2 ∧ τ₁.ν = τ₂.ν := by
  -- Route correction: the old blocker asked for full triple equality, but the downstream Gaussian
  -- and Lévy-scaling lemmas only consume the `sigma2` and `ν` projections.
  have hExp :
      ∀ t : ℝ, levyKhinchinExponent τ₁ t = levyKhinchinExponent τ₂ t :=
    levyKhinchinExponent_eq_of_sameRepresentation_of_continuous
      hτ₁
      hτ₂
      (continuousLevyKhinchinExponentLocal hτ₁.isCanonicalTriple)
      (continuousLevyKhinchinExponentLocal hτ₂.isCanonicalTriple)
  let α₁ : NNReal := ⟨τ₁.sigma2 / 2, by positivity⟩
  let α₂ : NNReal := ⟨τ₂.sigma2 / 2, by positivity⟩
  have hAuxEq :
      gaussianRecoveryAuxFiniteMeasure α₁ τ₁.ν
          (integrable_gaussianRecoveryKernel hτ₁.isCanonicalTriple.isCanonicalMeasure) =
        gaussianRecoveryAuxFiniteMeasure α₂ τ₂.ν
          (integrable_gaussianRecoveryKernel hτ₂.isCanonicalTriple.isCanonicalMeasure) := by
    simpa [α₁, α₂] using
      gaussianRecoveryAuxFiniteMeasure_eq_of_exponentEq
        hτ₁.isCanonicalTriple hτ₂.isCanonicalTriple hExp
  have hAlpha :
      (α₁ : ENNReal) = α₂ := by
    have hZero :=
      congrArg
        (fun ν : FiniteMeasure ℝ ↦ ((ν : Measure ℝ) ({0} : Set ℝ)))
        hAuxEq
    simpa [gaussianRecoveryAuxFiniteMeasure_apply_zero] using hZero
  have hSigmaHalf : τ₁.sigma2 / 2 = τ₂.sigma2 / 2 := by
    exact_mod_cast congrArg (fun a : NNReal ↦ (a : ℝ)) hAlpha
  have hSigma : τ₁.sigma2 = τ₂.sigma2 := by
    linarith
  have hTiltRestrict :
      ((τ₁.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
          (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) =
        ((τ₂.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
          (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) := by
    have hRestrict :=
      congrArg
        (fun ν : FiniteMeasure ℝ ↦ ((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ)))
        hAuxEq
    change
      ((((α₁ : ENNReal) • Measure.dirac 0 +
          τ₁.ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).restrict
          ({0}ᶜ : Set ℝ))) =
        ((((α₂ : ENNReal) • Measure.dirac 0 +
          τ₂.ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).restrict
          ({0}ᶜ : Set ℝ))) at hRestrict
    rw [Measure.restrict_add, Measure.restrict_smul,
      Measure.restrict_dirac' ((measurableSet_singleton (0 : ℝ)).compl), if_neg (by simp),
      smul_zero, zero_add, MeasureTheory.restrict_withDensity
        ((measurableSet_singleton (0 : ℝ)).compl),
      Measure.restrict_add, Measure.restrict_smul,
      Measure.restrict_dirac' ((measurableSet_singleton (0 : ℝ)).compl), if_neg (by simp),
      smul_zero, zero_add, MeasureTheory.restrict_withDensity
        ((measurableSet_singleton (0 : ℝ)).compl)] at hRestrict
    exact hRestrict
  have hNuRestrict :
      τ₁.ν.restrict ({0}ᶜ : Set ℝ) = τ₂.ν.restrict ({0}ᶜ : Set ℝ) := by
    have hInv :=
      congrArg
        (fun η : Measure ℝ ↦
          η.withDensity (fun x ↦ (ENNReal.ofReal (gaussianRecoveryKernel x))⁻¹))
        hTiltRestrict
    -- Proof comment: on `{0}ᶜ`, the Gaussian recovery density is strictly positive, so a second
    -- `withDensity` by its inverse removes the tilt and recovers the punctured jump measure.
    calc
      τ₁.ν.restrict ({0}ᶜ : Set ℝ) =
          (((τ₁.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
              (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).withDensity
            (fun x ↦ (ENNReal.ofReal (gaussianRecoveryKernel x))⁻¹)) := by
              symm
              exact
                withDensity_gaussianRecoveryKernel_inv_same_restrict_compl_singleton τ₁.ν
      _ =
          (((τ₂.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
              (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).withDensity
            (fun x ↦ (ENNReal.ofReal (gaussianRecoveryKernel x))⁻¹)) := hInv
      _ = τ₂.ν.restrict ({0}ᶜ : Set ℝ) := by
            exact
              withDensity_gaussianRecoveryKernel_inv_same_restrict_compl_singleton τ₂.ν
  have hNu : τ₁.ν = τ₂.ν := by
    rw [← Measure.restrict_add_restrict_compl (μ := τ₁.ν) (measurableSet_singleton (0 : ℝ)),
      ← Measure.restrict_add_restrict_compl (μ := τ₂.ν) (measurableSet_singleton (0 : ℝ))]
    congr 1
    · rw [Measure.restrict_singleton, hτ₁.isCanonicalTriple.isCanonicalMeasure.measure_singleton_zero,
        zero_smul, Measure.restrict_singleton,
      hτ₂.isCanonicalTriple.isCanonicalMeasure.measure_singleton_zero, zero_smul]
    · simpa [Set.compl_compl] using hNuRestrict
  exact ⟨hSigma, hNu⟩

-/

/-- Helper for Theorem 16.22: a Dirac law is represented by the zero-jump, zero-Gaussian
canonical triple with drift equal to the atom location. -/
private lemma hasLevyKhinchinRepresentation_dirac_local (b : ℝ) :
    HasLevyKhinchinRepresentation (diracProba b)
      { sigma2 := 0, b := b, ν := (0 : Measure ℝ) } := by
  constructor
  · -- Proof comment: the zero measure is canonical and the Gaussian coefficient is already `0`.
    infer_instance
  · intro t
    have hInner : inner ℝ b t = b * t := by
      simpa using (RCLike.inner_apply' (𝕜 := ℝ) b t)
    -- Proof comment: with vanishing Gaussian and jump terms, the exponent is exactly the phase of
    -- the Dirac mass at `b`.
    simpa [MeasureTheory.diracProba, MeasureTheory.charFun_dirac, hInner,
      levyKhinchinExponent, levyKhinchinExponentWithCentering, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 16.22: an exact positive-integer root family already yields infinite
divisibility; the normalized logarithmic lift is auxiliary context for the later existence step. -/
private lemma isInfinitelyDivisible_of_exactRoots_and_expLift_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    IsInfinitelyDivisible μ := by
  let _ := hΨ0
  let _ := hΨexp
  -- Proof comment: the lift data is not needed to prove infinite divisibility itself; the exact
  -- root family already matches the owner definition.
  exact isInfinitelyDivisible_of_exactRootFamily_local (μ := μ) μroot hroot

/-- Helper for Theorem 16.22: an exact positive-integer root family already gives the normalized
continuous exponential lift needed by the exact-root existence route. -/
private lemma continuousExpLift_of_exactRootFamily_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ) :
    ∃ Ψ : C(ℝ, ℂ), Ψ 0 = 0 ∧ ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t := by
  have hInf : IsInfinitelyDivisible μ :=
    isInfinitelyDivisible_of_exactRootFamily_local (μ := μ) μroot hroot
  -- Proof comment: after extracting infinite divisibility from the exact roots, the standard
  -- continuous-lift package supplies the normalized logarithm of the characteristic function.
  exact continuousExpLift_of_isInfinitelyDivisible_local hInf

/-- Helper for Theorem 16.22: the Dirac branch of the exact-root existence problem is already
handled by the explicit zero-jump, zero-Gaussian Lévy--Khintchin triple. -/
private lemma levyKhinchinTriple_exists_of_eq_dirac_local
    {μ : ProbabilityMeasure ℝ}
    (hDirac : ∃ b : ℝ, μ = diracProba b) :
    ∃ τ : LevyKhinchinTriple, HasLevyKhinchinRepresentation μ τ := by
  rcases hDirac with ⟨b, rfl⟩
  -- Proof comment: for a Dirac mass, the explicit drift-only triple already gives the full
  -- Lévy--Khintchin representation.
  exact ⟨{ sigma2 := 0, b := b, ν := (0 : Measure ℝ) }, hasLevyKhinchinRepresentation_dirac_local b⟩

/-- Helper for Theorem 16.22: exposing the compact-average `withDensity` factor turns the
auxiliary characteristic function back into the original Fourier kernel multiplied by
`compactAverageKernel`. -/
private lemma compactAverageWeightedFourierIntegral_eq_local
    {ν : Measure ℝ} (t : ℝ) :
    ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
        ∂ν.withDensity (fun x ↦ ENNReal.ofReal (compactAverageKernel x)) =
      ∫ x : ℝ,
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * compactAverageKernel x ∂ν := by
  -- Proof comment: `withDensity` contributes the real scalar
  -- `ENNReal.toReal (ofReal (compactAverageKernel x))`, which is exactly
  -- `compactAverageKernel x` because the kernel is nonnegative.
  rw [integral_withDensity_eq_integral_toReal_smul measurable_compactAverageKernel.ennreal_ofReal
    (by
      filter_upwards [compactAverageKernel_ae_ne_top (ν := ν)] with x hx
      exact lt_of_le_of_ne le_top hx)]
  refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
  have htoReal :
      ENNReal.toReal (ENNReal.ofReal (compactAverageKernel x)) = compactAverageKernel x := by
    simp [compactAverageKernel_nonneg x]
  calc
    ENNReal.toReal (ENNReal.ofReal (compactAverageKernel x)) •
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) =
      (((compactAverageKernel x : ℝ) : ℂ)) *
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := by
          simpa [Algebra.smul_def, htoReal]
    _ =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * (((compactAverageKernel x : ℝ) : ℂ)) := by
        ring

/-- Helper for Theorem 16.22: the compact-average exact-root auxiliary finite measure has
characteristic function equal to the compact-averaged exact-root exponent. -/
private lemma exactRootApproxCompactAverageMeasure_charFun_eq_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    charFun ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t =
      levyKhinchinExponent (exactRootApproxTriple μroot n) t -
        ((1 / 2 : ℂ) *
          ∫ s in (-1 : ℝ)..1, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  letI : IsFiniteMeasure ν := by
    change IsFiniteMeasure (((exactRootApproxIntensity μroot n : FiniteMeasure ℝ) : Measure ℝ))
    infer_instance
  have hFourier :
      Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) ν :=
    integrable_fourierKernel_of_isFiniteMeasure ν t
  have hRaw :
      Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ν :=
    integrable_compoundPoissonKernel_of_isFiniteMeasure ν t
  letI : IsFiniteMeasure (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    refine ⟨?_⟩
    simpa [Set.uIoc, min_eq_left (show (-1 : ℝ) ≤ 1 by norm_num),
      max_eq_right (show (-1 : ℝ) ≤ 1 by norm_num), Real.volume_Ioc] using
      (show volume (Set.Ioc (-1 : ℝ) 1) < ⊤ by norm_num [Real.volume_Ioc])
  letI : IsFiniteMeasure ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν) := by
    infer_instance
  have hShiftProdIntegrable :
      Integrable
        (Function.uncurry fun s x : ℝ ↦
          Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)))
        ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν) := by
    have hCont :
        Continuous fun p : ℝ × ℝ ↦
          Complex.exp (((((t + p.1) * p.2 : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    refine
      (integrable_const
        (μ := ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν))
        (1 : ℝ)).mono' ?_ ?_
    · simpa [Function.uncurry] using hCont.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun p ↦ by
        simpa [Function.uncurry] using
          (le_of_eq (Complex.norm_exp_ofReal_mul_I ((t + p.1) * p.2)))
  have hShiftIntervalCont :
      Continuous fun x : ℝ ↦
        ∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) := by
    have hUncurry :
        Continuous (Function.uncurry fun x s : ℝ ↦
          Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) := by
      fun_prop
    simpa [Function.uncurry] using
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume)
        (f := fun x s : ℝ ↦ Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)))
        hUncurry (-1 : ℝ) 1)
  have hShiftIntervalIntegrable :
      Integrable
        (fun x : ℝ ↦
          ∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) ν := by
    refine (integrable_const (2 : ℝ)).mono' hShiftIntervalCont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      have hNorm :
          ‖∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))‖ ≤
            (1 : ℝ) * |(1 : ℝ) - (-1 : ℝ)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        intro s hs
        simpa using (le_of_eq (Complex.norm_exp_ofReal_mul_I ((t + s) * x)))
      have hNorm' :
          ‖∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))‖ ≤ 2 := by
        calc
          ‖∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))‖ ≤
              (1 : ℝ) * |(1 : ℝ) - (-1 : ℝ)| := hNorm
          _ = 2 := by norm_num
      simpa using hNorm'
  have hShiftFactor :
      ∀ x : ℝ,
        ∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) =
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
            ∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by
    intro x
    calc
      ∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) =
          ∫ s in (-1 : ℝ)..1,
            Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by
              refine intervalIntegral.integral_congr fun s _ ↦ ?_
              have hArg :
                  (((((t + s) * x : ℝ) : ℂ) * Complex.I)) =
                    ((((t * x : ℝ) : ℂ) + (((s * x : ℝ) : ℂ))) * Complex.I) := by
                    calc
                      (((((t + s) * x : ℝ) : ℂ) * Complex.I)) =
                          ((((t * x + s * x : ℝ) : ℂ)) * Complex.I) := by
                            congr 1
                            ring
                      _ = ((((t * x : ℝ) : ℂ) + (((s * x : ℝ) : ℂ))) * Complex.I) := by
                            simp
              rw [hArg, add_mul, Complex.exp_add]
      _ =
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
            ∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by
              exact
                intervalIntegral.integral_const_mul
                  (a := (-1 : ℝ))
                  (b := (1 : ℝ))
                  (r := Complex.exp (((t * x : ℝ) : ℂ) * Complex.I))
                  (f := fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I))
  have hPointwise :
      ∀ x : ℝ,
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * compactAverageKernel x =
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
            ((1 / 2 : ℂ) *
              ∫ s in (-1 : ℝ)..1,
                Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) := by
    intro x
    calc
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * compactAverageKernel x =
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * (1 - Real.sinc x) := by
            simp [compactAverageKernel]
      _ =
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * (Real.sinc x : ℂ)) := by
              ring
      _ =
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
            ((1 / 2 : ℂ) *
              ∫ s in (-1 : ℝ)..1,
                Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) := by
              rw [hShiftFactor x, intervalIntegral_exp_mul_compactAverage_local]
              ring
  have hExpEq :
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂ν =
        levyKhinchinExponent (exactRootApproxTriple μroot n) t +
          ∫ x : ℝ, (1 : ℂ) ∂ν := by
    -- Proof comment: for the finite exact-root jump intensity, the raw oscillatory integral is the
    -- exact-root exponent plus the constant `1` contribution.
    calc
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂ν =
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) + (1 : ℂ) ∂ν := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
              ring
      _ =
          ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν +
            ∫ x : ℝ, (1 : ℂ) ∂ν := by
              rw [integral_add hRaw (integrable_const (1 : ℂ))]
      _ =
          levyKhinchinExponent (exactRootApproxTriple μroot n) t +
            ∫ x : ℝ, (1 : ℂ) ∂ν := by
              rw [exactRootApproxExponent_eq_rawKernelIntegral_local]
  have hExpEqShift :
      ∀ s : ℝ,
        ∫ x : ℝ, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) ∂ν =
          levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) +
            ∫ x : ℝ, (1 : ℂ) ∂ν := by
    intro s
    have hRawShift :
        Integrable (fun x : ℝ ↦ Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) - 1) ν :=
      integrable_compoundPoissonKernel_of_isFiniteMeasure ν (t + s)
    calc
      ∫ x : ℝ, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) ∂ν =
          ∫ x : ℝ,
            (Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) - 1) + (1 : ℂ) ∂ν := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
              ring
      _ =
          ∫ x : ℝ, (Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) - 1) ∂ν +
            ∫ x : ℝ, (1 : ℂ) ∂ν := by
              rw [integral_add hRawShift (integrable_const (1 : ℂ))]
      _ =
          levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) +
            ∫ x : ℝ, (1 : ℂ) ∂ν := by
              rw [exactRootApproxExponent_eq_rawKernelIntegral_local]
  have hApproxIntervalIntegrable :
      IntervalIntegrable
        (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
        volume (-1 : ℝ) 1 := by
    have hCont :
        Continuous (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) := by
      exact
        (continuousLevyKhinchinExponentLocal
          (exactRootApproxTriple_hasLevyKhinchinRepresentation_local μroot n).isCanonicalTriple).comp
          (continuous_const.add continuous_id)
    exact hCont.intervalIntegrable (μ := volume) (-1 : ℝ) 1
  -- Proof comment: the compact-average kernel inserts a fixed interval average of the Fourier
  -- phase, so the weighted exact-root characteristic function is exactly the compact-averaged
  -- exact-root exponent.
  calc
    charFun ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t =
        ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * compactAverageKernel x ∂ν := by
          rw [MeasureTheory.charFun_apply_real]
          simpa [ν, exactRootApproxCompactAverageMeasure] using
            compactAverageWeightedFourierIntegral_eq_local (ν := ν) t
    _ =
        ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂ν -
          ∫ x : ℝ,
            ((1 / 2 : ℂ) *
              ∫ s in (-1 : ℝ)..1,
                Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) ∂ν := by
          refine (integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ hPointwise x).trans ?_
          rw [integral_sub hFourier (hShiftIntervalIntegrable.const_mul (1 / 2 : ℂ))]
    _ =
        ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂ν -
          ((1 / 2 : ℂ) *
            ∫ s in (-1 : ℝ)..1,
              ∫ x : ℝ, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) ∂ν) := by
          congr 1
          exact shiftedFourierCompactAverageBridge_local (ν := ν) t hShiftProdIntegrable
    _ =
        (levyKhinchinExponent (exactRootApproxTriple μroot n) t +
            ∫ x : ℝ, (1 : ℂ) ∂ν) -
          ((1 / 2 : ℂ) *
            ∫ s in (-1 : ℝ)..1,
              (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) +
                ∫ x : ℝ, (1 : ℂ) ∂ν)) := by
          rw [hExpEq]
          congr 1
          exact congrArg
            (fun z : ℂ ↦ ((1 / 2 : ℂ) * z))
            (intervalIntegral.integral_congr fun s _ ↦ by
              rw [hExpEqShift s])
    _ =
        (levyKhinchinExponent (exactRootApproxTriple μroot n) t +
            ∫ x : ℝ, (1 : ℂ) ∂ν) -
          ((1 / 2 : ℂ) *
            ((∫ s in (-1 : ℝ)..1,
                levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) +
              ∫ s in (-1 : ℝ)..1, (∫ x : ℝ, (1 : ℂ) ∂ν))) := by
          rw [intervalIntegral.integral_add hApproxIntervalIntegrable intervalIntegrable_const]
    _ =
        levyKhinchinExponent (exactRootApproxTriple μroot n) t -
          ((1 / 2 : ℂ) *
            ∫ s in (-1 : ℝ)..1,
              levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) := by
          have hrealOne : (ν.real Set.univ : ℂ) = ν.real Set.univ • (1 : ℂ) := by
            simp
          have hConstInt : ∫ x : ℝ, (1 : ℂ) ∂ν = (ν.real Set.univ : ℂ) := by
            rw [integral_const]
            exact hrealOne.symm
          set A : ℂ :=
            ∫ s in (-1 : ℝ)..1, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
          rw [intervalIntegral.integral_const, hConstInt]
          have hLength :
              ((1 - -1 : ℝ) • (ν.real Set.univ : ℂ)) = (2 : ℂ) * (ν.real Set.univ : ℂ) := by
            norm_num [smul_eq_mul]
          calc
            levyKhinchinExponent (exactRootApproxTriple μroot n) t + (ν.real Set.univ : ℂ) -
                ((1 / 2 : ℂ) * (A + ((1 - -1 : ℝ) • (ν.real Set.univ : ℂ)))) =
              levyKhinchinExponent (exactRootApproxTriple μroot n) t + (ν.real Set.univ : ℂ) -
                ((1 / 2 : ℂ) * (A + (2 : ℂ) * (ν.real Set.univ : ℂ))) := by
                  rw [hLength]
            _ =
              levyKhinchinExponent (exactRootApproxTriple μroot n) t - ((1 / 2 : ℂ) * A) := by
                ring

/-- Helper for Theorem 16.22: evaluating the compact-average exact-root auxiliary characteristic
function at `0` identifies the complex mass limit needed for the finite-measure existence step. -/
private lemma exactRootApproxCompactAverageMass_tendsto_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    Tendsto
      (fun n : ℕ ↦ (((exactRootApproxCompactAverageMeasure μroot n).mass : NNReal) : ℂ))
      atTop
      (𝓝 ((compactAverageExpLift Ψ) 0)) := by
  have hChar :
      Tendsto
        (fun n : ℕ ↦
          charFun ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) 0)
        atTop
        (𝓝 ((compactAverageExpLift Ψ) 0)) := by
    refine
      (exactRootApproxCompactAverageExponent_tendsto_local
        (μ := μ) μroot hroot hΨ0 hΨexp 0).congr' ?_
    filter_upwards [] with n
    symm
    exact exactRootApproxCompactAverageMeasure_charFun_eq_local μroot n 0
  -- Proof comment: at zero frequency, the characteristic function of a finite measure is its
  -- total mass.
  refine hChar.congr' ?_
  filter_upwards [] with n
  rw [charFun_finiteMeasure_zero_eq_mass_local]

/-- Helper for Theorem 16.22: the compact-averaged lift takes a real value at `0` because it is
the limit of finite-measure masses. -/
private lemma compactAverageExpLift_zero_im_eq_zero_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    Complex.im ((compactAverageExpLift Ψ) 0) = 0 := by
  have him :
      Tendsto
        (fun n : ℕ ↦ Complex.im ((((exactRootApproxCompactAverageMeasure μroot n).mass : NNReal) : ℂ)))
        atTop
        (𝓝 (Complex.im ((compactAverageExpLift Ψ) 0))) :=
    (Complex.continuous_im.continuousAt.tendsto.comp <|
      exactRootApproxCompactAverageMass_tendsto_local (μ := μ) μroot hroot hΨ0 hΨexp)
  have hzero :
      Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 (Complex.im ((compactAverageExpLift Ψ) 0))) := by
    simpa using him
  exact tendsto_nhds_unique hzero tendsto_const_nhds

/-- Helper for Theorem 16.22: the compact-average auxiliary masses converge in `NNReal` to the
real part of the zero-frequency compact-average lift. -/
private lemma exactRootApproxCompactAverageMass_tendsto_nnreal_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    Tendsto
      (fun n : ℕ ↦ (exactRootApproxCompactAverageMeasure μroot n).mass)
      atTop
      (𝓝 (Real.toNNReal (Complex.re ((compactAverageExpLift Ψ) 0)))) := by
  have hRe :
      Tendsto
        (fun n : ℕ ↦ ((exactRootApproxCompactAverageMeasure μroot n).mass : ℝ))
        atTop
        (𝓝 (Complex.re ((compactAverageExpLift Ψ) 0))) := by
    -- Proof comment: take real parts of the existing complex mass limit.
    simpa using
      (Complex.continuous_re.continuousAt.tendsto.comp
        (exactRootApproxCompactAverageMass_tendsto_local
          (μ := μ) μroot hroot hΨ0 hΨexp))
  -- Proof comment: applying `Real.toNNReal` to the real-valued mass limit rewrites the source
  -- sequence back to the original `NNReal` masses.
  refine ((continuous_real_toNNReal.tendsto _).comp hRe).congr' ?_
  filter_upwards [] with n
  simp

/-- Helper for Theorem 16.22: on the non-Dirac branch, the compact-average characteristic-function
surface is realized by an auxiliary finite measure. -/
private lemma exists_compactAverageAuxFiniteMeasure_of_exactRoots_nonDirac_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (hDirac : ¬ ∃ b : ℝ, μ = diracProba b) :
    ∃ η : FiniteMeasure ℝ,
      ∀ t : ℝ,
        charFun ((η : FiniteMeasure ℝ) : Measure ℝ) t = (compactAverageExpLift Ψ) t := by
  let m : NNReal := Real.toNNReal (Complex.re ((compactAverageExpLift Ψ) 0))
  have hmass :
      Tendsto
        (fun n : ℕ ↦ (exactRootApproxCompactAverageMeasure μroot n).mass)
        atTop
        (𝓝 m) := by
    simpa [m] using
      exactRootApproxCompactAverageMass_tendsto_nnreal_local
        (μ := μ) μroot hroot hΨ0 hΨexp
  have hmPos : 0 < m := by
    -- Proof comment: compact averaging preserves strictly positive zero-frequency mass away from
    -- Dirac laws.
    dsimp [m]
    exact Real.toNNReal_pos.mpr
      (compactAverageLiftZero_pos_of_notDirac_local hΨ0 hΨexp hDirac)
  have hchar :
      ∀ t : ℝ,
        Tendsto
          (fun n : ℕ ↦
            charFun ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) :
              Measure ℝ) t)
          atTop
          (𝓝 ((compactAverageExpLift Ψ) t)) := by
    intro t
    refine
      (exactRootApproxCompactAverageExponent_tendsto_local
        (μ := μ) μroot hroot hΨ0 hΨexp t).congr' ?_
    filter_upwards [] with n
    symm
    exact exactRootApproxCompactAverageMeasure_charFun_eq_local μroot n t
  have hcont :
      ContinuousAt
        (fun t : ℝ ↦ (((m⁻¹ : NNReal) : ℂ)) * (compactAverageExpLift Ψ t))
        0 := by
    -- Proof comment: scaling the continuous compact-average lift by the fixed inverse mass keeps
    -- continuity at the origin.
    simpa using
      ((continuous_const.mul (compactAverageExpLift Ψ).continuous).continuousAt : ContinuousAt
        (fun t : ℝ ↦ (((m⁻¹ : NNReal) : ℂ)) * (compactAverageExpLift Ψ t)) 0)
  exact
    exists_auxFiniteMeasure_of_tendsto_charFun_local
      (ηs := fun n ↦ exactRootApproxCompactAverageMeasure μroot n)
      (Φ := fun t ↦ (compactAverageExpLift Ψ) t)
      (m := m)
      hmass
      (ne_of_gt hmPos)
      hchar
      hcont

/-- Helper for Theorem 16.22: on the non-Dirac branch, keep both the limiting compact-average
auxiliary finite measure and the normalized weak limit that produces it. -/
private lemma exists_compactAverageAuxFiniteMeasure_with_limit_of_exactRoots_nonDirac_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (hDirac : ¬ ∃ b : ℝ, μ = diracProba b) :
    ∃ ρ : ProbabilityMeasure ℝ, ∃ η : FiniteMeasure ℝ,
      η = (Real.toNNReal (Complex.re ((compactAverageExpLift Ψ) 0))) • ρ.toFiniteMeasure ∧
      (∀ t : ℝ, charFun ((η : FiniteMeasure ℝ) : Measure ℝ) t = (compactAverageExpLift Ψ) t) ∧
      Tendsto (fun n : ℕ ↦ (exactRootApproxCompactAverageMeasure μroot n).normalize) atTop (𝓝 ρ) := by
  let m : NNReal := Real.toNNReal (Complex.re ((compactAverageExpLift Ψ) 0))
  have hmass :
      Tendsto
        (fun n : ℕ ↦ (exactRootApproxCompactAverageMeasure μroot n).mass)
        atTop
        (𝓝 m) := by
    simpa [m] using
      exactRootApproxCompactAverageMass_tendsto_nnreal_local
        (μ := μ) μroot hroot hΨ0 hΨexp
  have hmPos : 0 < m := by
    -- Proof comment: away from Dirac laws, compact averaging leaves strictly positive mass at
    -- zero frequency.
    dsimp [m]
    exact Real.toNNReal_pos.mpr
      (compactAverageLiftZero_pos_of_notDirac_local hΨ0 hΨexp hDirac)
  have hchar :
      ∀ t : ℝ,
        Tendsto
          (fun n : ℕ ↦
            charFun ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) :
              Measure ℝ) t)
          atTop
          (𝓝 ((compactAverageExpLift Ψ) t)) := by
    intro t
    -- Proof comment: the repaired exact-root compact-average characteristic-function bridge
    -- identifies the pointwise limit surface.
    refine
      (exactRootApproxCompactAverageExponent_tendsto_local
        (μ := μ) μroot hroot hΨ0 hΨexp t).congr' ?_
    filter_upwards [] with n
    symm
    exact exactRootApproxCompactAverageMeasure_charFun_eq_local μroot n t
  have hcont :
      ContinuousAt
        (fun t : ℝ ↦ (((m⁻¹ : NNReal) : ℂ)) * (compactAverageExpLift Ψ t))
        0 := by
    -- Proof comment: the normalized compact-average lift is still continuous at the origin.
    simpa using
      ((continuous_const.mul (compactAverageExpLift Ψ).continuous).continuousAt : ContinuousAt
        (fun t : ℝ ↦ (((m⁻¹ : NNReal) : ℂ)) * (compactAverageExpLift Ψ t)) 0)
  -- Proof comment: the general finite-measure Lévy continuity package already returns the
  -- limiting law, the reconstructed finite measure, and the normalized weak convergence data.
  simpa [m] using
    (exists_auxFiniteMeasure_with_normalizedLimit_of_tendsto_charFun_local
      (ηs := fun n ↦ exactRootApproxCompactAverageMeasure μroot n)
      (Φ := fun t ↦ (compactAverageExpLift Ψ) t)
      (m := m)
      hmass
      (ne_of_gt hmPos)
      hchar
      hcont)

/-- Helper for Theorem 16.22: any nonzero finite measure is its total mass times the normalized
probability measure, so every complex integral factors accordingly. -/
private lemma integral_eq_mass_mul_integral_normalize_local
    (η : FiniteMeasure ℝ) (hmass : η ≠ 0) (f : ℝ → ℂ) :
    ∫ x : ℝ, f x ∂(η : Measure ℝ) =
      ((η.mass : NNReal) : ℂ) * ∫ x : ℝ, f x ∂(η.normalize : Measure ℝ) := by
  have hmass' : η.mass ≠ 0 := (FiniteMeasure.mass_nonzero_iff η).2 hmass
  have hNormalize :
      ∫ x : ℝ, f x ∂(η.normalize : Measure ℝ) =
        (((η.mass)⁻¹ : NNReal) : ℂ) * ∫ x : ℝ, f x ∂(η : Measure ℝ) := by
    rw [η.toMeasure_normalize_eq_of_nonzero hmass]
    change
      ∫ x : ℝ, f x ∂((((η.mass⁻¹ : NNReal) : ENNReal) • (η : Measure ℝ))) =
        (((η.mass⁻¹ : NNReal) : ℂ)) * ∫ x : ℝ, f x ∂(η : Measure ℝ)
    rw [integral_smul_measure]
    rfl
  have hmassC : (((η.mass : NNReal) : ℂ) * (((η.mass⁻¹ : NNReal) : ℂ))) = 1 := by
    have hmassCne : (((η.mass : NNReal) : ℂ)) ≠ 0 := by
      exact_mod_cast hmass'
    simpa using (mul_inv_cancel₀ hmassCne)
  calc
    ∫ x : ℝ, f x ∂(η : Measure ℝ)
        = 1 * ∫ x : ℝ, f x ∂(η : Measure ℝ) := by ring
    _ = (((η.mass : NNReal) : ℂ) * (((η.mass)⁻¹ : NNReal) : ℂ)) *
          ∫ x : ℝ, f x ∂(η : Measure ℝ) := by rw [hmassC]
    _ = ((η.mass : NNReal) : ℂ) *
          ((((η.mass)⁻¹ : NNReal) : ℂ) * ∫ x : ℝ, f x ∂(η : Measure ℝ)) := by ring
    _ = ((η.mass : NNReal) : ℂ) * ∫ x : ℝ, f x ∂(η.normalize : Measure ℝ) := by
          rw [hNormalize]

/-- Helper for Theorem 16.22: scaling a probability law by a finite mass scales every complex
integral by the same scalar. -/
private lemma integral_mass_smul_probability_local
    (m : NNReal) (ρ : ProbabilityMeasure ℝ) (f : ℝ → ℂ) :
    ∫ x : ℝ, f x ∂(((m • ρ.toFiniteMeasure : FiniteMeasure ℝ) : Measure ℝ)) =
      (m : ℂ) * ∫ x : ℝ, f x ∂(ρ : Measure ℝ) := by
  simpa [FiniteMeasure.toMeasure_smul, Algebra.smul_def] using
    (integral_smul_measure
      (μ := ((ρ.toFiniteMeasure : FiniteMeasure ℝ) : Measure ℝ))
      (c := m) (f := f))

/-- Helper for Theorem 16.22: bounded-continuous weak convergence of the normalized compact-average
auxiliary laws transports the reconstruction-kernel integrals to the limiting finite measure. -/
private lemma tendsto_integral_compactAverageReconstructionKernel_exactRootApprox_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (hMassPos : 0 < Complex.re ((compactAverageExpLift Ψ) 0))
    {ρ : ProbabilityMeasure ℝ} {η : FiniteMeasure ℝ}
    (hηeq : η = (Real.toNNReal (Complex.re ((compactAverageExpLift Ψ) 0))) • ρ.toFiniteMeasure)
    (hnormTendsto : Tendsto (fun n : ℕ ↦ (exactRootApproxCompactAverageMeasure μroot n).normalize)
      atTop (𝓝 ρ))
    (t : ℝ) :
    Tendsto
      (fun n : ℕ ↦
        ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
          ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ))
      atTop
      (𝓝 (∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(η : Measure ℝ))) := by
  let C : ℝ := (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) + 3 * t ^ (2 : ℕ)
  let f_t : BoundedContinuousFunction ℝ ℂ :=
    BoundedContinuousFunction.mkOfBound
      ⟨compactAverageReconstructionKernel_local t,
        continuous_compactAverageReconstructionKernel_local t⟩
      (2 * C)
      (fun x y ↦ by
        calc
          dist (compactAverageReconstructionKernel_local t x)
              (compactAverageReconstructionKernel_local t y)
              ≤ ‖compactAverageReconstructionKernel_local t x‖ +
                  ‖compactAverageReconstructionKernel_local t y‖ := by
                    simpa [dist_eq_norm, sub_eq_add_neg] using
                      (norm_sub_le
                        (compactAverageReconstructionKernel_local t x)
                        (compactAverageReconstructionKernel_local t y))
          _ ≤ C + C := by
                gcongr <;> simpa [C] using norm_compactAverageReconstructionKernel_local_le t _
          _ = 2 * C := by ring)
  let m : NNReal := Real.toNNReal (Complex.re ((compactAverageExpLift Ψ) 0))
  have hmPos : 0 < m := Real.toNNReal_pos.mpr hMassPos
  have hNormIntegral :
      Tendsto
        (fun n : ℕ ↦
          ∫ x : ℝ, f_t x ∂((exactRootApproxCompactAverageMeasure μroot n).normalize : Measure ℝ))
        atTop
        (𝓝 (∫ x : ℝ, f_t x ∂(ρ : Measure ℝ))) := by
    exact
      (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1
        hnormTendsto f_t
  have hMassTendsto :
      Tendsto
        (fun n : ℕ ↦ (((exactRootApproxCompactAverageMeasure μroot n).mass : NNReal) : ℂ))
        atTop
        (𝓝 (m : ℂ)) := by
    exact
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (NNReal.continuous_coe.continuousAt.tendsto.comp
          (exactRootApproxCompactAverageMass_tendsto_nnreal_local
            (μ := μ) μroot hroot hΨ0 hΨexp)))
  have hApproxEventuallyNonzero :
      ∀ᶠ n : ℕ in atTop, exactRootApproxCompactAverageMeasure μroot n ≠ 0 := by
    filter_upwards
      [(exactRootApproxCompactAverageMass_tendsto_nnreal_local
        (μ := μ) μroot hroot hΨ0 hΨexp) (Ioi_mem_nhds hmPos)] with n hn
    exact (FiniteMeasure.mass_nonzero_iff (exactRootApproxCompactAverageMeasure μroot n)).1
      (ne_of_gt hn)
  have hApproxEq :
      (fun n : ℕ ↦
        ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
          ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ)) =ᶠ[atTop]
      (fun n : ℕ ↦
        (((exactRootApproxCompactAverageMeasure μroot n).mass : NNReal) : ℂ) *
          ∫ x : ℝ, f_t x ∂((exactRootApproxCompactAverageMeasure μroot n).normalize : Measure ℝ)) := by
    filter_upwards [hApproxEventuallyNonzero] with n hn
    simpa [f_t] using
      (integral_eq_mass_mul_integral_normalize_local
        (exactRootApproxCompactAverageMeasure μroot n) hn
        (fun x : ℝ ↦ compactAverageReconstructionKernel_local t x))
  have hLimitEq :
      ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(η : Measure ℝ) =
        (m : ℂ) * ∫ x : ℝ, f_t x ∂(ρ : Measure ℝ) := by
    rw [hηeq]
    simpa [m, f_t] using
      (integral_mass_smul_probability_local
        m ρ (fun x : ℝ ↦ compactAverageReconstructionKernel_local t x))
  have hScaled :
      Tendsto
        (fun n : ℕ ↦
          (((exactRootApproxCompactAverageMeasure μroot n).mass : NNReal) : ℂ) *
            ∫ x : ℝ, f_t x ∂((exactRootApproxCompactAverageMeasure μroot n).normalize : Measure ℝ))
        atTop
        (𝓝 ((m : ℂ) * ∫ x : ℝ, f_t x ∂(ρ : Measure ℝ))) := by
    exact hMassTendsto.mul hNormIntegral
  have hIntegral :
      Tendsto
        (fun n : ℕ ↦
          ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
            ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ))
        atTop
        (𝓝 ((m : ℂ) * ∫ x : ℝ, f_t x ∂(ρ : Measure ℝ))) := by
    exact hScaled.congr' hApproxEq.symm
  simpa [hLimitEq] using hIntegral

/-- Helper for Theorem 16.22: after recovering the zero-drift Gaussian and jump fields from the
compact-average auxiliary measure, the remaining residual is exactly one linear imaginary drift. -/
private lemma compactAverageResidual_eq_linearDrift_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (hMassPos : 0 < Complex.re ((compactAverageExpLift Ψ) 0))
    {ρ : ProbabilityMeasure ℝ} {η : FiniteMeasure ℝ}
    (hηeq : η = (Real.toNNReal (Complex.re ((compactAverageExpLift Ψ) 0))) • ρ.toFiniteMeasure)
    (hnormTendsto : Tendsto (fun n : ℕ ↦ (exactRootApproxCompactAverageMeasure μroot n).normalize)
      atTop (𝓝 ρ)) :
    let σ2 : ℝ := 6 * (((η : Measure ℝ) ({0} : Set ℝ)).toReal)
    let ν := compactAverageRecoveredJumpMeasure_local η
    ∃ b : ℝ, ∀ t : ℝ, Ψ t = levyKhinchinExponentWithCentering σ2 b ν Real.sin t := by
  dsimp
  let σ2 : ℝ := 6 * (((η : Measure ℝ) ({0} : Set ℝ)).toReal)
  let ν : Measure ℝ := compactAverageRecoveredJumpMeasure_local η
  let R : ℝ → ℂ := fun t ↦ Ψ t - levyKhinchinExponentWithCentering σ2 0 ν Real.sin t
  let residualSeq : ℕ → ℝ → ℂ := fun n t ↦
    ((((exactRootApproxReconstructionDrift_local μroot n * t : ℝ) : ℂ) * Complex.I))
  have hIntegralLimit :
      ∀ t : ℝ,
        Tendsto
          (fun n : ℕ ↦
            ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
              ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ))
          atTop
          (𝓝 (levyKhinchinExponentWithCentering σ2 0 ν Real.sin t)) := by
    intro t
    have h :=
      tendsto_integral_compactAverageReconstructionKernel_exactRootApprox_local
        (μ := μ) μroot hroot hΨ0 hΨexp hMassPos hηeq hnormTendsto t
    have hEta :
        ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(η : Measure ℝ) =
          levyKhinchinExponentWithCentering σ2 0 ν Real.sin t := by
      symm
      simpa [σ2, ν] using compactAverageRecoveredZeroDriftExponent_local η t
    simpa [hEta] using h
  have hResidualLimit :
      ∀ t : ℝ, Tendsto (fun n : ℕ ↦ residualSeq n t) atTop (𝓝 (R t)) := by
    intro t
    have hRaw :
        Tendsto
          (fun n : ℕ ↦
            levyKhinchinExponent (exactRootApproxTriple μroot n) t -
              ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
                ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ))
          atTop
          (𝓝 (R t)) := by
      simpa [R] using
        (compoundPoissonApproxExponent_tendsto_local
          (μ := μ) μroot hroot hΨ0 hΨexp t).sub (hIntegralLimit t)
    refine hRaw.congr' ?_
    filter_upwards [] with n
    rw [exactRootApproxExponent_eq_reconstructionIntegral_add_drift_local]
    simp [residualSeq]
  have hResidualLinear :
      ∀ t : ℝ, R t = (t : ℂ) * R 1 := by
    intro t
    have hLeft : Tendsto (fun n : ℕ ↦ residualSeq n t) atTop (𝓝 (R t)) := hResidualLimit t
    have hRight :
        Tendsto (fun n : ℕ ↦ (t : ℂ) * residualSeq n 1) atTop (𝓝 ((t : ℂ) * R 1)) := by
      exact (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (t : ℂ)) atTop (𝓝 (t : ℂ))).mul
        (hResidualLimit 1)
    have hSeqEq :
        (fun n : ℕ ↦ residualSeq n t) =ᶠ[atTop] fun n : ℕ ↦ (t : ℂ) * residualSeq n 1 := by
      filter_upwards [] with n
      simp [residualSeq]
      ring
    have hRight' :
        Tendsto (fun n : ℕ ↦ residualSeq n t) atTop (𝓝 ((t : ℂ) * R 1)) := by
      exact hRight.congr' hSeqEq.symm
    exact tendsto_nhds_unique hLeft hRight'
  have hReZero :
      Complex.re (R 1) = 0 := by
    have hRe :
        Tendsto (fun n : ℕ ↦ Complex.re (residualSeq n 1)) atTop
          (𝓝 (Complex.re (R 1))) := by
      exact (Complex.continuous_re.continuousAt.tendsto.comp (hResidualLimit 1))
    have hZero :
        Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 (Complex.re (R 1))) := by
      refine hRe.congr' ?_
      filter_upwards [] with n
      simp [residualSeq]
    exact tendsto_nhds_unique hZero tendsto_const_nhds
  let b : ℝ := Complex.im (R 1)
  have hRone :
      R 1 = ((b : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [b, hReZero]
  refine ⟨b, ?_⟩
  intro t
  have hResidualFormula :
      R t = ((((b * t : ℝ) : ℂ)) * Complex.I) := by
    calc
      R t = (t : ℂ) * R 1 := hResidualLinear t
      _ = (t : ℂ) * ((b : ℂ) * Complex.I) := by rw [hRone]
      _ = ((((b * t : ℝ) : ℂ)) * Complex.I) := by
            simp [mul_assoc, mul_comm, mul_left_comm]
  have hAdd :
      Ψ t = levyKhinchinExponentWithCentering σ2 0 ν Real.sin t +
        ((((b * t : ℝ) : ℂ)) * Complex.I) := by
    have hAdd' :
        Ψ t = ((((b * t : ℝ) : ℂ)) * Complex.I) +
          levyKhinchinExponentWithCentering σ2 0 ν Real.sin t := by
      exact sub_eq_iff_eq_add.mp (by simpa [R] using hResidualFormula)
    simpa [add_comm] using hAdd'
  rw [levyKhinchinExponentWithSineCentering_add_drift_eq_local]
  exact hAdd

/-- Helper for Theorem 16.22: adding a drift coefficient to a fixed Gaussian/jump pair contributes
exactly the linear imaginary phase term in the Lévy--Khintchin exponent. -/
private lemma levyKhinchinExponent_add_drift_eq_local
    (σ2 b : ℝ) (ν : Measure ℝ) (t : ℝ) :
    levyKhinchinExponent { sigma2 := σ2, b := b, ν := ν } t =
      levyKhinchinExponent { sigma2 := σ2, b := 0, ν := ν } t +
        ((((b * t : ℝ) : ℂ)) * Complex.I) := by
  -- Proof comment: the Gaussian and jump parts are unchanged, so only the explicit drift term
  -- survives in the difference between the two exponents.
  simp [levyKhinchinExponent, levyKhinchinExponentWithCentering]
  ring
/-- Helper for Theorem 16.22: the exact-root approximation and the normalized lift isolate the
remaining forward Lévy--Khintchin existence blocker. -/
private lemma levyKhinchinTriple_exists_of_exactRoots_and_expLift_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    ∃ τ : LevyKhinchinTriple, HasLevyKhinchinRepresentation μ τ := by
  by_cases hDirac : ∃ b : ℝ, μ = diracProba b
  · rcases hDirac with ⟨b, rfl⟩
    -- Proof comment: the Dirac branch is explicit, so the canonical triple is `(0, b, 0)`.
    exact ⟨{ sigma2 := 0, b := b, ν := (0 : Measure ℝ) },
      hasLevyKhinchinRepresentation_dirac_local b⟩
  · have hMassPos :
        0 < Complex.re ((compactAverageExpLift Ψ) 0) :=
      compactAverageLiftZero_pos_of_notDirac_local hΨ0 hΨexp hDirac
    obtain ⟨ρ, η, hηeq, hηchar, hnormTendsto⟩ :=
      exists_compactAverageAuxFiniteMeasure_with_limit_of_exactRoots_nonDirac_local
        (μ := μ) μroot hroot hΨ0 hΨexp hDirac
    let _ := hMassPos
    let _ := ρ
    let _ := η
    let _ := hηeq
    let _ := hηchar
    let _ := hnormTendsto
    -- Proof comment: the non-Dirac branch now has the exact-root compact-average auxiliary
    -- finite measure `η` together with its normalized weak limit. Recover the zero-drift
    -- Gaussian/jump fields from `η` with the smooth `Real.sin` centering, then convert back to
    -- the canonical cutoff via `changeCentering`.
    let σ2 : ℝ := 6 * (((η : Measure ℝ) ({0} : Set ℝ)).toReal)
    let ν : Measure ℝ := compactAverageRecoveredJumpMeasure_local η
    have hν : IsCanonicalMeasure ν := by
      simpa [ν] using isCanonicalMeasure_compactAverageRecoveredJumpMeasure_local η
    have hDiffInt :
        Integrable (fun x : ℝ ↦ Real.sin x - levyKhinchinCanonicalCentering x) ν :=
      integrable_sin_sub_levyKhinchinCanonicalCentering_local hν
    obtain ⟨bSin, hbSin⟩ :=
      compactAverageResidual_eq_linearDrift_local
        (μ := μ) μroot hroot hΨ0 hΨexp hMassPos hηeq hnormTendsto
    let b : ℝ := bSin - ∫ x : ℝ, (Real.sin x - levyKhinchinCanonicalCentering x) ∂ν
    refine ⟨{ sigma2 := σ2, b := b, ν := ν }, ?_⟩
    constructor
    · refine ⟨?_, ?_⟩
      · dsimp [σ2]
        positivity
      · simpa [ν] using hν
    · intro t
      have hChangeFn :=
        levyKhinchinExponentWithCentering_changeCentering σ2 b ν hν Real.sin hDiffInt
      have hChangeAt := congrArg (fun f : ℝ → ℂ ↦ f t) hChangeFn
      rw [← hΨexp t, hbSin t]
      exact congrArg Complex.exp (by simpa [b, levyKhinchinExponent, ν] using hChangeAt)

/-- Helper for Theorem 16.22: an exact positive-integer root family reduces the existence problem
to the exact-root-plus-lift owner declaration. -/
private lemma levyKhinchinTriple_exists_of_exactRootFamily_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ) :
    ∃ τ : LevyKhinchinTriple, HasLevyKhinchinRepresentation μ τ := by
  obtain ⟨Ψ, hΨ0, hΨexp⟩ :=
    continuousExpLift_of_exactRootFamily_local (μ := μ) μroot hroot
  -- Proof comment: the exact roots first produce the normalized continuous lift, so the remaining
  -- work is exactly the owner existence bridge for exact roots plus that lift.
  exact
    levyKhinchinTriple_exists_of_exactRoots_and_expLift_local
      (μ := μ) μroot hroot hΨ0 hΨexp

/-- Helper for Theorem 16.22: infinitely divisible laws admit a Lévy--Khintchin representation by
the earlier Chapter 16 existence theorem. -/
private lemma levyKhinchinTriple_exists_of_isInfinitelyDivisible_local
    {μ : ProbabilityMeasure ℝ} (hμ : IsInfinitelyDivisible μ) :
    ∃ τ : LevyKhinchinTriple, HasLevyKhinchinRepresentation μ τ := by
  obtain ⟨μroot, hroot⟩ := existsExactRootFamily_of_isInfinitelyDivisible_local hμ
  -- Proof comment: the exact root family already carries the whole existence input, so the
  -- normalized lift is no longer threaded through this wrapper.
  exact levyKhinchinTriple_exists_of_exactRootFamily_local (μ := μ) μroot hroot

/-- Helper for Theorem 16.22: broad stability gives a canonical Lévy--Khintchin triple through
the local infinitely-divisible existence frontier. -/
private lemma levyKhinchinTriple_exists_of_broadStable
    {μ : ProbabilityMeasure ℝ} (hμ : IsStableInBroadSense μ) :
    ∃ τ : LevyKhinchinTriple, HasLevyKhinchinRepresentation μ τ := by
  rcases hμ.exists_scale_shift with ⟨a, d, ha_nonneg, hscale⟩
  have hInf : IsInfinitelyDivisible μ :=
    isInfinitelyDivisible_of_broadStableScaling hμ ha_nonneg hscale
  -- Proof comment: broad stability first yields infinite divisibility; the remaining existence
  -- step is the exact-root reconstruction packaged just above.
  exact levyKhinchinTriple_exists_of_isInfinitelyDivisible_local hInf

/-- Helper for Theorem 16.22: even before the missing uniqueness API is restored, the power-side
and affine-side broad-stability triples already give the same characteristic-function exponential
on the common law `μ ^ n`. -/
private lemma broadStablePowAffineExponent_exp_eq
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable)
    (n : ℕ+) :
    ∀ t : ℝ,
      Complex.exp
        (levyKhinchinExponent
        { sigma2 := (n : ℝ) * τ.sigma2
          b := (n : ℝ) * τ.b
          ν := (n : ℕ) • τ.ν } t) =
        Complex.exp
          (levyKhinchinExponent
          { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
            b := a n * τ.b + d n +
              a n * ∫ x : ℝ,
                ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
            ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } t) := by
  have hpowRep :
      HasLevyKhinchinRepresentation (μ ^ (n : ℕ))
        { sigma2 := (n : ℝ) * τ.sigma2
          b := (n : ℝ) * τ.b
          ν := (n : ℕ) • τ.ν } :=
    pow_hasLevyKhinchinRepresentation μ τ n hτ
  have ha_pos : ∀ m : ℕ+, 0 < a m := scalePosOfBroadStable hμ ha_nonneg hscale
  have hmapRep :
      HasLevyKhinchinRepresentation (μ ^ (n : ℕ))
        { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
          b := a n * τ.b + d n +
            a n * ∫ x : ℝ,
              ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
          ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } := by
    have hmapAffine :
        HasLevyKhinchinRepresentation
          (map μ (measurable_affineMap (a n) (d n)).aemeasurable)
          { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
            b := a n * τ.b + d n +
              a n * ∫ x : ℝ,
                ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
            ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } :=
      map_affine_hasLevyKhinchinRepresentation μ τ hτ (ha_pos n)
    -- Proof comment: rewrite the affine-image representation along the broad-stability identity
    -- so both exponent formulas live on the common law `μ ^ n`.
    exact hasLevyKhinchinRepresentation_congr (hscale n).symm hmapAffine
  intro t
  -- Proof comment: both exponentials are identified with the characteristic function of `μ ^ n`.
  rw [← hpowRep.charFun_eq_exp t, ← hmapRep.charFun_eq_exp t]

/-- Helper for Theorem 16.22: once continuity is recorded, the power-side and affine-side
canonical triples for `μ ^ n` already have the same exponent. -/
private lemma broadStablePowAffineExponent_eq
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable)
    (n : ℕ+) :
    ∀ t : ℝ,
      levyKhinchinExponent
        { sigma2 := (n : ℝ) * τ.sigma2
          b := (n : ℝ) * τ.b
          ν := (n : ℕ) • τ.ν } t =
        levyKhinchinExponent
          { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
            b := a n * τ.b + d n +
              a n * ∫ x : ℝ,
                ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
            ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } t := by
  have hpowRep :
      HasLevyKhinchinRepresentation (μ ^ (n : ℕ))
        { sigma2 := (n : ℝ) * τ.sigma2
          b := (n : ℝ) * τ.b
          ν := (n : ℕ) • τ.ν } :=
    pow_hasLevyKhinchinRepresentation μ τ n hτ
  have ha_pos : ∀ m : ℕ+, 0 < a m := scalePosOfBroadStable hμ ha_nonneg hscale
  have hmapRep :
      HasLevyKhinchinRepresentation (μ ^ (n : ℕ))
        { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
          b := a n * τ.b + d n +
            a n * ∫ x : ℝ,
              ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
          ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } := by
    have hmapAffine :
        HasLevyKhinchinRepresentation
          (map μ (measurable_affineMap (a n) (d n)).aemeasurable)
          { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
            b := a n * τ.b + d n +
              a n * ∫ x : ℝ,
                ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
            ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } :=
      map_affine_hasLevyKhinchinRepresentation μ τ hτ (ha_pos n)
    -- Proof comment: rewrite the affine-image representation along the broad-stability identity
    -- so both exponents represent the same law `μ ^ n`.
    exact hasLevyKhinchinRepresentation_congr (hscale n).symm hmapAffine
  intro t
  -- Proof comment: the project-local continuity interface already upgrades same-law
  -- representations to exponent equality, so no full-triple uniqueness lemma is needed here.
  exact
    levyKhinchinExponent_eq_of_sameRepresentation_of_continuous
      hpowRep
      hmapRep
      (continuousLevyKhinchinExponentLocal hpowRep.isCanonicalTriple)
      (continuousLevyKhinchinExponentLocal hmapRep.isCanonicalTriple)
      t

/-- Helper for Theorem 16.22: the power-side and affine-side broad-stability representations of
`μ ^ n` have the same Gaussian coefficient and Lévy measure. -/
private lemma broadStablePowAffine_sigma2_levyMeasure_eq
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable)
    (n : ℕ+) :
    ((n : ℝ) * τ.sigma2 = (a n) ^ (2 : ℕ) * τ.sigma2) ∧
      ((n : ℕ) • τ.ν = Measure.map (fun x : ℝ ↦ a n * x) τ.ν) := by
  have hpowRep :
      HasLevyKhinchinRepresentation (μ ^ (n : ℕ))
        { sigma2 := (n : ℝ) * τ.sigma2
          b := (n : ℝ) * τ.b
          ν := (n : ℕ) • τ.ν } :=
    pow_hasLevyKhinchinRepresentation μ τ n hτ
  have ha_pos : ∀ m : ℕ+, 0 < a m := scalePosOfBroadStable hμ ha_nonneg hscale
  have hmapAffine :
      HasLevyKhinchinRepresentation
        (map μ (measurable_affineMap (a n) (d n)).aemeasurable)
        { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
          b := a n * τ.b + d n +
            a n * ∫ x : ℝ,
              ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
          ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } :=
    map_affine_hasLevyKhinchinRepresentation μ τ hτ (ha_pos n)
  have hmapRep :
      HasLevyKhinchinRepresentation (μ ^ (n : ℕ))
        { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
          b := a n * τ.b + d n +
            a n * ∫ x : ℝ,
              ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
          ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } :=
    hasLevyKhinchinRepresentation_congr (hscale n).symm hmapAffine
  -- Proof comment: both sides represent the same law `μ ^ n`, so the narrowed same-law recovery
  -- reads off the Gaussian coefficient and Lévy measure directly.
  exact sigma2_levyMeasure_eq_of_sameRepresentation hpowRep hmapRep

/-- Helper for Theorem 16.22: the canonical Gaussian coefficient satisfies the broad-stability
scaling relation `((aₙ)^2 - n) σ² = 0`. -/
private lemma stableBroad_canonicalTriple_gaussianScaling
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable) :
    ∀ n : ℕ+, ((a n) ^ (2 : ℕ) - (n : ℝ)) * τ.sigma2 = 0 := by
  intro n
  have hsigmaν :=
    broadStablePowAffine_sigma2_levyMeasure_eq hμ hτ ha_nonneg hscale n
  have hsigma :
      (n : ℝ) * τ.sigma2 = (a n) ^ (2 : ℕ) * τ.sigma2 := hsigmaν.1
  nlinarith

/-- Helper for Theorem 16.22: the canonical Lévy measure satisfies the exact broad-stability
scaling relation. -/
private lemma stableBroad_canonicalTriple_levyMeasureScaling
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable) :
    ∀ n : ℕ+, (n : ℕ) • τ.ν = Measure.map (fun x : ℝ ↦ a n * x) τ.ν := by
  intro n
  -- Proof comment: the narrowed same-law recovery already returns the `ν` scaling identity.
  exact (broadStablePowAffine_sigma2_levyMeasure_eq hμ hτ ha_nonneg hscale n).2

/-- Helper for Theorem 16.22: at frequency `1`, the broad-stability comparison can be normalized
so the Gaussian and Lévy fields agree literally on both sides. -/
private lemma broadStablePowAffineExponent_eq_normalizedAtOne
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+, μ ^ (n : ℕ) = μ.map (measurable_affineMap (a n) (d n)).aemeasurable)
    (n : ℕ+) :
    levyKhinchinExponent
      { sigma2 := (n : ℝ) * τ.sigma2
        b := (n : ℝ) * τ.b
        ν := (n : ℕ) • τ.ν } 1 =
      levyKhinchinExponent
        { sigma2 := (n : ℝ) * τ.sigma2
          b := a n * τ.b + d n +
            a n * ∫ x : ℝ,
              ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
          ν := (n : ℕ) • τ.ν } 1 := by
  have hsigmaZero := stableBroad_canonicalTriple_gaussianScaling hμ hτ ha_nonneg hscale n
  have hsigma :
      (a n) ^ (2 : ℕ) * τ.sigma2 = (n : ℝ) * τ.sigma2 := by
    nlinarith
  have hnu := stableBroad_canonicalTriple_levyMeasureScaling hμ hτ ha_nonneg hscale n
  have hExp := broadStablePowAffineExponent_eq hμ hτ ha_nonneg hscale n 1
  -- Proof comment: rewrite the affine-side exponent into the same Gaussian/jump normal form as
  -- the power-side exponent before reading off the drift term.
  rw [hsigma, ← hnu] at hExp
  simpa using hExp

/-- Helper for Theorem 16.22: after normalizing the Gaussian and Lévy fields, broad stability
projects to the explicit drift identity. -/
private lemma stableBroad_bField_eq
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+, μ ^ (n : ℕ) = μ.map (measurable_affineMap (a n) (d n)).aemeasurable)
    (n : ℕ+) :
    (n : ℝ) * τ.b =
      a n * τ.b + d n +
        a n * ∫ x : ℝ, ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν := by
  have hExpNormalized :=
    broadStablePowAffineExponent_eq_normalizedAtOne hμ hτ ha_nonneg hscale n
  have himagNormalized := congrArg Complex.im hExpNormalized
  -- Proof comment: once the non-drift fields match syntactically, taking imaginary parts leaves
  -- exactly the linear drift comparison.
  simp only [levyKhinchinExponent, levyKhinchinExponentWithCentering, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul,
    mul_zero, add_zero, one_mul] at himagNormalized
  linarith

/-- Helper for Theorem 16.22: if the Lévy measure vanishes, the power-side and affine-side
exponents are the same normalized continuous logarithm of `charFun (μ ^ n)`. -/
private lemma zeroLevyExponent_eq_of_broadStableScaling
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable)
    (hν : τ.ν = 0) :
    ∀ n : ℕ+, ∀ t : ℝ,
      (((-(((n : ℝ) * τ.sigma2) / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
          ((((n : ℝ) * τ.b * t : ℝ) : ℂ) * Complex.I) =
        (((-(((a n) ^ (2 : ℕ) * τ.sigma2) / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
          ((((a n * τ.b + d n) * t : ℝ) : ℂ) * Complex.I) := by
  intro n
  let Ψpow : C(ℝ, ℂ) :=
    ⟨fun t : ℝ ↦
      (((-(((n : ℝ) * τ.sigma2) / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
        ((((n : ℝ) * τ.b * t : ℝ) : ℂ) * Complex.I), by continuity⟩
  let Ψmap : C(ℝ, ℂ) :=
    ⟨fun t : ℝ ↦
      (((-(((a n) ^ (2 : ℕ) * τ.sigma2) / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
        ((((a n * τ.b + d n) * t : ℝ) : ℂ) * Complex.I), by continuity⟩
  let μpow : Measure ℝ := ((μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ)
  have hpowExp :
      ∀ t : ℝ,
        Complex.exp (Ψpow t) = charFun μpow t := by
    intro t
    have hΨpow :
        Ψpow t = ((n : ℕ) : ℂ) * levyKhinchinExponent τ t := by
      -- Proof comment: with `τ.ν = 0`, the `n`th power exponent is exactly the scalar multiple
      -- `n ψ(t)`.
      simp [Ψpow, levyKhinchinExponent, levyKhinchinExponentWithCentering, hν]
      ring
    calc
      Complex.exp (Ψpow t)
          = Complex.exp (((n : ℕ) : ℂ) * levyKhinchinExponent τ t) := by rw [hΨpow]
      _ = Complex.exp (levyKhinchinExponent τ t) ^ (n : ℕ) := by
            rw [Complex.exp_nat_mul]
      _ = charFun (μ : Measure ℝ) t ^ (n : ℕ) := by rw [hτ.charFun_eq_exp]
      _ = charFun μpow t := by
            simpa using
              (congrArg (fun f : ℝ → ℂ ↦ f t) (ProbabilityMeasure.charFun_pow μ (n : ℕ))).symm
  have hmapExp :
      ∀ t : ℝ,
        Complex.exp (Ψmap t) = charFun μpow t := by
    intro t
    have hΨmap :
        Ψmap t =
          levyKhinchinExponent τ (a n * t) + ((((d n * t : ℝ) : ℂ) * Complex.I)) := by
      -- Proof comment: when `τ.ν = 0`, the affine image changes only the Gaussian coefficient
      -- and adds the translated linear phase.
      simp [Ψmap, levyKhinchinExponent, levyKhinchinExponentWithCentering, hν]
      ring
    have hchar_map :
        charFun
            ((map μ (measurable_affineMap (a n) (d n)).aemeasurable : ProbabilityMeasure ℝ) :
              Measure ℝ) t =
          charFun (μ : Measure ℝ) (a n * t) *
            Complex.exp ((((d n * t : ℝ) : ℂ) * Complex.I)) := by
      -- Proof comment: decompose the affine map into scaling followed by translation.
      rw [ProbabilityMeasure.toMeasure_map]
      have hcomp :
          Measure.map (fun x : ℝ ↦ a n * x + d n) (μ : Measure ℝ) =
            Measure.map (fun x : ℝ ↦ x + d n) (Measure.map (fun x : ℝ ↦ a n * x) (μ : Measure ℝ)) := by
        rw [show (fun x : ℝ ↦ a n * x + d n) =
            (fun x : ℝ ↦ x + d n) ∘ fun x : ℝ ↦ a n * x from rfl, ← Measure.map_map]
        all_goals fun_prop
      rw [hcomp, MeasureTheory.charFun_map_add_const]
      rw [MeasureTheory.charFun_map_mul]
      simp [realInner_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    calc
      Complex.exp (Ψmap t)
          = Complex.exp (levyKhinchinExponent τ (a n * t)) *
              Complex.exp ((((d n * t : ℝ) : ℂ) * Complex.I)) := by
                rw [hΨmap, Complex.exp_add]
      _ = charFun (μ : Measure ℝ) (a n * t) *
            Complex.exp ((((d n * t : ℝ) : ℂ) * Complex.I)) := by
              rw [hτ.charFun_eq_exp]
      _ = charFun
            ((map μ (measurable_affineMap (a n) (d n)).aemeasurable : ProbabilityMeasure ℝ) :
              Measure ℝ) t := by
              rw [hchar_map]
      _ = charFun μpow t := by
            simpa [μpow, hscale n]
  have hchar_nonzero : ∀ t : ℝ, charFun μpow t ≠ 0 := by
    intro t
    rw [← hpowExp t]
    exact Complex.exp_ne_zero _
  let φpow : ℝ → ℂ := fun t ↦ charFun μpow t
  obtain ⟨Ψ, hΨ, huniq⟩ :=
    existsUniqueContinuousExpLift
      (by
        simpa [φpow] using
          (MeasureTheory.continuous_charFun : Continuous (charFun μpow)))
      hchar_nonzero
      (by simpa [φpow] using MeasureTheory.charFun_zero μpow)
  have hpow_eq_Ψ : Ψpow = Ψ := by
    apply huniq
    constructor
    · -- Proof comment: the power-side polynomial lift is normalized at `0`.
      simp [Ψpow]
    · exact hpowExp
  have hmap_eq_Ψ : Ψmap = Ψ := by
    apply huniq
    constructor
    · -- Proof comment: the affine-side polynomial lift is normalized at `0`.
      simp [Ψmap]
    · exact hmapExp
  have hEq : Ψpow = Ψmap := hpow_eq_Ψ.trans hmap_eq_Ψ.symm
  intro t
  -- Proof comment: evaluate the equality of continuous lifts at the requested frequency.
  exact congrArg (fun f : C(ℝ, ℂ) ↦ f t) hEq

/-- Helper for Theorem 16.22: if the Lévy measure vanishes, the broad-stability scale factors are
forced to be `aₙ = n^(1/2)`. -/
private lemma stableBroad_zeroLevyMeasure_scale_eq
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable)
    (hν : τ.ν = 0) :
    ∀ n : ℕ+, a n = (n : ℝ) ^ (1 / (2 : ℝ)) := by
  intro n
  have hσ_ne : τ.sigma2 ≠ 0 := by
    intro hσ
    have hdirac : μ = diracProba τ.b :=
      eq_diracProba_of_zeroGaussian_zeroLevy hτ hσ hν
    exact hμ.1 τ.b hdirac
  have hσ_pos : 0 < τ.sigma2 := by
    -- Proof comment: canonical Gaussian coefficients are nonnegative, so nonvanishing implies
    -- strict positivity.
    exact lt_of_le_of_ne hτ.isCanonicalTriple.sigma2_nonneg (by simpa using hσ_ne.symm)
  have hExpAtOne :=
    zeroLevyExponent_eq_of_broadStableScaling hτ hscale hν n 1
  have hreal := congrArg Complex.re hExpAtOne
  have hsigmaScale : ((a n) ^ (2 : ℕ) - (n : ℝ)) * τ.sigma2 = 0 := by
    -- Proof comment: taking real parts isolates the quadratic Gaussian coefficient.
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_eq_add_neg, add_zero, one_mul] at hreal
    linarith
  have hsq : (a n) ^ (2 : ℕ) = (n : ℝ) := by
    nlinarith [hsigmaScale, hσ_pos]
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hsq_sqrt : (a n) ^ (2 : ℕ) = (Real.sqrt (n : ℝ)) ^ (2 : ℕ) := by
    rw [pow_two, Real.sq_sqrt hn_nonneg]
    simpa [pow_two] using hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq_sqrt with ha_eq | ha_eq
  · -- Proof comment: positivity of the affine scale picks the positive square root branch.
    simpa [Real.sqrt_eq_rpow] using ha_eq
  · exfalso
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
      apply Real.sqrt_pos.2
      positivity
    linarith [ha_nonneg n, hsqrt_pos, ha_eq]

/-- Helper for Theorem 16.22: if the Lévy measure vanishes, the centering constants are exactly
`b (n - n^(1/2))`. -/
private lemma stableBroad_zeroLevyMeasure_centering_eq
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable)
    (hν : τ.ν = 0) :
    ∀ n : ℕ+, d n = τ.b * ((n : ℝ) - (n : ℝ) ^ (1 / (2 : ℝ))) := by
  intro n
  have hExpAtOne :=
    zeroLevyExponent_eq_of_broadStableScaling hτ hscale hν n 1
  have himag := congrArg Complex.im hExpAtOne
  have hscale_eq :
      a n = (n : ℝ) ^ (1 / (2 : ℝ)) :=
    stableBroad_zeroLevyMeasure_scale_eq hμ hτ ha_nonneg hscale hν n
  -- Proof comment: taking imaginary parts isolates the linear drift contribution.
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, add_zero, one_mul] at himag
  have himag' : (n : ℝ) * τ.b = (n : ℝ) ^ (1 / (2 : ℝ)) * τ.b + d n := by
    simpa [hscale_eq] using himag
  linarith

/-- Helper for Theorem 16.22: when the canonical Lévy measure vanishes, the broad-stability
branch is already the Gaussian index-`2` case. -/
private lemma stableBroad_zeroLevyMeasure_indexTwo
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable)
    (hν : τ.ν = 0) :
    IsStableInBroadSenseWithIndex μ 2 ∧ IsGaussian (μ : Measure ℝ) := by
  have hscale_eq :
      ∀ n : ℕ+, a n = (n : ℝ) ^ (1 / (2 : ℝ)) :=
    stableBroad_zeroLevyMeasure_scale_eq hμ hτ ha_nonneg hscale hν
  have hcenter_eq :
      ∀ n : ℕ+, d n = τ.b * ((n : ℝ) - (n : ℝ) ^ (1 / (2 : ℝ))) :=
    stableBroad_zeroLevyMeasure_centering_eq hμ hτ ha_nonneg hscale hν
  have hgaussEq :
      (μ : Measure ℝ) =
        gaussianReal τ.b ⟨τ.sigma2, hτ.isCanonicalTriple.sigma2_nonneg⟩ := by
    apply Measure.ext_of_charFun
    funext t
    -- Proof comment: with `τ.ν = 0`, the Lévy--Khintchin exponent is exactly the Gaussian
    -- characteristic exponent with mean `τ.b` and variance `τ.sigma2`.
    rw [hτ.charFun_eq_exp, ProbabilityTheory.charFun_gaussianReal]
    simp [levyKhinchinExponent, levyKhinchinExponentWithCentering, hν, sub_eq_add_neg]
    ring
  constructor
  · refine ⟨hμ.1, by simp, ?_⟩
    refine ⟨fun n ↦ τ.b * ((n : ℝ) - (n : ℝ) ^ (1 / (2 : ℝ))), ?_⟩
    intro n
    -- Proof comment: rewrite the original affine realization using the recovered Gaussian scale
    -- and centering formulas.
    simpa [hscale_eq n, hcenter_eq n] using hscale n
  · -- Proof comment: the characteristic-function identification upgrades the law to a Gaussian
    -- measure by transport from `gaussianReal`.
    have hgauss : IsGaussian
        (gaussianReal τ.b ⟨τ.sigma2, hτ.isCanonicalTriple.sigma2_nonneg⟩) := by
      infer_instance
    simpa [hgaussEq] using hgauss

/-- Helper for Theorem 16.22: a canonical Lévy measure has finite right tails away from `0`. -/
private lemma canonicalTriple_rightTail_lt_top
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) {x : ℝ} (hx : 0 < x) :
    τ.ν (Set.Ici x) < ⊤ := by
  have hmin_pos : 0 < min (x ^ (2 : ℕ)) 1 := by
    refine lt_min ?_ zero_lt_one
    simpa [pow_two] using sq_pos_of_pos hx
  have hlevel :
      τ.ν {y : ℝ | min (x ^ (2 : ℕ)) 1 / 2 < min (y ^ (2 : ℕ)) 1} < ⊤ :=
    IsCanonicalMeasure.canonicalMeasure_levelSet_lt_top
      hτ.isCanonicalMeasure (by positivity)
  have hsubset :
      Set.Ici x ⊆ {y : ℝ | min (x ^ (2 : ℕ)) 1 / 2 < min (y ^ (2 : ℕ)) 1} := by
    intro y hy
    have hy_nonneg : 0 ≤ y := le_trans hx.le hy
    have habs : |x| ≤ |y| := by
      simpa [abs_of_nonneg hx.le, abs_of_nonneg hy_nonneg] using hy
    have hsq : x ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by
      simpa [sq_abs] using sq_le_sq.mpr habs
    have hmono : min (x ^ (2 : ℕ)) 1 ≤ min (y ^ (2 : ℕ)) 1 :=
      min_le_min_right 1 hsq
    exact lt_of_lt_of_le (by simpa using half_lt_self hmin_pos) hmono
  exact lt_of_le_of_lt (measure_mono hsubset) hlevel

/-- Helper for Theorem 16.22: a canonical Lévy measure has finite left tails away from `0`. -/
private lemma canonicalTriple_leftTail_lt_top
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) {x : ℝ} (hx : 0 < x) :
    τ.ν (Set.Iic (-x)) < ⊤ := by
  have hmin_pos : 0 < min (x ^ (2 : ℕ)) 1 := by
    refine lt_min ?_ zero_lt_one
    simpa [pow_two] using sq_pos_of_pos hx
  have hlevel :
      τ.ν {y : ℝ | min (x ^ (2 : ℕ)) 1 / 2 < min (y ^ (2 : ℕ)) 1} < ⊤ :=
    IsCanonicalMeasure.canonicalMeasure_levelSet_lt_top
      hτ.isCanonicalMeasure (by positivity)
  have hsubset :
      Set.Iic (-x) ⊆ {y : ℝ | min (x ^ (2 : ℕ)) 1 / 2 < min (y ^ (2 : ℕ)) 1} := by
    intro y hy
    have hy_le : y ≤ -x := by simpa using hy
    have hy_nonpos : y ≤ 0 := by linarith
    have habs : |x| ≤ |y| := by
      rw [abs_of_nonneg hx.le, abs_of_nonpos hy_nonpos]
      linarith
    have hsq : x ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by
      simpa [sq_abs] using sq_le_sq.mpr habs
    have hmono : min (x ^ (2 : ℕ)) 1 ≤ min (y ^ (2 : ℕ)) 1 :=
      min_le_min_right 1 hsq
    exact lt_of_lt_of_le (by simpa using half_lt_self hmin_pos) hmono
  exact lt_of_le_of_lt (measure_mono hsubset) hlevel

/-- Helper for Theorem 16.22: the Lévy-measure scaling identity induces exact one-sided tail
scaling on the half-lines away from `0`. -/
private lemma oneSidedTailScaling_of_levyMeasureScaling
    {τ : LevyKhinchinTriple} {a : ℕ+ → ℝ}
    (hτ : IsCanonicalTriple τ)
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hscaleν : ∀ n : ℕ+, (n : ℕ) • τ.ν = Measure.map (fun x : ℝ ↦ a n * x) τ.ν) :
    (∀ n : ℕ+, ∀ x : ℝ, 0 < x →
      (n : ℝ) * (τ.ν (Set.Ici x)).toReal = (τ.ν (Set.Ici (x / a n))).toReal) ∧
    (∀ n : ℕ+, ∀ x : ℝ, 0 < x →
      (n : ℝ) * (τ.ν (Set.Iic (-x))).toReal = (τ.ν (Set.Iic (-(x / a n)))).toReal) := by
  constructor
  · intro n x hx
    have hmeas : Measurable (fun y : ℝ ↦ a n * y) := by
      fun_prop
    have hfinite_x : τ.ν (Set.Ici x) < ⊤ := canonicalTriple_rightTail_lt_top hτ hx
    have hfinite_div : τ.ν (Set.Ici (x / a n)) < ⊤ :=
      canonicalTriple_rightTail_lt_top hτ (div_pos hx (ha_pos n))
    have hpreimage :
        (fun y : ℝ ↦ a n * y) ⁻¹' Set.Ici x = Set.Ici (x / a n) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Ici]
      rw [div_le_iff₀ (ha_pos n)]
      ring
    have htail :=
      congrArg (fun ν : Measure ℝ ↦ ν (Set.Ici x)) (hscaleν n)
    have htail' :
        (n : ENNReal) * τ.ν (Set.Ici x) = τ.ν (Set.Ici (x / a n)) := by
      simpa [nsmul_eq_mul, Measure.smul_apply, Measure.map_apply hmeas measurableSet_Ici,
        hpreimage] using htail
    -- Proof comment: both half-line masses are finite away from `0`, so `toReal` turns the
    -- measure equality into an exact scalar identity.
    have htoReal := congrArg ENNReal.toReal htail'
    simpa [ENNReal.toReal_mul, hfinite_x.ne, hfinite_div.ne] using htoReal
  · intro n x hx
    have hmeas : Measurable (fun y : ℝ ↦ a n * y) := by
      fun_prop
    have hfinite_x : τ.ν (Set.Iic (-x)) < ⊤ := canonicalTriple_leftTail_lt_top hτ hx
    have hfinite_div : τ.ν (Set.Iic (-(x / a n))) < ⊤ :=
      canonicalTriple_leftTail_lt_top hτ (div_pos hx (ha_pos n))
    have hpreimage :
        (fun y : ℝ ↦ a n * y) ⁻¹' Set.Iic (-x) = Set.Iic (-(x / a n)) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Iic]
      have hnegdiv : -(x / a n) = (-x) / a n := by
        field_simp [ne_of_gt (ha_pos n)]
      rw [hnegdiv]
      rw [le_div_iff₀ (ha_pos n)]
      ring
    have htail :=
      congrArg (fun ν : Measure ℝ ↦ ν (Set.Iic (-x))) (hscaleν n)
    have htail' :
        (n : ENNReal) * τ.ν (Set.Iic (-x)) = τ.ν (Set.Iic (-(x / a n))) := by
      simpa [nsmul_eq_mul, Measure.smul_apply, Measure.map_apply hmeas measurableSet_Iic,
        hpreimage] using htail
    -- Proof comment: the same finite-tail transport works on the negative half-line.
    have htoReal := congrArg ENNReal.toReal htail'
    simpa [ENNReal.toReal_mul, hfinite_x.ne, hfinite_div.ne] using htoReal

/-- Helper for Theorem 16.22: the right-tail function of a canonical Lévy measure is antitone on
`(0, ∞)`. -/
private lemma canonicalTriple_rightTail_toReal_antitoneOn
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) :
    AntitoneOn (fun x : ℝ ↦ (τ.ν (Set.Ici x)).toReal) (Set.Ioi 0) := by
  intro x hx y hy hxy
  -- Proof comment: enlarging the cutoff shrinks the right half-line, so the corresponding tail
  -- mass can only decrease.
  refine ENNReal.toReal_mono (canonicalTriple_rightTail_lt_top hτ hx).ne ?_
  exact measure_mono fun z hz ↦ le_trans hxy hz

/-- Helper for Theorem 16.22: the left-tail function of a canonical Lévy measure is antitone on
`(0, ∞)`. -/
private lemma canonicalTriple_leftTail_toReal_antitoneOn
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) :
    AntitoneOn (fun x : ℝ ↦ (τ.ν (Set.Iic (-x))).toReal) (Set.Ioi 0) := by
  intro x hx y hy hxy
  -- Proof comment: increasing the positive radius pushes the left half-line farther left, so its
  -- tail mass also decreases.
  refine ENNReal.toReal_mono (canonicalTriple_leftTail_lt_top hτ hx).ne ?_
  exact measure_mono fun z hz ↦ by
    have hz' : z ≤ -y := hz
    have hneg : -y ≤ -x := by linarith
    exact le_trans hz' hneg

/-- Helper for Theorem 16.22: the finite right tails of a canonical Lévy measure decay to `0`
along `atTop`. -/
private lemma canonicalTriple_rightTail_toReal_tendsto_zero_atTop
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) :
    Tendsto (fun x : ℝ ↦ (τ.ν (Set.Ici x)).toReal) atTop (𝓝 0) := by
  let s : ℕ → Set ℝ := fun n ↦ Set.Ici (max (n : ℝ) 1)
  have hs_meas : ∀ n : ℕ, NullMeasurableSet (s n) τ.ν := by
    intro n
    exact measurableSet_Ici.nullMeasurableSet
  have hs_anti : Antitone s := by
    intro m n hmn
    exact Set.Ici_subset_Ici.2 (max_le_max (by exact_mod_cast hmn) le_rfl)
  have hs_fin : ∃ n : ℕ, τ.ν (s n) ≠ ⊤ := by
    refine ⟨0, ?_⟩
    simpa [s] using (canonicalTriple_rightTail_lt_top hτ zero_lt_one).ne
  have hs_tendsto :
      Tendsto (fun n : ℕ ↦ τ.ν (s n)) atTop (𝓝 (τ.ν (⋂ n, s n))) :=
    tendsto_measure_iInter_atTop hs_meas hs_anti hs_fin
  have hs_inter : (⋂ n, s n) = ∅ := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt x
      have hx_all : ∀ n : ℕ, x ∈ s n := by
        simpa [Set.mem_iInter] using hx
      have hx_mem : max (n : ℝ) 1 ≤ x := by
        simpa [s] using hx_all n
      have hlt : x < max (n : ℝ) 1 := lt_of_lt_of_le hn (le_max_left (n : ℝ) 1)
      exact (not_lt_of_ge hx_mem) hlt
    · simp
  have hs_toReal :
      Tendsto (fun n : ℕ ↦ (τ.ν (s n)).toReal) atTop (𝓝 0) := by
    refine (ENNReal.tendsto_toReal_zero_iff ?_).2 ?_
    · intro n
      exact
        (canonicalTriple_rightTail_lt_top hτ
          (lt_of_lt_of_le zero_lt_one (le_max_right (n : ℝ) 1))).ne
    · simpa [hs_inter] using hs_tendsto
  let F : ℝ → ℝ := fun x ↦ (τ.ν (Set.Ici (max x 1))).toReal
  have hF_anti : Antitone F := by
    intro x y hxy
    dsimp [F]
    refine ENNReal.toReal_mono ?_ ?_
    · exact
        (canonicalTriple_rightTail_lt_top hτ
          (lt_of_lt_of_le zero_lt_one (le_max_right x 1))).ne
    · exact measure_mono (Set.Ici_subset_Ici.2 (max_le_max hxy le_rfl))
  have hF_tendsto : Tendsto F atTop (𝓝 0) := by
    exact
      (tendsto_iff_tendsto_subseq_of_antitone hF_anti tendsto_natCast_atTop_atTop).2 <|
        by simpa [F, s] using hs_toReal
  refine Tendsto.congr' ?_ hF_tendsto
  filter_upwards [Ici_mem_atTop (1 : ℝ)] with x hx
  have hx' : 1 ≤ x := hx
  -- Proof comment: above `1`, the auxiliary cutoff `max x 1` is exactly `x`, so the
  -- antitone-atTop reduction applies to the original right-tail function.
  simp [F, max_eq_left hx']

/-- Helper for Theorem 16.22: the finite left tails of a canonical Lévy measure decay to `0`
along `atTop`. -/
private lemma canonicalTriple_leftTail_toReal_tendsto_zero_atTop
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) :
    Tendsto (fun x : ℝ ↦ (τ.ν (Set.Iic (-x))).toReal) atTop (𝓝 0) := by
  let s : ℕ → Set ℝ := fun n ↦ Set.Iic (-max (n : ℝ) 1)
  have hs_meas : ∀ n : ℕ, NullMeasurableSet (s n) τ.ν := by
    intro n
    exact measurableSet_Iic.nullMeasurableSet
  have hs_anti : Antitone s := by
    intro m n hmn
    have hmax : max (m : ℝ) 1 ≤ max (n : ℝ) 1 := max_le_max (by exact_mod_cast hmn) le_rfl
    exact Set.Iic_subset_Iic.2 (by linarith)
  have hs_fin : ∃ n : ℕ, τ.ν (s n) ≠ ⊤ := by
    refine ⟨0, ?_⟩
    simpa [s] using (canonicalTriple_leftTail_lt_top hτ zero_lt_one).ne
  have hs_tendsto :
      Tendsto (fun n : ℕ ↦ τ.ν (s n)) atTop (𝓝 (τ.ν (⋂ n, s n))) :=
    tendsto_measure_iInter_atTop hs_meas hs_anti hs_fin
  have hs_inter : (⋂ n, s n) = ∅ := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      have hx_all : ∀ n : ℕ, x ∈ s n := by
        simpa [Set.mem_iInter] using hx
      have hx_mem : x ≤ -max (n : ℝ) 1 := by
        simpa [s] using hx_all n
      have hlt : -x < max (n : ℝ) 1 := lt_of_lt_of_le hn (le_max_left (n : ℝ) 1)
      linarith
    · simp
  have hs_toReal :
      Tendsto (fun n : ℕ ↦ (τ.ν (s n)).toReal) atTop (𝓝 0) := by
    refine (ENNReal.tendsto_toReal_zero_iff ?_).2 ?_
    · intro n
      exact
        (canonicalTriple_leftTail_lt_top hτ
          (lt_of_lt_of_le zero_lt_one (le_max_right (n : ℝ) 1))).ne
    · simpa [hs_inter] using hs_tendsto
  let F : ℝ → ℝ := fun x ↦ (τ.ν (Set.Iic (-max x 1))).toReal
  have hF_anti : Antitone F := by
    intro x y hxy
    dsimp [F]
    refine ENNReal.toReal_mono ?_ ?_
    · exact
        (canonicalTriple_leftTail_lt_top hτ
          (lt_of_lt_of_le zero_lt_one (le_max_right x 1))).ne
    · have hmax : max x 1 ≤ max y 1 := max_le_max hxy le_rfl
      exact measure_mono (Set.Iic_subset_Iic.2 (by linarith))
  have hF_tendsto : Tendsto F atTop (𝓝 0) := by
    exact
      (tendsto_iff_tendsto_subseq_of_antitone hF_anti tendsto_natCast_atTop_atTop).2 <|
        by simpa [F, s] using hs_toReal
  refine Tendsto.congr' ?_ hF_tendsto
  filter_upwards [Ici_mem_atTop (1 : ℝ)] with x hx
  have hx' : 1 ≤ x := hx
  -- Proof comment: the same `max x 1` normalization reduces the left-tail limit to the
  -- antitone-atTop subsequence argument proved above.
  simp [F, max_eq_left hx']

/-- Helper for Theorem 16.22: a nonzero canonical Lévy measure has a positive closed tail on at
least one side of the origin. -/
private lemma oneSidedTailNontrivial_of_nonzeroLevyMeasure
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) (hν : τ.ν ≠ 0) :
    (∃ x0 : ℝ, 0 < x0 ∧ 0 < (τ.ν (Set.Ici x0)).toReal) ∨
      (∃ x0 : ℝ, 0 < x0 ∧ 0 < (τ.ν (Set.Iic (-x0))).toReal) := by
  by_cases hRight :
      ∃ x0 : ℝ, 0 < x0 ∧ 0 < (τ.ν (Set.Ici x0)).toReal
  · exact Or.inl hRight
  by_cases hLeft :
      ∃ x0 : ℝ, 0 < x0 ∧ 0 < (τ.ν (Set.Iic (-x0))).toReal
  · exact Or.inr hLeft
  have hRightZero :
      ∀ x : ℝ, 0 < x → τ.ν (Set.Ici x) = 0 := by
    intro x hx
    have hxfinite : τ.ν (Set.Ici x) < ⊤ := canonicalTriple_rightTail_lt_top hτ hx
    by_contra hmass
    have hmass_pos : 0 < (τ.ν (Set.Ici x)).toReal := by
      exact ENNReal.toReal_pos (by exact hmass) hxfinite.ne
    exact hRight ⟨x, hx, hmass_pos⟩
  have hLeftZero :
      ∀ x : ℝ, 0 < x → τ.ν (Set.Iic (-x)) = 0 := by
    intro x hx
    have hxfinite : τ.ν (Set.Iic (-x)) < ⊤ := canonicalTriple_leftTail_lt_top hτ hx
    by_contra hmass
    have hmass_pos : 0 < (τ.ν (Set.Iic (-x))).toReal := by
      exact ENNReal.toReal_pos (by exact hmass) hxfinite.ne
    exact hLeft ⟨x, hx, hmass_pos⟩
  have hcoverZero :
      ∀ n : ℕ, τ.ν (IsCanonicalMeasure.canonicalMeasureCoverSet n) = 0 := by
    intro n
    let c : ℝ := ((n + 1 : ℝ))⁻¹
    have hc_pos : 0 < c := by
      dsimp [c]
      positivity
    have hc_le_one : c ≤ 1 := by
      dsimp [c]
      have hsucc : (1 : ℝ) ≤ n + 1 := by nlinarith
      exact inv_le_one_of_one_le₀ hsucc
    have hsubset :
        IsCanonicalMeasure.canonicalMeasureCoverSet n ⊆ Set.Iic (-c) ∪ Set.Ici c := by
      intro x hx
      dsimp [IsCanonicalMeasure.canonicalMeasureCoverSet, c] at hx
      have hx_sq : c < x ^ (2 : ℕ) := lt_of_lt_of_le hx (min_le_left _ _)
      have hx_abs_gt : c < |x| := by
        by_contra hnot
        have hx_abs_le : |x| ≤ c := le_of_not_gt hnot
        have hx_sq_le : x ^ (2 : ℕ) ≤ c := by
          calc
            x ^ (2 : ℕ) = |x| ^ (2 : ℕ) := by simp [sq_abs]
            _ ≤ c ^ (2 : ℕ) := by gcongr
            _ ≤ c := by
              have hc_nonneg : 0 ≤ c := hc_pos.le
              nlinarith [hc_le_one, sq_nonneg (c - 1)]
        exact not_lt_of_ge hx_sq_le hx_sq
      by_cases hx_nonneg : 0 ≤ x
      · right
        have : c < x := by
          rwa [abs_of_nonneg hx_nonneg] at hx_abs_gt
        exact this.le
      · left
        have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
        have : x < -c := by
          have hnegx_gt : c < -x := by
            simpa [abs_of_neg hx_neg] using hx_abs_gt
          linarith
        exact this.le
    have htail_zero :
        τ.ν (Set.Iic (-c) ∪ Set.Ici c) = 0 := by
      have hleft_zero : τ.ν (Set.Iic (-c)) = 0 := hLeftZero c hc_pos
      have hright_zero : τ.ν (Set.Ici c) = 0 := hRightZero c hc_pos
      refine le_antisymm ?_ bot_le
      calc
        τ.ν (Set.Iic (-c) ∪ Set.Ici c)
            ≤ τ.ν (Set.Iic (-c)) + τ.ν (Set.Ici c) := by
                exact measure_union_le _ _
        _ = 0 := by simp [hleft_zero, hright_zero]
    exact le_antisymm (measure_mono hsubset |> fun hle ↦ le_trans hle htail_zero.le) bot_le
  have hcoverUnionZero :
      τ.ν (⋃ n : ℕ, IsCanonicalMeasure.canonicalMeasureCoverSet n) = 0 := by
    exact measure_iUnion_null hcoverZero
  have hUnivZero :
      τ.ν Set.univ = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      τ.ν Set.univ
          = τ.ν (({0} : Set ℝ) ∪ ⋃ n : ℕ, IsCanonicalMeasure.canonicalMeasureCoverSet n) := by
              rw [IsCanonicalMeasure.canonicalMeasureCover_spanning]
      _ ≤ τ.ν ({0} : Set ℝ) + τ.ν (⋃ n : ℕ, IsCanonicalMeasure.canonicalMeasureCoverSet n) := by
            exact measure_union_le _ _
      _ = 0 := by
            simp [hτ.isCanonicalMeasure.measure_singleton_zero, hcoverUnionZero]
  have hzero : τ.ν = 0 := by
    apply Measure.ext
    intro s hs
    refine le_antisymm ?_ bot_le
    exact le_trans (measure_mono <| Set.subset_univ s) hUnivZero.le
  exact (hν hzero).elim

/-- Helper for Theorem 16.22: exact positive-tail scaling forces every nontrivial scale factor to
be strictly larger than `1`. -/
private lemma scaleGtOne_of_exactTailScaling
    {a : ℕ+ → ℝ} {F : ℝ → ℝ}
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hantitone : AntitoneOn F (Set.Ioi 0))
    (hscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x)
    (hbase : ∃ x0 : ℝ, 0 < x0 ∧ 0 < F x0) :
    ∀ {n : ℕ+}, 1 < (n : ℕ) → 1 < a n := by
  intro n hn
  rcases hbase with ⟨x0, hx0, hFx0⟩
  by_contra hnot
  have han_le_one : a n ≤ 1 := not_lt.mp hnot
  have hdiv_pos : 0 < x0 / a n := div_pos hx0 (ha_pos n)
  have hx0_le_div : x0 ≤ x0 / a n := by
    rw [le_div_iff₀ (ha_pos n)]
    nlinarith
  have htail_le : F (x0 / a n) ≤ F x0 :=
    hantitone hx0 hdiv_pos hx0_le_div
  have htail_eq : F (x0 / a n) = (n : ℝ) * F x0 :=
    hscale n x0 hx0
  have hn_real : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have htail_gt : F x0 < (n : ℝ) * F x0 := by
    nlinarith
  linarith [htail_le, htail_gt, htail_eq]

/-- Helper for Theorem 16.22: exact positive-tail scaling makes the scale sequence strictly
increasing. -/
private lemma scaleStrictMono_of_exactTailScaling
    {a : ℕ+ → ℝ} {F : ℝ → ℝ}
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hantitone : AntitoneOn F (Set.Ioi 0))
    (hscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x)
    (hbase : ∃ x0 : ℝ, 0 < x0 ∧ 0 < F x0) :
    StrictMono a := by
  intro m n hmn
  rcases hbase with ⟨x0, hx0, hFx0⟩
  have hm : F (x0 / a m) = (m : ℝ) * F x0 := hscale m x0 hx0
  have hn : F (x0 / a n) = (n : ℝ) * F x0 := hscale n x0 hx0
  have hFn_lt_Fm : F (x0 / a n) > F (x0 / a m) := by
    have hmn_real : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    rw [hm, hn]
    nlinarith
  by_contra hnot
  have hle : a n ≤ a m := not_lt.mp hnot
  have hdiv : x0 / a m ≤ x0 / a n := by
    rw [div_le_div_iff_of_pos_left hx0 (ha_pos m) (ha_pos n)]
    exact hle
  have hanti := hantitone (div_pos hx0 (ha_pos m)) (div_pos hx0 (ha_pos n)) hdiv
  linarith

/-- Helper for Theorem 16.22: exact positive-tail scaling makes the scale sequence unbounded
above. -/
private lemma scaleUnbounded_of_exactTailScaling
    {a : ℕ+ → ℝ} {F : ℝ → ℝ}
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hantitone : AntitoneOn F (Set.Ioi 0))
    (hscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x)
    (hbase : ∃ x0 : ℝ, 0 < x0 ∧ 0 < F x0) :
    ∀ M : ℝ, ∃ n : ℕ+, M < a n := by
  intro M
  by_cases hM_nonpos : M ≤ 0
  · -- Proof comment: nonpositive thresholds are beaten by the first positive scale.
    exact ⟨1, lt_of_le_of_lt hM_nonpos (ha_pos 1)⟩
  · have hM_pos : 0 < M := lt_of_not_ge hM_nonpos
    rcases hbase with ⟨x0, hx0, hFx0⟩
    by_contra hbounded
    push Not at hbounded
    have hupper :
        ∀ n : ℕ+, F (x0 / a n) ≤ F (x0 / M) := by
      intro n
      have hdiv : x0 / M ≤ x0 / a n := by
        rw [div_le_div_iff_of_pos_left hx0 hM_pos (ha_pos n)]
        exact hbounded n
      exact hantitone (div_pos hx0 hM_pos) (div_pos hx0 (ha_pos n)) hdiv
    obtain ⟨N, hN⟩ := exists_nat_gt (F (x0 / M) / F x0)
    let n : ℕ+ := Nat.succPNat N
    have hratio_lt : F (x0 / M) / F x0 < (n : ℝ) := by
      have hN_lt : F (x0 / M) / F x0 < (N : ℝ) := by
        exact_mod_cast hN
      have hcast : (N : ℝ) < (n : ℝ) := by
        simpa [n, Nat.succPNat_coe]
      exact lt_trans hN_lt hcast
    have hmul_lt : F (x0 / M) < (n : ℝ) * F x0 := by
      exact (div_lt_iff₀ hFx0).1 hratio_lt
    have hmul_le : (n : ℝ) * F x0 ≤ F (x0 / M) := by
      simpa [hscale n x0 hx0] using hupper n
    linarith

/-- Helper for Theorem 16.22: exact positive-tail scaling propagates one positive tail value to
all positive arguments. -/
private lemma tailPositive_of_exactTailScaling
    {a : ℕ+ → ℝ} {F : ℝ → ℝ}
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hantitone : AntitoneOn F (Set.Ioi 0))
    (hscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x)
    (hbase : ∃ x0 : ℝ, 0 < x0 ∧ 0 < F x0) :
    ∀ x : ℝ, 0 < x → 0 < F x := by
  intro x hx
  rcases hbase with ⟨x0, hx0, hFx0⟩
  obtain ⟨n, hn⟩ :=
    scaleUnbounded_of_exactTailScaling ha_pos hantitone hscale ⟨x0, hx0, hFx0⟩ (x / x0)
  have hdiv_pos : 0 < x / a n := div_pos hx (ha_pos n)
  have hdiv_le : x / a n ≤ x0 := by
    rw [div_le_iff₀ (ha_pos n)]
    exact le_of_lt <| by
      have hxmul : (x / x0) * x0 = x := by
        rw [div_eq_mul_inv]
        field_simp [hx0.ne']
      have hscale_lt : (x / x0) * x0 < a n * x0 := by
        exact mul_lt_mul_of_pos_right hn hx0
      simpa [hxmul, mul_comm, mul_left_comm, mul_assoc] using hscale_lt
  have htail_ge : F x0 ≤ F (x / a n) :=
    hantitone hdiv_pos hx0 hdiv_le
  have hmul_pos : 0 < (n : ℝ) * F x := by
    rw [← hscale n x hx]
    exact lt_of_lt_of_le hFx0 htail_ge
  exact (mul_pos_iff_of_pos_left (show 0 < (n : ℝ) by positivity)).1 hmul_pos

/-- Helper for Theorem 16.22: exact tail scaling can be rewritten in multiplicative form. -/
private lemma exactTailScaling_mul
    {a : ℕ+ → ℝ} {F : ℝ → ℝ}
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x) :
    ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (a n * x) = F x / (n : ℝ) := by
  intro n x hx
  have hscaled := hscale n (a n * x) (mul_pos (ha_pos n) hx)
  have hdiv : (a n * x) / a n = x := by
    field_simp [ne_of_gt (ha_pos n)]
  have hn_ne : ((n : ℕ) : ℝ) ≠ 0 := by positivity
  rw [hdiv] at hscaled
  have hmul : (n : ℝ) * F (a n * x) = F x := by
    -- Proof comment: evaluate the original scaling law at the multiplied argument `aₙ x`.
    simpa [mul_comm] using hscaled.symm
  have hdiv' := congrArg (fun z : ℝ ↦ z / (n : ℝ)) hmul
  simpa [hn_ne, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv'

/-- Helper for Theorem 16.22: for a fixed index `α`, the one-sided Lévy tails scale exactly under
the canonical dilations `x ↦ n^(1 / α) x`. -/
private lemma fixedIndex_oneSidedTailScaling
    {μ : ProbabilityMeasure ℝ} {α : ℝ} {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ α)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    (∀ n : ℕ+, ∀ x : ℝ, 0 < x →
      (τ.ν (Set.Ici (((n : ℝ) ^ (1 / α)) * x))).toReal =
        (τ.ν (Set.Ici x)).toReal / (n : ℝ)) ∧
    (∀ n : ℕ+, ∀ x : ℝ, 0 < x →
      (τ.ν (Set.Iic (-(((n : ℝ) ^ (1 / α)) * x)))).toReal =
        (τ.ν (Set.Iic (-x))).toReal / (n : ℝ)) := by
  obtain ⟨d, hscale⟩ := hμ.exists_centering
  have hμ_broad : IsStableInBroadSense μ := by
    refine ⟨hμ.1, ?_⟩
    refine ⟨fun n ↦ (n : ℝ) ^ (1 / α), d, ?_, hscale⟩
    intro n
    exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) _)
  have ha_nonneg : ∀ n : ℕ+, 0 ≤ (n : ℝ) ^ (1 / α) := by
    intro n
    exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) _)
  have ha_pos : ∀ n : ℕ+, 0 < (n : ℝ) ^ (1 / α) := by
    intro n
    exact Real.rpow_pos_of_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) _
  have hscaleν :
      ∀ n : ℕ+, (n : ℕ) • τ.ν =
        Measure.map (fun x : ℝ ↦ (n : ℝ) ^ (1 / α) * x) τ.ν :=
    stableBroad_canonicalTriple_levyMeasureScaling hμ_broad hτ ha_nonneg hscale
  have htail :=
    oneSidedTailScaling_of_levyMeasureScaling hτ.isCanonicalTriple ha_pos hscaleν
  have hscaleRight :
      ∀ n : ℕ+, ∀ x : ℝ, 0 < x →
        (τ.ν (Set.Ici (x / ((n : ℝ) ^ (1 / α))))).toReal =
          (n : ℝ) * (τ.ν (Set.Ici x)).toReal := by
    intro n x hx
    simpa [mul_comm] using (htail.1 n x hx).symm
  have hscaleLeft :
      ∀ n : ℕ+, ∀ x : ℝ, 0 < x →
        (τ.ν (Set.Iic (-(x / ((n : ℝ) ^ (1 / α)))))).toReal =
          (n : ℝ) * (τ.ν (Set.Iic (-x))).toReal := by
    intro n x hx
    simpa [mul_comm] using (htail.2 n x hx).symm
  constructor
  · intro n x hx
    -- Proof comment: the general multiplicative exact-tail-scaling helper specializes directly to
    -- the canonical stable scales `n^(1 / α)`.
    exact exactTailScaling_mul
      (a := fun n : ℕ+ ↦ (n : ℝ) ^ (1 / α))
      (F := fun x : ℝ ↦ (τ.ν (Set.Ici x)).toReal)
      ha_pos hscaleRight n x hx
  · intro n x hx
    -- Proof comment: the same specialization applies to the left-tail function.
    simpa using
      (exactTailScaling_mul
        (a := fun n : ℕ+ ↦ (n : ℝ) ^ (1 / α))
        (F := fun x : ℝ ↦ (τ.ν (Set.Iic (-x))).toReal)
        ha_pos hscaleLeft n x hx)

/-- Helper for Theorem 16.22: on the canonical stable scales `n^(1 / α)`, the one-sided Lévy
tails are already the textbook `1 / n` power law. -/
private lemma fixedIndex_oneSidedTail_onCanonicalScales
    {μ : ProbabilityMeasure ℝ} {α : ℝ} {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ α)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    (∀ n : ℕ+,
      (τ.ν (Set.Ici ((n : ℝ) ^ (1 / α)))).toReal =
        (τ.ν (Set.Ici 1)).toReal / (n : ℝ)) ∧
    (∀ n : ℕ+,
      (τ.ν (Set.Iic (-((n : ℝ) ^ (1 / α))))).toReal =
        (τ.ν (Set.Iic (-1))).toReal / (n : ℝ)) := by
  have htail := fixedIndex_oneSidedTailScaling hμ hτ
  constructor
  · intro n
    -- Proof comment: evaluate the exact scaling identity at the unit cutoff.
    simpa using htail.1 n 1 zero_lt_one
  · intro n
    -- Proof comment: the left-tail formula is the same unit-cutoff specialization.
    simpa using htail.2 n 1 zero_lt_one

/-- Helper for Theorem 16.22: the fixed-index right tail already has the textbook power-law values
on positive rational scales `(m / n)^(1 / α)`. -/
private lemma fixedIndex_rightTail_onPositiveRatios
    {μ : ProbabilityMeasure ℝ} {α : ℝ} {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ α)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    ∀ m n : ℕ+,
      (τ.ν (Set.Ici (((m : ℝ) / (n : ℝ)) ^ (1 / α)))).toReal =
        ((n : ℝ) / (m : ℝ)) * (τ.ν (Set.Ici 1)).toReal := by
  intro m n
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast m.pos
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast n.pos
  have hmn_pos : 0 < ((m : ℝ) / (n : ℝ)) := div_pos hm_pos hn_pos
  have hscale := (fixedIndex_oneSidedTailScaling hμ hτ).1
  have hratio :=
    hscale n (((m : ℝ) / (n : ℝ)) ^ (1 / α)) (Real.rpow_pos_of_pos hmn_pos _)
  have hmul :
      ((n : ℝ) ^ (1 / α)) * (((m : ℝ) / (n : ℝ)) ^ (1 / α)) = (m : ℝ) ^ (1 / α) := by
    -- Proof comment: the rational cutoff is chosen so that the `n^(1 / α)` dilation lands on the
    -- canonical scale `m^(1 / α)`.
    rw [← Real.mul_rpow hn_pos.le hmn_pos.le]
    field_simp [hn_pos.ne']
  have hunit :
      (τ.ν (Set.Ici ((m : ℝ) ^ (1 / α)))).toReal =
        (τ.ν (Set.Ici 1)).toReal / (m : ℝ) := by
    -- Proof comment: evaluate the exact scaling law at the unit cutoff to recover the `1 / m`
    -- normalization.
    simpa using hscale m 1 zero_lt_one
  rw [hmul, hunit] at hratio
  have hratio' := congrArg (fun z : ℝ ↦ z * (n : ℝ)) hratio
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  -- Proof comment: clear the single remaining denominator to isolate the rational power-law
  -- value.
  simp [div_eq_mul_inv, hn_ne] at hratio' ⊢
  linarith

/-- Helper for Theorem 16.22: the fixed-index left tail already has the textbook power-law values
on positive rational scales `(m / n)^(1 / α)`. -/
private lemma fixedIndex_leftTail_onPositiveRatios
    {μ : ProbabilityMeasure ℝ} {α : ℝ} {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ α)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    ∀ m n : ℕ+,
      (τ.ν (Set.Iic (-(((m : ℝ) / (n : ℝ)) ^ (1 / α))))).toReal =
        ((n : ℝ) / (m : ℝ)) * (τ.ν (Set.Iic (-1))).toReal := by
  intro m n
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast m.pos
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast n.pos
  have hmn_pos : 0 < ((m : ℝ) / (n : ℝ)) := div_pos hm_pos hn_pos
  have hscale := (fixedIndex_oneSidedTailScaling hμ hτ).2
  have hratio :=
    hscale n (((m : ℝ) / (n : ℝ)) ^ (1 / α)) (Real.rpow_pos_of_pos hmn_pos _)
  have hmul :
      ((n : ℝ) ^ (1 / α)) * (((m : ℝ) / (n : ℝ)) ^ (1 / α)) = (m : ℝ) ^ (1 / α) := by
    -- Proof comment: the same rational rescaling identity controls the left tail.
    rw [← Real.mul_rpow hn_pos.le hmn_pos.le]
    field_simp [hn_pos.ne']
  have hunit :
      (τ.ν (Set.Iic (-((m : ℝ) ^ (1 / α))))).toReal =
        (τ.ν (Set.Iic (-1))).toReal / (m : ℝ) := by
    -- Proof comment: the left tail has the same canonical `1 / m` normalization at unit cutoff.
    simpa using hscale m 1 zero_lt_one
  rw [hmul, hunit] at hratio
  have hratio' := congrArg (fun z : ℝ ↦ z * (n : ℝ)) hratio
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  -- Proof comment: clear the denominator exactly as in the right-tail computation.
  simp [div_eq_mul_inv, hn_ne] at hratio' ⊢
  linarith

/-- Helper for Theorem 16.22: every positive rational cutoff can be written as a ratio of
positive naturals. -/
private lemma exists_pnat_ratio_eq_of_pos_rat (q : ℚ) (hq : 0 < (q : ℝ)) :
    ∃ m n : ℕ+, (q : ℝ) = (m : ℝ) / (n : ℝ) := by
  have hqRat : 0 < q := by
    exact_mod_cast hq
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hqRat
  have hnum_natAbs_pos : 0 < q.num.natAbs := by
    exact Int.natAbs_pos.mpr hnum_pos.ne'
  let m : ℕ+ := ⟨q.num.natAbs, hnum_natAbs_pos⟩
  let n : ℕ+ := ⟨q.den, Rat.den_pos q⟩
  refine ⟨m, n, ?_⟩
  -- Proof comment: use the reduced numerator/denominator form of `q` and then cast to `ℝ`.
  calc
    (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    _ = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
      rw [Nat.cast_natAbs]
      simp [abs_of_nonneg hnum_pos.le]
    _ = (m : ℝ) / (n : ℝ) := rfl

/-- Helper for Theorem 16.22: the fixed-index right tail already has the textbook power-law
values on every positive rational scale `q^(1 / α)`. -/
private lemma fixedIndex_rightTail_onPositiveQ
    {μ : ProbabilityMeasure ℝ} {α : ℝ} {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ α)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    ∀ q : ℚ, 0 < (q : ℝ) →
      (τ.ν (Set.Ici ((q : ℝ) ^ (1 / α)))).toReal =
        ((q : ℝ)⁻¹) * (τ.ν (Set.Ici 1)).toReal := by
  intro q hq
  obtain ⟨m, n, hqmn⟩ := exists_pnat_ratio_eq_of_pos_rat q hq
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast m.pos
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast n.pos
  have hInv : (((m : ℝ) / (n : ℝ))⁻¹) = (n : ℝ) / (m : ℝ) := by
    field_simp [hm_pos.ne', hn_pos.ne']
  -- Proof comment: after normalizing the rational cutoff to `m / n`, the already proved ratio
  -- formula applies directly.
  rw [hqmn, hInv]
  simpa using fixedIndex_rightTail_onPositiveRatios hμ hτ m n

/-- Helper for Theorem 16.22: the fixed-index left tail already has the textbook power-law
values on every positive rational scale `q^(1 / α)`. -/
private lemma fixedIndex_leftTail_onPositiveQ
    {μ : ProbabilityMeasure ℝ} {α : ℝ} {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ α)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    ∀ q : ℚ, 0 < (q : ℝ) →
      (τ.ν (Set.Iic (-((q : ℝ) ^ (1 / α))))).toReal =
        ((q : ℝ)⁻¹) * (τ.ν (Set.Iic (-1))).toReal := by
  intro q hq
  obtain ⟨m, n, hqmn⟩ := exists_pnat_ratio_eq_of_pos_rat q hq
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast m.pos
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast n.pos
  have hInv : (((m : ℝ) / (n : ℝ))⁻¹) = (n : ℝ) / (m : ℝ) := by
    field_simp [hm_pos.ne', hn_pos.ne']
  -- Proof comment: the negative-half-line formula is the same normalization followed by the left
  -- ratio theorem.
  rw [hqmn, hInv]
  simpa using fixedIndex_leftTail_onPositiveRatios hμ hτ m n

/-- Helper for Theorem 16.22: once the positive-rational cutoffs are known, the fixed-index right
tail has the full power-law formula on every positive cutoff. -/
private lemma fixedIndex_rightTail_powerLaw_allPos
    {μ : ProbabilityMeasure ℝ} {α : ℝ} {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ α)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    ∀ x : ℝ, 0 < x →
      (τ.ν (Set.Ici x)).toReal =
        (τ.ν (Set.Ici 1)).toReal * x ^ (-α) := by
  let F : ℝ → ℝ := fun t ↦ (τ.ν (Set.Ici t)).toReal
  let C : ℝ := F 1
  have hα0 : 0 < α := hμ.index_mem_Ioc.1
  have hanti := canonicalTriple_rightTail_toReal_antitoneOn hτ.isCanonicalTriple
  intro x hx
  let y : ℝ := x ^ α
  have hy_pos : 0 < y := by
    dsimp [y]
    exact Real.rpow_pos_of_pos hx α
  have hFx_nonneg : 0 ≤ F x := by
    dsimp [F]
    exact ENNReal.toReal_nonneg
  have hC_nonneg : 0 ≤ C := by
    dsimp [C, F]
    exact ENNReal.toReal_nonneg
  have htarget_eq : C * x ^ (-α) = C / y := by
    calc
      C * x ^ (-α) = C * (x ^ α)⁻¹ := by rw [Real.rpow_neg hx.le]
      _ = C / y := by simp [y, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hupper :
      ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < y → F x ≤ (q : ℝ)⁻¹ * C := by
    intro q hq_pos hqy
    have hqroot_pos : 0 < (q : ℝ) ^ (1 / α) := Real.rpow_pos_of_pos hq_pos _
    have hqroot_lt : (q : ℝ) ^ (1 / α) < x := by
      simpa [one_div] using
        (Real.rpow_inv_lt_iff_of_pos (le_of_lt hq_pos) hx.le hα0).2 <| by
          simpa [y] using hqy
    have hqmono : F x ≤ F ((q : ℝ) ^ (1 / α)) := hanti hqroot_pos hx hqroot_lt.le
    have hqval := fixedIndex_rightTail_onPositiveQ hμ hτ q hq_pos
    calc
      F x ≤ F ((q : ℝ) ^ (1 / α)) := hqmono
      _ = (q : ℝ)⁻¹ * C := by simpa [F, C] using hqval
  have hlower :
      ∀ r : ℚ, y < (r : ℝ) → 0 < (r : ℝ) → (r : ℝ)⁻¹ * C ≤ F x := by
    intro r hyr hr_pos
    have hrroot_pos : 0 < (r : ℝ) ^ (1 / α) := Real.rpow_pos_of_pos hr_pos _
    have hx_lt_hrroot : x < (r : ℝ) ^ (1 / α) := by
      simpa [one_div] using
        (Real.lt_rpow_inv_iff_of_pos hx.le (le_of_lt hr_pos) hα0).2 <| by
          simpa [y] using hyr
    have hrmono : F ((r : ℝ) ^ (1 / α)) ≤ F x := hanti hx hrroot_pos hx_lt_hrroot.le
    have hrval := fixedIndex_rightTail_onPositiveQ hμ hτ r hr_pos
    calc
      (r : ℝ)⁻¹ * C = F ((r : ℝ) ^ (1 / α)) := by simpa [F, C] using hrval.symm
      _ ≤ F x := hrmono
  by_cases hCzero : C = 0
  · -- Proof comment: if the unit right tail vanishes, every rational upper bound forces the
    -- whole right-tail function to vanish at `x`.
    obtain ⟨q, hq_pos, hqy⟩ := exists_rat_btwn hy_pos
    have hFx_le_zero : F x ≤ 0 := by
      simpa [hCzero] using hupper q hq_pos hqy
    have hFx_zero : F x = 0 := le_antisymm hFx_le_zero hFx_nonneg
    simpa [F, C, hCzero, hFx_zero]
  · have hC_ne : 0 ≠ C := by simpa [eq_comm] using hCzero
    have hC_pos : 0 < C := lt_of_le_of_ne hC_nonneg hC_ne
    have htarget_nonneg : 0 ≤ C * x ^ (-α) := by
      exact mul_nonneg hC_nonneg (Real.rpow_nonneg hx.le _)
    have htarget_upper : F x ≤ C * x ^ (-α) := by
      by_contra hgt
      have hgt' : C * x ^ (-α) < F x := lt_of_not_ge hgt
      have hFx_pos : 0 < F x := lt_of_le_of_lt htarget_nonneg hgt'
      have hdiv_lt : C / F x < y := by
        have hmul_lt : C < F x * y := by
          have htarget_div : C / y < F x := by simpa [htarget_eq] using hgt'
          exact (div_lt_iff₀ hy_pos).1 htarget_div
        exact (div_lt_iff₀ hFx_pos).2 <| by simpa [mul_comm] using hmul_lt
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hdiv_lt
      have hq_pos : 0 < (q : ℝ) := lt_of_le_of_lt (div_nonneg hC_nonneg hFx_nonneg) hq1
      have hqbound_lt : C / (q : ℝ) < F x := by
        have hmul_lt : C < (q : ℝ) * F x := by
          exact (div_lt_iff₀ hFx_pos).1 hq1
        exact (div_lt_iff₀ hq_pos).2 <| by simpa [mul_comm] using hmul_lt
      have hFx_le_qbound : F x ≤ C / (q : ℝ) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hupper q hq_pos hq2
      exact (not_le_of_gt hqbound_lt) hFx_le_qbound
    have htarget_lower : C * x ^ (-α) ≤ F x := by
      by_contra hlt
      have hlt' : F x < C * x ^ (-α) := lt_of_not_ge hlt
      obtain ⟨r0, hyr0, hr0⟩ := exists_rat_btwn (lt_add_one y)
      have hr0_pos : 0 < (r0 : ℝ) := lt_trans hy_pos hyr0
      have hFx_pos : 0 < F x := by
        have hr0bound : (r0 : ℝ)⁻¹ * C ≤ F x := hlower r0 hyr0 hr0_pos
        have hr0bound_pos : 0 < (r0 : ℝ)⁻¹ * C := by
          exact mul_pos (inv_pos.mpr hr0_pos) hC_pos
        exact lt_of_lt_of_le hr0bound_pos hr0bound
      have hy_lt_div : y < C / F x := by
        have hmul_lt : F x * y < C := by
          have htarget_div : F x < C / y := by simpa [htarget_eq] using hlt'
          exact (lt_div_iff₀ hy_pos).1 htarget_div
        exact (lt_div_iff₀ hFx_pos).2 <| by simpa [mul_comm] using hmul_lt
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hy_lt_div
      have hr_pos : 0 < (r : ℝ) := lt_trans hy_pos hr1
      have hrbound_le : C / (r : ℝ) ≤ F x := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlower r hr1 hr_pos
      have hFx_lt_rbound : F x < C / (r : ℝ) := by
        have hmul_lt : F x * (r : ℝ) < C := by
          have : (r : ℝ) * F x < C := (lt_div_iff₀ hFx_pos).1 hr2
          simpa [mul_comm] using this
        exact (lt_div_iff₀ hr_pos).2 <| by simpa [mul_comm] using hmul_lt
      exact (not_le_of_gt hFx_lt_rbound) hrbound_le
    simpa [F, C] using le_antisymm htarget_upper htarget_lower

/-- Helper for Theorem 16.22: once the positive-rational cutoffs are known, the fixed-index left
tail has the full power-law formula on every positive cutoff. -/
private lemma fixedIndex_leftTail_powerLaw_allPos
    {μ : ProbabilityMeasure ℝ} {α : ℝ} {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ α)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    ∀ x : ℝ, 0 < x →
      (τ.ν (Set.Iic (-x))).toReal =
        (τ.ν (Set.Iic (-1))).toReal * x ^ (-α) := by
  let F : ℝ → ℝ := fun t ↦ (τ.ν (Set.Iic (-t))).toReal
  let C : ℝ := F 1
  have hα0 : 0 < α := hμ.index_mem_Ioc.1
  have hanti := canonicalTriple_leftTail_toReal_antitoneOn hτ.isCanonicalTriple
  intro x hx
  let y : ℝ := x ^ α
  have hy_pos : 0 < y := by
    dsimp [y]
    exact Real.rpow_pos_of_pos hx α
  have hFx_nonneg : 0 ≤ F x := by
    dsimp [F]
    exact ENNReal.toReal_nonneg
  have hC_nonneg : 0 ≤ C := by
    dsimp [C, F]
    exact ENNReal.toReal_nonneg
  have htarget_eq : C * x ^ (-α) = C / y := by
    calc
      C * x ^ (-α) = C * (x ^ α)⁻¹ := by rw [Real.rpow_neg hx.le]
      _ = C / y := by simp [y, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hupper :
      ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < y → F x ≤ (q : ℝ)⁻¹ * C := by
    intro q hq_pos hqy
    have hqroot_pos : 0 < (q : ℝ) ^ (1 / α) := Real.rpow_pos_of_pos hq_pos _
    have hqroot_lt : (q : ℝ) ^ (1 / α) < x := by
      simpa [one_div] using
        (Real.rpow_inv_lt_iff_of_pos (le_of_lt hq_pos) hx.le hα0).2 <| by
          simpa [y] using hqy
    have hqmono : F x ≤ F ((q : ℝ) ^ (1 / α)) := hanti hqroot_pos hx hqroot_lt.le
    have hqval := fixedIndex_leftTail_onPositiveQ hμ hτ q hq_pos
    calc
      F x ≤ F ((q : ℝ) ^ (1 / α)) := hqmono
      _ = (q : ℝ)⁻¹ * C := by simpa [F, C] using hqval
  have hlower :
      ∀ r : ℚ, y < (r : ℝ) → 0 < (r : ℝ) → (r : ℝ)⁻¹ * C ≤ F x := by
    intro r hyr hr_pos
    have hrroot_pos : 0 < (r : ℝ) ^ (1 / α) := Real.rpow_pos_of_pos hr_pos _
    have hx_lt_hrroot : x < (r : ℝ) ^ (1 / α) := by
      simpa [one_div] using
        (Real.lt_rpow_inv_iff_of_pos hx.le (le_of_lt hr_pos) hα0).2 <| by
          simpa [y] using hyr
    have hrmono : F ((r : ℝ) ^ (1 / α)) ≤ F x := hanti hx hrroot_pos hx_lt_hrroot.le
    have hrval := fixedIndex_leftTail_onPositiveQ hμ hτ r hr_pos
    calc
      (r : ℝ)⁻¹ * C = F ((r : ℝ) ^ (1 / α)) := by simpa [F, C] using hrval.symm
      _ ≤ F x := hrmono
  by_cases hCzero : C = 0
  · -- Proof comment: the same rational upper squeeze collapses the entire left tail to zero.
    obtain ⟨q, hq_pos, hqy⟩ := exists_rat_btwn hy_pos
    have hFx_le_zero : F x ≤ 0 := by
      simpa [hCzero] using hupper q hq_pos hqy
    have hFx_zero : F x = 0 := le_antisymm hFx_le_zero hFx_nonneg
    simpa [F, C, hCzero, hFx_zero]
  · have hC_ne : 0 ≠ C := by simpa [eq_comm] using hCzero
    have hC_pos : 0 < C := lt_of_le_of_ne hC_nonneg hC_ne
    have htarget_nonneg : 0 ≤ C * x ^ (-α) := by
      exact mul_nonneg hC_nonneg (Real.rpow_nonneg hx.le _)
    have htarget_upper : F x ≤ C * x ^ (-α) := by
      by_contra hgt
      have hgt' : C * x ^ (-α) < F x := lt_of_not_ge hgt
      have hFx_pos : 0 < F x := lt_of_le_of_lt htarget_nonneg hgt'
      have hdiv_lt : C / F x < y := by
        have hmul_lt : C < F x * y := by
          have htarget_div : C / y < F x := by simpa [htarget_eq] using hgt'
          exact (div_lt_iff₀ hy_pos).1 htarget_div
        exact (div_lt_iff₀ hFx_pos).2 <| by simpa [mul_comm] using hmul_lt
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hdiv_lt
      have hq_pos : 0 < (q : ℝ) := lt_of_le_of_lt (div_nonneg hC_nonneg hFx_nonneg) hq1
      have hqbound_lt : C / (q : ℝ) < F x := by
        have hmul_lt : C < (q : ℝ) * F x := by
          exact (div_lt_iff₀ hFx_pos).1 hq1
        exact (div_lt_iff₀ hq_pos).2 <| by simpa [mul_comm] using hmul_lt
      have hFx_le_qbound : F x ≤ C / (q : ℝ) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hupper q hq_pos hq2
      exact (not_le_of_gt hqbound_lt) hFx_le_qbound
    have htarget_lower : C * x ^ (-α) ≤ F x := by
      by_contra hlt
      have hlt' : F x < C * x ^ (-α) := lt_of_not_ge hlt
      obtain ⟨r0, hyr0, hr0⟩ := exists_rat_btwn (lt_add_one y)
      have hr0_pos : 0 < (r0 : ℝ) := lt_trans hy_pos hyr0
      have hFx_pos : 0 < F x := by
        have hr0bound : (r0 : ℝ)⁻¹ * C ≤ F x := hlower r0 hyr0 hr0_pos
        have hr0bound_pos : 0 < (r0 : ℝ)⁻¹ * C := by
          exact mul_pos (inv_pos.mpr hr0_pos) hC_pos
        exact lt_of_lt_of_le hr0bound_pos hr0bound
      have hy_lt_div : y < C / F x := by
        have hmul_lt : F x * y < C := by
          have htarget_div : F x < C / y := by simpa [htarget_eq] using hlt'
          exact (lt_div_iff₀ hy_pos).1 htarget_div
        exact (lt_div_iff₀ hFx_pos).2 <| by simpa [mul_comm] using hmul_lt
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hy_lt_div
      have hr_pos : 0 < (r : ℝ) := lt_trans hy_pos hr1
      have hrbound_le : C / (r : ℝ) ≤ F x := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlower r hr1 hr_pos
      have hFx_lt_rbound : F x < C / (r : ℝ) := by
        have hmul_lt : F x * (r : ℝ) < C := by
          have : (r : ℝ) * F x < C := (lt_div_iff₀ hFx_pos).1 hr2
          simpa [mul_comm] using this
        exact (lt_div_iff₀ hr_pos).2 <| by simpa [mul_comm] using hmul_lt
      exact (not_le_of_gt hFx_lt_rbound) hrbound_le
    simpa [F, C] using le_antisymm htarget_upper htarget_lower

/-- Helper for Theorem 16.22: the stable Lévy density is a measurable branchwise power kernel. -/
private lemma measurable_stableLevyDensity (α cMinus cPlus : ℝ) :
    Measurable (stableLevyDensity α cMinus cPlus) := by
  have hneg : Measurable (fun x : ℝ ↦ cMinus * (-x) ^ (-α - 1)) := by
    fun_prop
  have hpos : Measurable (fun x : ℝ ↦ cPlus * x ^ (-α - 1)) := by
    fun_prop
  simpa [stableLevyDensity_apply] using
    (Measurable.ite measurableSet_Iio hneg
      (Measurable.ite measurableSet_Ioi hpos measurable_const))

/-- Helper for Theorem 16.22: the model stable Lévy measure has the textbook right-tail
power law on `(0, ∞)`. -/
private lemma stableLevyMeasure_rightTail_toReal
    {α cPlus x : ℝ} (hα0 : 0 < α) (hcPlus : 0 ≤ cPlus) (hx : 0 < x) :
    ((stableLevyMeasure α 0 cPlus) (Set.Ici x)).toReal = (cPlus / α) * x ^ (-α) := by
  have hmeas : Measurable (stableLevyDensity α 0 cPlus) :=
    measurable_stableLevyDensity α 0 cPlus
  rw [stableLevyMeasure_def, withDensity_apply _ measurableSet_Ici]
  change
    (∫⁻ a in Set.Ici x, ENNReal.ofReal (stableLevyDensity α 0 cPlus a) ∂volume).toReal =
      (cPlus / α) * x ^ (-α)
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ici x)] fun a : ℝ ↦ stableLevyDensity α 0 cPlus a := by
    filter_upwards with a
    exact stableLevyDensity_nonneg le_rfl hcPlus a
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable]
  have hkernel :
      ∫ a in Set.Ici x, stableLevyDensity α 0 cPlus a ∂volume =
        ∫ a in Set.Ioi x, cPlus * a ^ (-α - 1) ∂volume := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun a ha ↦ ?_
    have ha_pos : 0 < a := lt_trans hx ha
    have hnot_neg : ¬ a < 0 := by
      linarith
    -- Proof comment: once `a > x > 0`, only the positive branch of the stable density survives.
    rw [stableLevyDensity_apply]
    simp [hnot_neg, ha_pos]
  have hα_lt : -α - 1 < -1 := by
    linarith
  rw [hkernel, integral_const_mul, integral_Ioi_rpow_of_lt hα_lt hx]
  have hαne : α ≠ 0 := by
    linarith
  field_simp [hαne]
  ring

/-- Helper for Theorem 16.22: the model stable Lévy measure has the textbook left-tail
power law on `(-∞, 0)`. -/
private lemma stableLevyMeasure_leftTail_toReal
    {α cMinus x : ℝ} (hα0 : 0 < α) (hcMinus : 0 ≤ cMinus) (hx : 0 < x) :
    ((stableLevyMeasure α cMinus 0) (Set.Iic (-x))).toReal = (cMinus / α) * x ^ (-α) := by
  have hmeas : Measurable (stableLevyDensity α cMinus 0) :=
    measurable_stableLevyDensity α cMinus 0
  rw [stableLevyMeasure_def, withDensity_apply _ measurableSet_Iic]
  change
    (∫⁻ a in Set.Iic (-x), ENNReal.ofReal (stableLevyDensity α cMinus 0 a) ∂volume).toReal =
      (cMinus / α) * x ^ (-α)
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Iic (-x))] fun a : ℝ ↦ stableLevyDensity α cMinus 0 a := by
    filter_upwards with a
    exact stableLevyDensity_nonneg hcMinus le_rfl a
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable]
  have hkernel :
      ∫ a in Set.Iic (-x), stableLevyDensity α cMinus 0 a ∂volume =
        ∫ a in Set.Iio (-x), cMinus * (-a) ^ (-α - 1) ∂volume := by
    rw [MeasureTheory.integral_Iic_eq_integral_Iio]
    refine setIntegral_congr_fun measurableSet_Iio fun a ha ↦ ?_
    have ha_lt : a < -x := ha
    have ha_neg : a < 0 := by
      linarith
    -- Proof comment: on the strict left ray, only the negative branch of the density contributes.
    rw [stableLevyDensity_apply]
    simp [ha_neg]
  have hcomp :
      ∫ a in Set.Iio (-x), cMinus * (-a) ^ (-α - 1) ∂volume =
        ∫ a in Set.Ioi x, cMinus * a ^ (-α - 1) ∂volume := by
    calc
      ∫ a in Set.Iio (-x), cMinus * (-a) ^ (-α - 1) ∂volume
          = ∫ a in Set.Iic (-x), cMinus * (-a) ^ (-α - 1) ∂volume := by
              rw [← MeasureTheory.integral_Iic_eq_integral_Iio]
      _ = ∫ a in Set.Ioi x, cMinus * a ^ (-α - 1) ∂volume := by
            simpa using
              (integral_comp_neg_Iic (-x) (fun t : ℝ ↦ cMinus * t ^ (-α - 1)))
  have hα_lt : -α - 1 < -1 := by
    linarith
  rw [hkernel, hcomp, integral_const_mul, integral_Ioi_rpow_of_lt hα_lt hx]
  have hαne : α ≠ 0 := by
    linarith
  field_simp [hαne]
  ring

/-- Helper for Theorem 16.22: if both one-sided coefficients vanish, the model stable Lévy
measure is the zero measure. -/
private lemma stableLevyMeasure_zero_zero (α : ℝ) :
    stableLevyMeasure α 0 0 = 0 := by
  rw [stableLevyMeasure_def]
  simp [stableLevyDensity_apply]

/-- Helper for Theorem 16.22: exact tail scaling together with decay at infinity forces the
normalization `a₁ = 1`. -/
private lemma scaleOne_eq_one_of_exactTailScaling
    {a : ℕ+ → ℝ} {F : ℝ → ℝ}
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x)
    (hzero : Tendsto F atTop (𝓝 0))
    (hbase : ∃ x0 : ℝ, 0 < x0 ∧ 0 < F x0) :
    a 1 = 1 := by
  rcases hbase with ⟨x0, hx0, hFx0⟩
  have hsmall : ∀ᶠ x : ℝ in atTop, |F x| < F x0 / 2 := by
    have hball := hzero.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < F x0 / 2))
    simpa [Metric.mem_ball, Real.dist_eq] using hball
  by_cases hlt : a 1 < 1
  · have hq_gt : 1 < (a 1)⁻¹ := by
      rw [one_lt_inv₀ (ha_pos 1)]
      exact hlt
    let u : ℕ → ℝ := fun k ↦ (a 1)⁻¹ ^ k * x0
    have hseq :
        Tendsto u atTop atTop := by
      simpa [u, mul_comm] using
        Tendsto.atTop_mul_const hx0 (tendsto_pow_atTop_atTop_of_one_lt hq_gt)
    have hconst : ∀ k : ℕ, F (u k) = F x0 := by
      intro k
      induction k with
      | zero =>
          simp [u]
      | succ k hk =>
          have hk_pos : 0 < u k := by
            dsimp [u]
            exact mul_pos (pow_pos (inv_pos.mpr (ha_pos 1)) k) hx0
          have hrewrite :
              u (k + 1) = u k / a 1 := by
            dsimp [u]
            rw [pow_succ]
            ring
          rw [hrewrite]
          -- Proof comment: each division by `a₁` leaves the tail value unchanged when `n = 1`.
          rw [hscale 1 _ hk_pos, hk]
          norm_num
    have hEventNat : ∀ᶠ k : ℕ in atTop, |F (u k)| < F x0 / 2 := by
      simpa [u] using (hseq.eventually hsmall)
    rcases hEventNat.exists with ⟨k, hk⟩
    have hbadAbs : |F x0| < F x0 / 2 := by
      simpa [hconst k] using hk
    have hbad : F x0 < F x0 / 2 := by
      simpa [abs_of_pos hFx0] using hbadAbs
    linarith
  by_cases hgt : 1 < a 1
  · let u : ℕ → ℝ := fun k ↦ (a 1) ^ k * x0
    have hseq :
        Tendsto u atTop atTop := by
      simpa [u, mul_comm] using
        Tendsto.atTop_mul_const hx0 (tendsto_pow_atTop_atTop_of_one_lt hgt)
    have hconst : ∀ k : ℕ, F (u k) = F x0 := by
      intro k
      induction k with
      | zero =>
          simp [u]
      | succ k hk =>
          have hk_pos : 0 < u k := by
            simp [u]
            positivity
          have hrewrite :
              u (k + 1) = a 1 * u k := by
            dsimp [u]
            rw [pow_succ]
            ring
          rw [hrewrite]
          -- Proof comment: multiplying by `a₁` also preserves the tail value because the
          -- `n = 1` scaling identity is an equality.
          rw [exactTailScaling_mul ha_pos hscale 1 _ hk_pos, hk]
          norm_num
    have hEventNat : ∀ᶠ k : ℕ in atTop, |F (u k)| < F x0 / 2 := by
      simpa [u] using (hseq.eventually hsmall)
    rcases hEventNat.exists with ⟨k, hk⟩
    have hbadAbs : |F x0| < F x0 / 2 := by
      simpa [hconst k] using hk
    have hbad : F x0 < F x0 / 2 := by
      simpa [abs_of_pos hFx0] using hbadAbs
    linarith
  exact le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)

/-- Helper for Theorem 16.22: adjacent exact tail scales act by a fixed geometric decay factor on
positive arguments. -/
private lemma adjacentRatioTailScaling_of_exactTailScaling
    {a : ℕ+ → ℝ} {F : ℝ → ℝ}
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F ((a (Nat.succPNat (n + 1)) / a (Nat.succPNat n)) * x) =
        ((n + 1 : ℝ) / (n + 2 : ℝ)) * F x := by
  intro n x hx
  have hdiv_pos : 0 < x / a (Nat.succPNat n) := by
    exact div_pos hx (ha_pos (Nat.succPNat n))
  calc
    F ((a (Nat.succPNat (n + 1)) / a (Nat.succPNat n)) * x)
        = F (a (Nat.succPNat (n + 1)) * (x / a (Nat.succPNat n))) := by
            have hne : a (Nat.succPNat n) ≠ 0 := ne_of_gt (ha_pos (Nat.succPNat n))
            field_simp [hne]
    _ = F (x / a (Nat.succPNat n)) / ((Nat.succPNat (n + 1) : ℕ) : ℝ) := by
          exact exactTailScaling_mul ha_pos hscale (Nat.succPNat (n + 1))
            (x / a (Nat.succPNat n)) hdiv_pos
    _ = (((Nat.succPNat n : ℕ) : ℝ) * F x) / ((Nat.succPNat (n + 1) : ℕ) : ℝ) := by
          rw [hscale (Nat.succPNat n) x hx]
    _ = ((n + 1 : ℝ) / (n + 2 : ℝ)) * F x := by
          have hsucc1 : (((Nat.succPNat n : ℕ) : ℝ)) = n + 1 := by
            norm_num [Nat.succPNat_coe]
          have hsucc2 : (((Nat.succPNat (n + 1) : ℕ) : ℝ)) = n + 2 := by
            simpa [Nat.succPNat_coe, Nat.cast_add, Nat.cast_one, add_assoc]
          rw [hsucc1, hsucc2]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring

/-- Helper for Theorem 16.22: exact tail scaling forces the adjacent scale ratios to be
antitone. -/
private lemma adjacentScaleRatio_antitone_of_exactTailScaling
    {a : ℕ+ → ℝ} {F : ℝ → ℝ}
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hantitone : AntitoneOn F (Set.Ioi 0))
    (hscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x)
    (hbase : ∃ x0 : ℝ, 0 < x0 ∧ 0 < F x0) :
    Antitone fun n : ℕ ↦ a (Nat.succPNat (n + 1)) / a (Nat.succPNat n) := by
  intro m n hmn
  by_contra hratio
  let qm : ℝ := a (Nat.succPNat (m + 1)) / a (Nat.succPNat m)
  let qn : ℝ := a (Nat.succPNat (n + 1)) / a (Nat.succPNat n)
  have hq : qm < qn := by
    exact lt_of_not_ge hratio
  rcases hbase with ⟨x0, hx0, hFx0⟩
  have hqm_pos : 0 < qm := by
    dsimp [qm]
    exact div_pos (ha_pos (Nat.succPNat (m + 1))) (ha_pos (Nat.succPNat m))
  have hqn_pos : 0 < qn := by
    dsimp [qn]
    exact div_pos (ha_pos (Nat.succPNat (n + 1))) (ha_pos (Nat.succPNat n))
  let x : ℝ := x0 / qn
  have hx : 0 < x := by
    dsimp [x]
    exact div_pos hx0 hqn_pos
  have hqx : qm * x < qn * x := by
    dsimp [x]
    exact mul_lt_mul_of_pos_right hq (div_pos hx0 hqn_pos)
  have hqn_mul : qn * x = x0 := by
    dsimp [x]
    field_simp [hqn_pos.ne']
  have hScaleM := adjacentRatioTailScaling_of_exactTailScaling ha_pos hscale m x hx
  have hScaleN := adjacentRatioTailScaling_of_exactTailScaling ha_pos hscale n x hx
  have hFx_pos : 0 < F x := by
    have hrn_pos : 0 < ((n + 1 : ℝ) / (n + 2 : ℝ)) := by positivity
    have hFqx_pos : 0 < F (qn * x) := by
      simpa [hqn_mul] using hFx0
    rw [hScaleN] at hFqx_pos
    nlinarith
  have hanti :
      F (qm * x) ≥ F (qn * x) := by
    exact hantitone (mul_pos hqm_pos hx) (mul_pos hqn_pos hx) hqx.le
  have hmn_ne : m ≠ n := by
    intro hmn_eq
    subst hmn_eq
    exact lt_irrefl _ hq
  have hmn_lt : m < n := lt_of_le_of_ne hmn hmn_ne
  have hsum_lt : (m : ℝ) + 2 < (n : ℝ) + 2 := by
    exact_mod_cast Nat.add_lt_add_right hmn_lt 2
  have hInv_lt : 1 / ((n : ℝ) + 2) < 1 / ((m : ℝ) + 2) := by
    exact one_div_lt_one_div_of_lt (by positivity) hsum_lt
  have hrm :
      ((m + 1 : ℝ) / (m + 2 : ℝ)) = 1 - 1 / ((m : ℝ) + 2) := by
    field_simp
    ring
  have hrn :
      ((n + 1 : ℝ) / (n + 2 : ℝ)) = 1 - 1 / ((n : ℝ) + 2) := by
    field_simp
    ring
  have hratio_lt :
      ((m + 1 : ℝ) / (m + 2 : ℝ)) < ((n + 1 : ℝ) / (n + 2 : ℝ)) := by
    rw [hrm, hrn]
    linarith
  have hscale_lt :
      ((m + 1 : ℝ) / (m + 2 : ℝ)) * F x < ((n + 1 : ℝ) / (n + 2 : ℝ)) * F x := by
    exact mul_lt_mul_of_pos_right hratio_lt hFx_pos
  rw [hScaleM, hScaleN] at hanti
  linarith

/-- Helper for Theorem 16.22: the Gaussian-branch truncated kernels. -/
private def stableBroadIndexTwoScaledTruncation (n : ℕ) (x : ℝ) : ℝ :=
  ((n + 1 : ℝ)⁻¹) * min (((n + 1 : ℝ) * x ^ (2 : ℕ))) (1 : ℝ)

/-- Helper for Theorem 16.22: every Gaussian-branch truncated kernel is dominated by the
canonical integrand `x ↦ min (x^2) 1`. -/
private lemma stableBroad_indexTwo_scaledTruncation_le (n : ℕ) (x : ℝ) :
    stableBroadIndexTwoScaledTruncation n x ≤ min (x ^ (2 : ℕ)) 1 := by
  let m : ℝ := n + 1
  have hm_pos : 0 < m := by
    dsimp [m]
    positivity
  have hm_one : (1 : ℝ) ≤ m := by
    dsimp [m]
    norm_num
  by_cases hcut : m * x ^ (2 : ℕ) ≤ 1
  · have hx_le_one : x ^ (2 : ℕ) ≤ 1 := by
      calc
        x ^ (2 : ℕ) ≤ m * x ^ (2 : ℕ) := by
          have hx_nonneg : 0 ≤ x ^ (2 : ℕ) := by positivity
          nlinarith
        _ ≤ 1 := hcut
    -- Proof comment: on the small branch the truncation does not cut anything off.
    dsimp [stableBroadIndexTwoScaledTruncation, m]
    rw [min_eq_left hcut]
    field_simp [hm_pos.ne']
    rw [min_eq_left hx_le_one]
  · have hcut' : 1 < m * x ^ (2 : ℕ) := lt_of_not_ge hcut
    have hm_inv_le_sq : m⁻¹ ≤ x ^ (2 : ℕ) := by
      have hm_inv_lt_sq : m⁻¹ < x ^ (2 : ℕ) := by
        rw [inv_lt_iff_one_lt_mul₀ hm_pos]
        simpa [mul_comm] using hcut'
      exact le_of_lt hm_inv_lt_sq
    have hm_inv_le_one : m⁻¹ ≤ (1 : ℝ) := by
      have hneq : m ≠ 0 := hm_pos.ne'
      field_simp [one_div, hneq]
      nlinarith
    -- Proof comment: on the large branch the truncated kernel is exactly `(n + 1)⁻¹`, which is
    -- below both `x^2` and `1`.
    dsimp [stableBroadIndexTwoScaledTruncation, m]
    rw [min_eq_right (le_of_lt hcut')]
    simpa using (le_min hm_inv_le_sq hm_inv_le_one)

/-- Helper for Theorem 16.22: the Gaussian-branch truncated kernels vanish pointwise. -/
private lemma stableBroad_indexTwo_scaledTruncation_tendsto_zero (x : ℝ) :
    Tendsto (fun n : ℕ ↦ stableBroadIndexTwoScaledTruncation n x) atTop (𝓝 0) := by
  have hnonneg :
      ∀ n : ℕ, 0 ≤ stableBroadIndexTwoScaledTruncation n x := by
    intro n
    dsimp [stableBroadIndexTwoScaledTruncation]
    positivity
  have hbound :
      ∀ᶠ n : ℕ in atTop, stableBroadIndexTwoScaledTruncation n x ≤ 1 / ((n : ℝ) + 1) :=
    Filter.Eventually.of_forall fun n ↦ by
      dsimp [stableBroadIndexTwoScaledTruncation]
      have hmin : min (((n + 1 : ℝ) * x ^ (2 : ℕ))) (1 : ℝ) ≤ 1 := min_le_right _ _
      have hmul :
          ((n + 1 : ℝ)⁻¹) * min (((n + 1 : ℝ) * x ^ (2 : ℕ))) (1 : ℝ) ≤
            ((n + 1 : ℝ)⁻¹) * 1 := by
        gcongr
      simpa using hmul
  -- Proof comment: the kernels are uniformly squeezed between `0` and the reciprocal sequence.
  exact squeeze_zero'
    (Filter.Eventually.of_forall hnonneg)
    hbound
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- Helper for Theorem 16.22: the Lévy-measure scaling identity keeps the Gaussian-branch
truncated integral constant. -/
private lemma stableBroad_indexTwo_scaledTruncation_integral_eq
    {τ : LevyKhinchinTriple}
    (hscaleν : ∀ n : ℕ+, (n : ℕ) • τ.ν =
      Measure.map (fun x : ℝ ↦ (n : ℝ) ^ (1 / (2 : ℝ)) * x) τ.ν)
    (n : ℕ) :
    ∫ x, stableBroadIndexTwoScaledTruncation n x ∂τ.ν =
      ∫ x, min (x ^ (2 : ℕ)) 1 ∂τ.ν := by
  let m : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  have hm_cast : ((m : ℕ) : ℝ) = (n + 1 : ℝ) := by
    norm_num [m]
  have hm_nonneg : 0 ≤ ((m : ℕ) : ℝ) := by positivity
  have hm_pos : 0 < ((m : ℕ) : ℝ) := by positivity
  have hpow :
      ∀ x : ℝ,
        min ((((m : ℝ) ^ (1 / (2 : ℝ)) * x) ^ (2 : ℕ))) (1 : ℝ) =
          min (((m : ℝ) * x ^ (2 : ℕ))) (1 : ℝ) := by
    intro x
    have hsqrt : ((m : ℝ) ^ (1 / (2 : ℝ))) = Real.sqrt (m : ℝ) := by
      simpa using (Real.sqrt_eq_rpow (m : ℝ)).symm
    rw [hsqrt, pow_two]
    rw [show (Real.sqrt (m : ℝ) * x) * (Real.sqrt (m : ℝ) * x) = (m : ℝ) * x ^ (2 : ℕ) by
      calc
        (Real.sqrt (m : ℝ) * x) * (Real.sqrt (m : ℝ) * x)
            = (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) * (x * x) := by ring
        _ = (m : ℝ) * x ^ (2 : ℕ) := by
            rw [show Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) by
              nlinarith [Real.sq_sqrt hm_nonneg], pow_two]
      ]
  have hscaleν' :
      (m : ℕ) • τ.ν =
        Measure.map (fun x : ℝ ↦ (m : ℝ) ^ (1 / (2 : ℝ)) * x) τ.ν := by
    exact hscaleν m
  calc
    ∫ x, stableBroadIndexTwoScaledTruncation n x ∂τ.ν
        = ((n + 1 : ℝ)⁻¹) *
            ∫ x, min (((n + 1 : ℝ) * x ^ (2 : ℕ))) (1 : ℝ) ∂τ.ν := by
              simp [stableBroadIndexTwoScaledTruncation, integral_const_mul]
    _ = ((n + 1 : ℝ)⁻¹) *
          ∫ x, min ((((m : ℝ) ^ (1 / (2 : ℝ)) * x) ^ (2 : ℕ))) (1 : ℝ) ∂τ.ν := by
            congr 2
            funext x
            simpa [hm_cast] using (hpow x).symm
    _ = ((n + 1 : ℝ)⁻¹) *
          ∫ x, min (x ^ (2 : ℕ)) 1 ∂Measure.map
            (fun x : ℝ ↦ (m : ℝ) ^ (1 / (2 : ℝ)) * x) τ.ν := by
              rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ((n + 1 : ℝ)⁻¹) * ∫ x, min (x ^ (2 : ℕ)) 1 ∂((m : ℕ) • τ.ν) := by
            rw [← hscaleν']
    _ = ((n + 1 : ℝ)⁻¹) * (((m : ℕ) : ℝ) * ∫ x, min (x ^ (2 : ℕ)) 1 ∂τ.ν) := by
            have hmeasure : ((m : ℕ) • τ.ν) = ((((m : ℕ) : ENNReal) • τ.ν) : Measure ℝ) := by
              ext s hs
              simp [nsmul_eq_mul]
            rw [hmeasure, integral_smul_measure]
            simp
    _ = ∫ x, min (x ^ (2 : ℕ)) 1 ∂τ.ν := by
          have hneq : (n + 1 : ℝ) ≠ 0 := by positivity
          field_simp [hneq]
          simpa [hm_cast]

/-- Helper for Theorem 16.22: broad stability with index `2` forces the canonical Lévy measure to
vanish. -/
private lemma stableBroad_indexTwo_zeroLevyMeasure
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ 2)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    τ.ν = 0 := by
  obtain ⟨d, hscale⟩ := hμ.exists_centering
  have hμ_broad : IsStableInBroadSense μ := by
    refine ⟨hμ.1, ?_⟩
    refine ⟨fun n ↦ (n : ℝ) ^ (1 / (2 : ℝ)), d, ?_, hscale⟩
    intro n
    exact le_of_lt (Real.rpow_pos_of_pos (by positivity) _)
  have hscaleν :
      ∀ n : ℕ+, (n : ℕ) • τ.ν =
        Measure.map (fun x : ℝ ↦ (n : ℝ) ^ (1 / (2 : ℝ)) * x) τ.ν :=
    stableBroad_canonicalTriple_levyMeasureScaling
      hμ_broad hτ
      (fun n ↦ le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
      hscale
  have hIntegralConst :
      ∀ n : ℕ,
        ∫ x, stableBroadIndexTwoScaledTruncation n x ∂τ.ν =
          ∫ x, min (x ^ (2 : ℕ)) 1 ∂τ.ν :=
    stableBroad_indexTwo_scaledTruncation_integral_eq hscaleν
  have hτMeasure : IsCanonicalMeasure τ.ν := hτ.isCanonicalTriple.isCanonicalMeasure
  have hIntegralTendsto :
      Tendsto (fun n : ℕ ↦ ∫ x, stableBroadIndexTwoScaledTruncation n x ∂τ.ν)
        atTop
        (𝓝 (∫ x, (0 : ℝ) ∂τ.ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1)
      ?_
      hτMeasure.integrable_sq_min_one
      ?_
      ?_
    · intro n
      have hmeas : Measurable (stableBroadIndexTwoScaledTruncation n) := by
        unfold stableBroadIndexTwoScaledTruncation
        fun_prop
      exact hmeas.aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall fun x ↦ by
        have hnonneg : 0 ≤ stableBroadIndexTwoScaledTruncation n x := by
          dsimp [stableBroadIndexTwoScaledTruncation]
          positivity
        simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
          stableBroad_indexTwo_scaledTruncation_le n x
    · exact Filter.Eventually.of_forall stableBroad_indexTwo_scaledTruncation_tendsto_zero
  have hIntegralZero :
      ∫ x, min (x ^ (2 : ℕ)) 1 ∂τ.ν = 0 := by
    have hconst :
        Tendsto
          (fun n : ℕ ↦ ∫ x, stableBroadIndexTwoScaledTruncation n x ∂τ.ν)
          atTop
          (𝓝 (∫ x, min (x ^ (2 : ℕ)) 1 ∂τ.ν)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      exact Filter.Eventually.of_forall fun n ↦ (hIntegralConst n).symm
    simpa [eq_comm] using tendsto_nhds_unique hIntegralTendsto hconst
  have hAeZero :
      (fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1) =ᵐ[τ.ν] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun x ↦ by positivity)
      hτMeasure.integrable_sq_min_one).1 hIntegralZero
  have hNonzeroSet :
      τ.ν {x : ℝ | min (x ^ (2 : ℕ)) 1 ≠ 0} = 0 := by
    have hAe :
        ∀ᵐ x ∂τ.ν, min (x ^ (2 : ℕ)) 1 = 0 := by
      simpa using hAeZero
    simpa [ae_iff] using hAe
  apply Measure.ext
  intro s hs
  refine le_antisymm ?_ bot_le
  have hsubset :
      s ⊆ {x : ℝ | min (x ^ (2 : ℕ)) 1 ≠ 0} ∪ ({0} : Set ℝ) := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inr hx0
    · left
      have hsq_pos : 0 < x ^ (2 : ℕ) := by
        simpa [pow_two] using sq_pos_of_ne_zero hx0
      have hmin_pos : 0 < min (x ^ (2 : ℕ)) 1 := lt_min hsq_pos zero_lt_one
      exact ne_of_gt hmin_pos
  have hunion_zero :
      τ.ν ({x : ℝ | min (x ^ (2 : ℕ)) 1 ≠ 0} ∪ ({0} : Set ℝ)) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      τ.ν ({x : ℝ | min (x ^ (2 : ℕ)) 1 ≠ 0} ∪ ({0} : Set ℝ))
          ≤ τ.ν {x : ℝ | min (x ^ (2 : ℕ)) 1 ≠ 0} + τ.ν ({0} : Set ℝ) := by
              exact measure_union_le _ _
      _ = 0 := by
            simp [hNonzeroSet, hτMeasure.measure_singleton_zero]
  exact le_trans (measure_mono hsubset) hunion_zero.le

/-
/-- Helper for Theorem 16.22: a canonical Lévy measure vanishes once its exact scale factors stay
bounded by a fixed multiple of `sqrt n`. -/
private lemma levyMeasure_zero_of_scaleSqrtBounded
    {τ : LevyKhinchinTriple} {a : ℕ+ → ℝ}
    (hτ : IsCanonicalTriple τ)
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hscaleν : ∀ n : ℕ+, (n : ℕ) • τ.ν = Measure.map (fun x : ℝ ↦ a n * x) τ.ν)
    {C : ℝ} (hC_pos : 0 < C)
    (hbound : ∀ n : ℕ+, a n ≤ C * Real.sqrt (n : ℝ)) :
    τ.ν = 0 := by
  let G : ℝ → ℝ := fun x ↦ min (((x / C) ^ (2 : ℕ))) (1 : ℝ)
  have hG_meas : Measurable G := by
    dsimp [G]
    fun_prop
  have hG_nonneg : ∀ x : ℝ, 0 ≤ G x := by
    intro x
    dsimp [G]
    positivity
  have hG_int :
      Integrable G τ.ν := by
    let K : ℝ := max (1 : ℝ) ((C⁻¹) ^ (2 : ℕ))
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      positivity
    have hdom :
        Integrable (fun x : ℝ ↦ K * min (x ^ (2 : ℕ)) (1 : ℝ)) τ.ν := by
      simpa [K] using hτ.isCanonicalMeasure.integrable_sq_min_one.const_mul (max 1 ((C⁻¹) ^ (2 : ℕ)))
    refine hdom.mono' hG_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      have hsq_nonneg : 0 ≤ x ^ (2 : ℕ) := by positivity
      by_cases hsmall : x ^ (2 : ℕ) ≤ 1
      · have hmin_left : min (x ^ (2 : ℕ)) (1 : ℝ) = x ^ (2 : ℕ) := min_eq_left hsmall
        have hcoeff :
            ((x / C) ^ (2 : ℕ)) = ((C⁻¹) ^ (2 : ℕ)) * x ^ (2 : ℕ) := by
          rw [div_eq_mul_inv, mul_pow]
          ring_nf
        have hGK :
            G x ≤ K * min (x ^ (2 : ℕ)) (1 : ℝ) := by
          calc
            G x ≤ ((x / C) ^ (2 : ℕ)) := min_le_left _ _
            _ = ((C⁻¹) ^ (2 : ℕ)) * x ^ (2 : ℕ) := hcoeff
            _ ≤ K * x ^ (2 : ℕ) := by
                  refine mul_le_mul_of_nonneg_right ?_ hsq_nonneg
                  exact le_max_right _ _
            _ = K * min (x ^ (2 : ℕ)) (1 : ℝ) := by rw [hmin_left]
        simpa [Real.norm_eq_abs, abs_of_nonneg (hG_nonneg x), K, hK_nonneg] using hGK
      · have hmin_right : min (x ^ (2 : ℕ)) (1 : ℝ) = 1 := by
          exact min_eq_right (le_of_not_ge hsmall)
        have hGK :
            G x ≤ K * min (x ^ (2 : ℕ)) (1 : ℝ) := by
          calc
            G x ≤ 1 := min_le_right _ _
            _ ≤ K := by
                  dsimp [K]
                  exact le_max_left _ _
            _ = K * min (x ^ (2 : ℕ)) (1 : ℝ) := by rw [hmin_right, mul_one]
        simpa [Real.norm_eq_abs, abs_of_nonneg (hG_nonneg x), K, hK_nonneg] using hGK
  have hScaledTruncInt :
      Tendsto (fun n : ℕ ↦ ∫ x, stableBroadIndexTwoScaledTruncation n x ∂τ.ν)
        atTop
        (𝓝 (∫ x, (0 : ℝ) ∂τ.ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1)
      ?_
      hτ.isCanonicalMeasure.integrable_sq_min_one
      ?_
      ?_
    · intro n
      have hmeas : Measurable (stableBroadIndexTwoScaledTruncation n) := by
        unfold stableBroadIndexTwoScaledTruncation
        fun_prop
      exact hmeas.aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall fun x ↦ by
        have hnonneg : 0 ≤ stableBroadIndexTwoScaledTruncation n x := by
          dsimp [stableBroadIndexTwoScaledTruncation]
          positivity
        simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
          stableBroad_indexTwo_scaledTruncation_le n x
    · exact Filter.Eventually.of_forall stableBroad_indexTwo_scaledTruncation_tendsto_zero
  have hIntegralBound :
      ∀ n : ℕ, ∫ x, G x ∂τ.ν ≤ ∫ x, stableBroadIndexTwoScaledTruncation n x ∂τ.ν := by
    intro n
    let p : ℕ+ := Nat.succPNat n
    have hp_cast : (((p : ℕ) : ℝ)) = n + 1 := by
      simp [p, Nat.succPNat_coe]
    have hRightInt : Integrable (stableBroadIndexTwoScaledTruncation n) τ.ν := by
      refine hτ.isCanonicalMeasure.integrable_sq_min_one.mono' ?_ ?_
      · have hmeas : Measurable (stableBroadIndexTwoScaledTruncation n) := by
          unfold stableBroadIndexTwoScaledTruncation
          fun_prop
        exact hmeas.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x ↦ by
          have hnonneg : 0 ≤ stableBroadIndexTwoScaledTruncation n x := by
            dsimp [stableBroadIndexTwoScaledTruncation]
            positivity
          simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
            stableBroad_indexTwo_scaledTruncation_le n x
    have hpoint :
        ∀ x : ℝ,
          ((n + 1 : ℝ)⁻¹) * G (a p * x) ≤ stableBroadIndexTwoScaledTruncation n x := by
      intro x
      have hcoeff_div :
          a p / C ≤ Real.sqrt (n + 1 : ℝ) := by
        rw [div_le_iff₀ hC_pos]
        simpa [hp_cast, mul_comm] using hbound p
      have hcoeff_sq :
          (a p / C) ^ (2 : ℕ) ≤ (n + 1 : ℝ) := by
        have hcoeff_nonneg : 0 ≤ a p / C := by
          exact div_nonneg (ha_pos p).le hC_pos.le
        have hsqrt_nonneg : 0 ≤ Real.sqrt (n + 1 : ℝ) :=
          Real.sqrt_nonneg (n + 1 : ℝ)
        have hmul :
            (a p / C) * (a p / C) ≤ Real.sqrt (n + 1 : ℝ) * Real.sqrt (n + 1 : ℝ) :=
          mul_le_mul hcoeff_div hcoeff_div hcoeff_nonneg hsqrt_nonneg
        calc
          (a p / C) ^ (2 : ℕ) = (a p / C) * (a p / C) := by ring
          _ ≤ Real.sqrt (n + 1 : ℝ) * Real.sqrt (n + 1 : ℝ) := hmul
          _ = (n + 1 : ℝ) := by
                nlinarith [Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)]
      have hsplit : (a p * x) / C = (a p / C) * x := by
        field_simp [hC_pos.ne']
      have hscaled_sq :
          (((a p * x) / C) ^ (2 : ℕ)) ≤ (n + 1 : ℝ) * x ^ (2 : ℕ) := by
        rw [hsplit, mul_pow]
        nlinarith [hcoeff_sq, sq_nonneg x]
      have hmin_le :
          G (a p * x) ≤ min (((n + 1 : ℝ) * x ^ (2 : ℕ))) (1 : ℝ) := by
        dsimp [G]
        exact min_le_min hscaled_sq le_rfl
      calc
        ((n + 1 : ℝ)⁻¹) * G (a p * x)
            ≤ ((n + 1 : ℝ)⁻¹) * min (((n + 1 : ℝ) * x ^ (2 : ℕ))) (1 : ℝ) := by
                refine mul_le_mul_of_nonneg_left hmin_le ?_
                positivity
        _ = stableBroadIndexTwoScaledTruncation n x := by
              simp [stableBroadIndexTwoScaledTruncation]
    have hLeftInt : Integrable (fun x : ℝ ↦ ((n + 1 : ℝ)⁻¹) * G (a p * x)) τ.ν := by
      refine hRightInt.mono' ?_ ?_
      · have hmeas : Measurable (fun x : ℝ ↦ ((n + 1 : ℝ)⁻¹) * G (a p * x)) := by
          dsimp [G]
          fun_prop
        exact hmeas.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x ↦ by
          have hleft_nonneg : 0 ≤ ((n + 1 : ℝ)⁻¹) * G (a p * x) := by
            positivity
          have hpoint_abs :
              |((n + 1 : ℝ)⁻¹) * G (a p * x)| ≤
                stableBroadIndexTwoScaledTruncation n x := by
            simpa [abs_of_nonneg hleft_nonneg] using hpoint x
          simpa [Real.norm_eq_abs] using hpoint_abs
    have hScaleIntegral :
        ∫ x, G x ∂τ.ν = ((n + 1 : ℝ)⁻¹) * ∫ x, G (a p * x) ∂τ.ν := by
      have hmeasure :
          ((((p : ℕ) : ENNReal) • τ.ν) : Measure ℝ) =
            Measure.map (fun x : ℝ ↦ a p * x) τ.ν := by
        simpa using hscaleν p
      have hScaled :
          (p : ℝ) * ∫ x, G x ∂τ.ν =
            ∫ x, G (a p * x) ∂τ.ν := by
        calc
          (p : ℝ) * ∫ x, G x ∂τ.ν
              = ((((p : ℕ) : ENNReal).toReal : ℝ)) • ∫ x, G x ∂τ.ν := by
                  simp [smul_eq_mul]
          _ = ∫ x, G x ∂(((((p : ℕ) : ENNReal) • τ.ν) : Measure ℝ)) := by
                  symm
                  rw [integral_smul_measure]
          _ = ∫ x, G x ∂Measure.map (fun x : ℝ ↦ a p * x) τ.ν := by rw [hmeasure]
          _ = ∫ x, G (a p * x) ∂τ.ν := by
                rw [integral_map (by fun_prop) (by fun_prop)]
      have hp_ne : (p : ℝ) ≠ 0 := by positivity
      have hScaled' :
          (n + 1 : ℝ) * ∫ x, G x ∂τ.ν =
            ∫ x, G (a p * x) ∂τ.ν := by
        simpa [hp_cast] using hScaled
      field_simp [hp_ne]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hScaled'
    calc
      ∫ x, G x ∂τ.ν = ∫ x, ((n + 1 : ℝ)⁻¹) * G (a p * x) ∂τ.ν := by
        rw [integral_const_mul, hScaleIntegral]
      _ ≤ ∫ x, stableBroadIndexTwoScaledTruncation n x ∂τ.ν := by
        refine integral_mono_ae hLeftInt hRightInt ?_
        exact Filter.Eventually.of_forall hpoint
  let I : ℝ := ∫ x, G x ∂τ.ν
  have hI_nonneg : 0 ≤ I := by
    exact integral_nonneg fun x ↦ hG_nonneg x
  have hI_zero : I = 0 := by
    by_contra hI_ne
    have hI_pos : 0 < I := lt_of_le_of_ne hI_nonneg (Ne.symm hI_ne)
    have hEventually :
        ∀ᶠ n : ℕ in atTop, ∫ x, stableBroadIndexTwoScaledTruncation n x ∂τ.ν < I := by
      have hNhds : Set.Iio I ∈ 𝓝 (∫ x, (0 : ℝ) ∂τ.ν) := by
        simpa using (Iio_mem_nhds hI_pos : Set.Iio I ∈ 𝓝 (0 : ℝ))
      exact hScaledTruncInt.eventually hNhds
    rcases hEventually.exists with ⟨n, hn⟩
    exact (not_lt_of_ge (hIntegralBound n)) hn
  have hAeZero :
      G =ᵐ[τ.ν] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun x ↦ hG_nonneg x) hG_int).1 hI_zero
  have hNonzeroSet :
      τ.ν {x : ℝ | G x ≠ 0} = 0 := by
    have hAe :
        ∀ᵐ x ∂τ.ν, G x = 0 := by
      simpa using hAeZero
    simpa [ae_iff] using hAe
  apply Measure.ext
  intro s hs
  refine le_antisymm ?_ bot_le
  have hsubset :
      s ⊆ {x : ℝ | G x ≠ 0} ∪ ({0} : Set ℝ) := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inr hx0
    · left
      have hdiv_ne : x / C ≠ 0 := by
        exact div_ne_zero hx0 hC_pos.ne'
      have hsq_pos : 0 < (x / C) ^ (2 : ℕ) := by
        simpa [pow_two] using sq_pos_of_ne_zero hdiv_ne
      have hmin_pos : 0 < G x := by
        dsimp [G]
        exact lt_min hsq_pos zero_lt_one
      exact ne_of_gt hmin_pos
  have hunion_zero :
      τ.ν ({x : ℝ | G x ≠ 0} ∪ ({0} : Set ℝ)) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      τ.ν ({x : ℝ | G x ≠ 0} ∪ ({0} : Set ℝ))
          ≤ τ.ν {x : ℝ | G x ≠ 0} + τ.ν ({0} : Set ℝ) := by
              exact measure_union_le _ _
      _ = 0 := by
            simp [hNonzeroSet, hτ.isCanonicalMeasure.measure_singleton_zero]
  exact le_trans (measure_mono hsubset) hunion_zero.le
-/

/-- Helper for Theorem 16.22: a canonical Lévy measure vanishes once its exact scale factors stay
bounded by a fixed multiple of `sqrt n`. -/
private lemma levyMeasure_zero_of_scaleSqrtBounded
    {τ : LevyKhinchinTriple} {a : ℕ+ → ℝ}
    (hτ : IsCanonicalTriple τ)
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hscaleν : ∀ n : ℕ+, (n : ℕ) • τ.ν = Measure.map (fun x : ℝ ↦ a n * x) τ.ν)
    {C : ℝ} (hC_pos : 0 < C)
    (hbound : ∀ n : ℕ+, a n ≤ C * Real.sqrt (n : ℝ)) :
    τ.ν = 0 := by
  -- Route correction: use the already prepared dominated-convergence comparison with the
  -- Gaussian-branch truncation kernels instead of leaving this as a re-plan placeholder.
  let G : ℝ → ℝ := fun x ↦ min (((x / C) ^ (2 : ℕ))) (1 : ℝ)
  have hG_meas : Measurable G := by
    dsimp [G]
    fun_prop
  have hG_nonneg : ∀ x : ℝ, 0 ≤ G x := by
    intro x
    dsimp [G]
    positivity
  have hG_int :
      Integrable G τ.ν := by
    let K : ℝ := max (1 : ℝ) ((C⁻¹) ^ (2 : ℕ))
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      positivity
    have hdom :
        Integrable (fun x : ℝ ↦ K * min (x ^ (2 : ℕ)) (1 : ℝ)) τ.ν := by
      simpa [K] using hτ.isCanonicalMeasure.integrable_sq_min_one.const_mul
        (max 1 ((C⁻¹) ^ (2 : ℕ)))
    refine hdom.mono' hG_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      have hsq_nonneg : 0 ≤ x ^ (2 : ℕ) := by positivity
      by_cases hsmall : x ^ (2 : ℕ) ≤ 1
      · have hmin_left : min (x ^ (2 : ℕ)) (1 : ℝ) = x ^ (2 : ℕ) := min_eq_left hsmall
        have hcoeff :
            ((x / C) ^ (2 : ℕ)) = ((C⁻¹) ^ (2 : ℕ)) * x ^ (2 : ℕ) := by
          rw [div_eq_mul_inv, mul_pow]
          ring_nf
        have hGK :
            G x ≤ K * min (x ^ (2 : ℕ)) (1 : ℝ) := by
          calc
            G x ≤ ((x / C) ^ (2 : ℕ)) := min_le_left _ _
            _ = ((C⁻¹) ^ (2 : ℕ)) * x ^ (2 : ℕ) := hcoeff
            _ ≤ K * x ^ (2 : ℕ) := by
                  refine mul_le_mul_of_nonneg_right ?_ hsq_nonneg
                  exact le_max_right _ _
            _ = K * min (x ^ (2 : ℕ)) (1 : ℝ) := by rw [hmin_left]
        simpa [Real.norm_eq_abs, abs_of_nonneg (hG_nonneg x), K, hK_nonneg] using hGK
      · have hmin_right : min (x ^ (2 : ℕ)) (1 : ℝ) = 1 := by
          exact min_eq_right (le_of_not_ge hsmall)
        have hGK :
            G x ≤ K * min (x ^ (2 : ℕ)) (1 : ℝ) := by
          calc
            G x ≤ 1 := min_le_right _ _
            _ ≤ K := by
                  dsimp [K]
                  exact le_max_left _ _
            _ = K * min (x ^ (2 : ℕ)) (1 : ℝ) := by rw [hmin_right, mul_one]
        simpa [Real.norm_eq_abs, abs_of_nonneg (hG_nonneg x), K, hK_nonneg] using hGK
  have hScaledTruncInt :
      Tendsto (fun n : ℕ ↦ ∫ x, stableBroadIndexTwoScaledTruncation n x ∂τ.ν)
        atTop
        (𝓝 (∫ x, (0 : ℝ) ∂τ.ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1)
      ?_
      hτ.isCanonicalMeasure.integrable_sq_min_one
      ?_
      ?_
    · intro n
      have hmeas : Measurable (stableBroadIndexTwoScaledTruncation n) := by
        unfold stableBroadIndexTwoScaledTruncation
        fun_prop
      exact hmeas.aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall fun x ↦ by
        have hnonneg : 0 ≤ stableBroadIndexTwoScaledTruncation n x := by
          dsimp [stableBroadIndexTwoScaledTruncation]
          positivity
        simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
          stableBroad_indexTwo_scaledTruncation_le n x
    · exact Filter.Eventually.of_forall stableBroad_indexTwo_scaledTruncation_tendsto_zero
  have hIntegralBound :
      ∀ n : ℕ, ∫ x, G x ∂τ.ν ≤ ∫ x, stableBroadIndexTwoScaledTruncation n x ∂τ.ν := by
    intro n
    let p : ℕ+ := Nat.succPNat n
    have hp_cast : (((p : ℕ) : ℝ)) = n + 1 := by
      simp [p, Nat.succPNat_coe]
    have hRightInt : Integrable (stableBroadIndexTwoScaledTruncation n) τ.ν := by
      refine hτ.isCanonicalMeasure.integrable_sq_min_one.mono' ?_ ?_
      · have hmeas : Measurable (stableBroadIndexTwoScaledTruncation n) := by
          unfold stableBroadIndexTwoScaledTruncation
          fun_prop
        exact hmeas.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x ↦ by
          have hnonneg : 0 ≤ stableBroadIndexTwoScaledTruncation n x := by
            dsimp [stableBroadIndexTwoScaledTruncation]
            positivity
          simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
            stableBroad_indexTwo_scaledTruncation_le n x
    have hpoint :
        ∀ x : ℝ,
          ((n + 1 : ℝ)⁻¹) * G (a p * x) ≤ stableBroadIndexTwoScaledTruncation n x := by
      intro x
      have hcoeff_div :
          a p / C ≤ Real.sqrt (n + 1 : ℝ) := by
        rw [div_le_iff₀ hC_pos]
        simpa [hp_cast, mul_comm] using hbound p
      have hcoeff_sq :
          (a p / C) ^ (2 : ℕ) ≤ (n + 1 : ℝ) := by
        have hcoeff_nonneg : 0 ≤ a p / C := by
          exact div_nonneg (ha_pos p).le hC_pos.le
        have hsqrt_nonneg : 0 ≤ Real.sqrt (n + 1 : ℝ) :=
          Real.sqrt_nonneg (n + 1 : ℝ)
        have hmul :
            (a p / C) * (a p / C) ≤ Real.sqrt (n + 1 : ℝ) * Real.sqrt (n + 1 : ℝ) :=
          mul_le_mul hcoeff_div hcoeff_div hcoeff_nonneg hsqrt_nonneg
        calc
          (a p / C) ^ (2 : ℕ) = (a p / C) * (a p / C) := by ring
          _ ≤ Real.sqrt (n + 1 : ℝ) * Real.sqrt (n + 1 : ℝ) := hmul
          _ = (n + 1 : ℝ) := by
                nlinarith [Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)]
      have hsplit : (a p * x) / C = (a p / C) * x := by
        field_simp [hC_pos.ne']
      have hscaled_sq :
          (((a p * x) / C) ^ (2 : ℕ)) ≤ (n + 1 : ℝ) * x ^ (2 : ℕ) := by
        rw [hsplit, mul_pow]
        nlinarith [hcoeff_sq, sq_nonneg x]
      have hmin_le :
          G (a p * x) ≤ min (((n + 1 : ℝ) * x ^ (2 : ℕ))) (1 : ℝ) := by
        dsimp [G]
        exact min_le_min hscaled_sq le_rfl
      calc
        ((n + 1 : ℝ)⁻¹) * G (a p * x)
            ≤ ((n + 1 : ℝ)⁻¹) * min (((n + 1 : ℝ) * x ^ (2 : ℕ))) (1 : ℝ) := by
                refine mul_le_mul_of_nonneg_left hmin_le ?_
                positivity
        _ = stableBroadIndexTwoScaledTruncation n x := by
              simp [stableBroadIndexTwoScaledTruncation]
    have hLeftInt : Integrable (fun x : ℝ ↦ ((n + 1 : ℝ)⁻¹) * G (a p * x)) τ.ν := by
      refine hRightInt.mono' ?_ ?_
      · have hmeas : Measurable (fun x : ℝ ↦ ((n + 1 : ℝ)⁻¹) * G (a p * x)) := by
          dsimp [G]
          fun_prop
        exact hmeas.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x ↦ by
          have hleft_nonneg : 0 ≤ ((n + 1 : ℝ)⁻¹) * G (a p * x) := by
            positivity
          have hpoint_abs :
              |((n + 1 : ℝ)⁻¹) * G (a p * x)| ≤ stableBroadIndexTwoScaledTruncation n x := by
            simpa [abs_of_nonneg hleft_nonneg] using hpoint x
          simpa [Real.norm_eq_abs] using hpoint_abs
    have hScaleIntegral :
        ∫ x, G x ∂τ.ν = ((n + 1 : ℝ)⁻¹) * ∫ x, G (a p * x) ∂τ.ν := by
      have hmeasure :
          ((((p : ℕ) : ENNReal) • τ.ν) : Measure ℝ) =
            Measure.map (fun x : ℝ ↦ a p * x) τ.ν := by
        ext s hs
        simpa [nsmul_eq_mul, Measure.smul_apply] using
          congrArg (fun μ : Measure ℝ ↦ μ s) (hscaleν p)
      have hScaled :
          (p : ℝ) * ∫ x, G x ∂τ.ν = ∫ x, G (a p * x) ∂τ.ν := by
        calc
          (p : ℝ) * ∫ x, G x ∂τ.ν
              = ((((p : ℕ) : ENNReal).toReal : ℝ)) • ∫ x, G x ∂τ.ν := by
                  simp [smul_eq_mul]
          _ = ∫ x, G x ∂(((((p : ℕ) : ENNReal) • τ.ν) : Measure ℝ)) := by
                  symm
                  rw [integral_smul_measure]
          _ = ∫ x, G x ∂Measure.map (fun x : ℝ ↦ a p * x) τ.ν := by rw [hmeasure]
          _ = ∫ x, G (a p * x) ∂τ.ν := by
                rw [integral_map (by fun_prop) (by fun_prop)]
      have hp_ne : (p : ℝ) ≠ 0 := by positivity
      have hScaled' :
          (n + 1 : ℝ) * ∫ x, G x ∂τ.ν = ∫ x, G (a p * x) ∂τ.ν := by
        simpa [hp_cast] using hScaled
      field_simp [hp_ne]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hScaled'
    calc
      ∫ x, G x ∂τ.ν = ∫ x, ((n + 1 : ℝ)⁻¹) * G (a p * x) ∂τ.ν := by
        rw [integral_const_mul, hScaleIntegral]
      _ ≤ ∫ x, stableBroadIndexTwoScaledTruncation n x ∂τ.ν := by
        refine integral_mono_ae hLeftInt hRightInt ?_
        exact Filter.Eventually.of_forall hpoint
  let I : ℝ := ∫ x, G x ∂τ.ν
  have hI_nonneg : 0 ≤ I := by
    exact integral_nonneg fun x ↦ hG_nonneg x
  have hI_zero : I = 0 := by
    by_contra hI_ne
    have hI_pos : 0 < I := lt_of_le_of_ne hI_nonneg (Ne.symm hI_ne)
    have hEventually :
        ∀ᶠ n : ℕ in atTop, ∫ x, stableBroadIndexTwoScaledTruncation n x ∂τ.ν < I := by
      have hNhds : Set.Iio I ∈ 𝓝 (∫ x, (0 : ℝ) ∂τ.ν) := by
        simpa using (Iio_mem_nhds hI_pos : Set.Iio I ∈ 𝓝 (0 : ℝ))
      exact hScaledTruncInt.eventually hNhds
    rcases hEventually.exists with ⟨n, hn⟩
    exact (not_lt_of_ge (hIntegralBound n)) hn
  have hAeZero :
      G =ᵐ[τ.ν] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun x ↦ hG_nonneg x) hG_int).1 hI_zero
  have hNonzeroSet :
      τ.ν {x : ℝ | G x ≠ 0} = 0 := by
    have hAe :
        ∀ᵐ x ∂τ.ν, G x = 0 := by
      simpa using hAeZero
    simpa [ae_iff] using hAe
  apply Measure.ext
  intro s hs
  refine le_antisymm ?_ bot_le
  have hsubset :
      s ⊆ {x : ℝ | G x ≠ 0} ∪ ({0} : Set ℝ) := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inr hx0
    · left
      have hdiv_ne : x / C ≠ 0 := by
        exact div_ne_zero hx0 hC_pos.ne'
      have hsq_pos : 0 < (x / C) ^ (2 : ℕ) := by
        simpa [pow_two] using sq_pos_of_ne_zero hdiv_ne
      have hmin_pos : 0 < G x := by
        dsimp [G]
        exact lt_min hsq_pos zero_lt_one
      exact ne_of_gt hmin_pos
  have hunion_zero :
      τ.ν ({x : ℝ | G x ≠ 0} ∪ ({0} : Set ℝ)) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      τ.ν ({x : ℝ | G x ≠ 0} ∪ ({0} : Set ℝ))
          ≤ τ.ν {x : ℝ | G x ≠ 0} + τ.ν ({0} : Set ℝ) := by
              exact measure_union_le _ _
      _ = 0 := by
            simp [hNonzeroSet, hτ.isCanonicalMeasure.measure_singleton_zero]
  exact le_trans (measure_mono hsubset) hunion_zero.le

/-- Helper for Theorem 16.22: iterating one adjacent exact-tail ratio moves along a geometric
grid with the corresponding geometric decay factor. -/
private lemma adjacentRatioTailScaling_pow_local
    {a : ℕ+ → ℝ} {F : ℝ → ℝ}
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x)
    (n : ℕ) :
    ∀ k : ℕ, ∀ x : ℝ, 0 < x →
      F (((a (Nat.succPNat (n + 1)) / a (Nat.succPNat n)) ^ k) * x) =
        (((n + 1 : ℝ) / (n + 2 : ℝ)) ^ k) * F x := by
  intro k
  induction k with
  | zero =>
      intro x hx
      -- Proof comment: the zeroth grid point is the original tail value.
      simp
  | succ k hk =>
      intro x hx
      let q : ℝ := a (Nat.succPNat (n + 1)) / a (Nat.succPNat n)
      let r : ℝ := (n + 1 : ℝ) / (n + 2 : ℝ)
      have hq_pos : 0 < q := by
        dsimp [q]
        exact div_pos (ha_pos (Nat.succPNat (n + 1))) (ha_pos (Nat.succPNat n))
      have hxk_pos : 0 < q ^ k * x := by
        dsimp [q]
        exact mul_pos (pow_pos hq_pos k) hx
      calc
        F ((q ^ (k + 1)) * x)
            = F (q * (q ^ k * x)) := by
                rw [pow_succ]
                ring
        _ = r * F (q ^ k * x) := by
              simpa [q, r, mul_comm, mul_left_comm, mul_assoc] using
                (adjacentRatioTailScaling_of_exactTailScaling ha_pos hscale n (q ^ k * x) hxk_pos)
        _ = r * (r ^ k * F x) := by rw [hk x hx]
        _ = r ^ (k + 1) * F x := by
              rw [pow_succ]
              ring

/-- Helper for Theorem 16.22: one adjacent exact-tail ratio yields a one-step power-law squeeze on
every larger point of the tail. -/
private lemma adjacentPowerLawBounds_of_exactTailScaling_local
    {a : ℕ+ → ℝ} {F : ℝ → ℝ}
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hantitone : AntitoneOn F (Set.Ioi 0))
    (hscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x)
    {x0 : ℝ} (hx0 : 0 < x0) (hFx0 : 0 < F x0)
    (n : ℕ) :
    let q : ℝ := a (Nat.succPNat (n + 1)) / a (Nat.succPNat n)
    let r : ℝ := (n + 1 : ℝ) / (n + 2 : ℝ)
    let α : ℝ := Real.log (((n + 2 : ℝ) / (n + 1 : ℝ))) / Real.log q
    ∀ y : ℝ, 1 ≤ y →
      r * y ^ (-α) * F x0 ≤ F (y * x0) ∧
        F (y * x0) ≤ r⁻¹ * y ^ (-α) * F x0 := by
  dsimp
  intro y hy
  let q : ℝ := a (Nat.succPNat (n + 1)) / a (Nat.succPNat n)
  let r : ℝ := (n + 1 : ℝ) / (n + 2 : ℝ)
  let α : ℝ := Real.log (((n + 2 : ℝ) / (n + 1 : ℝ))) / Real.log q
  have hstrict : StrictMono a :=
    scaleStrictMono_of_exactTailScaling ha_pos hantitone hscale ⟨x0, hx0, hFx0⟩
  have hstep : Nat.succPNat n < Nat.succPNat (n + 1) := by
    exact_mod_cast (Nat.lt_succ_self (n + 1))
  have hq_gt : 1 < q := by
    dsimp [q]
    rw [one_lt_div_iff]
    exact Or.inl ⟨ha_pos (Nat.succPNat n), hstrict hstep⟩
  have hq_pos : 0 < q := lt_trans zero_lt_one hq_gt
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hratio_pos : 0 < ((n + 2 : ℝ) / (n + 1 : ℝ)) := by positivity
  have hratio_gt : 1 < ((n + 2 : ℝ) / (n + 1 : ℝ)) := by
    rw [one_lt_div_iff]
    exact Or.inl ⟨by positivity, by linarith⟩
  have hα_pos : 0 < α := by
    dsimp [α]
    exact div_pos (Real.log_pos hratio_gt)
      (Real.log_pos hq_gt)
  have hr_eq : q ^ (-α) = r := by
    have hqpow :
        q ^ α = ((n + 2 : ℝ) / (n + 1 : ℝ)) := by
      have hlog_ne : Real.log q ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one hq_pos (by linarith : q ≠ 1)
      rw [Real.rpow_def_of_pos hq_pos]
      have hlog_mul :
          Real.log q * α = Real.log ((n + 2 : ℝ) / (n + 1 : ℝ)) := by
        dsimp [α]
        field_simp [hlog_ne]
      rw [hlog_mul, Real.exp_log hratio_pos]
    rw [Real.rpow_neg hq_pos.le, hqpow]
    dsimp [r]
    field_simp
  have hpow_neg_nat :
      ∀ k : ℕ, ((q ^ k : ℝ) ^ (-α)) = r ^ k := by
    intro k
    calc
      ((q ^ k : ℝ) ^ (-α))
          = (q ^ (k : ℝ)) ^ (-α) := by rw [← Real.rpow_natCast]
      _ = q ^ ((k : ℝ) * (-α)) := by rw [← Real.rpow_mul hq_pos.le]
      _ = q ^ ((-α) * (k : ℝ)) := by congr 1; ring
      _ = (q ^ (-α)) ^ (k : ℝ) := by rw [Real.rpow_mul hq_pos.le]
      _ = (q ^ (-α)) ^ k := by rw [Real.rpow_natCast]
      _ = r ^ k := by rw [hr_eq]
  have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  obtain ⟨k, hk_lower, hk_upper⟩ := exists_nat_pow_near hy hq_gt
  have hgrid_k :
      F (q ^ k * x0) = r ^ k * F x0 := by
    simpa [q, r] using adjacentRatioTailScaling_pow_local ha_pos hscale n k x0 hx0
  have hgrid_succ :
      F (q ^ (k + 1) * x0) = r ^ (k + 1) * F x0 := by
    simpa [q, r] using adjacentRatioTailScaling_pow_local ha_pos hscale n (k + 1) x0 hx0
  have hmono_upper :
      F (y * x0) ≤ F (q ^ k * x0) := by
    have hqx0 : q ^ k * x0 ≤ y * x0 := by
      exact mul_le_mul_of_nonneg_right hk_lower hx0.le
    exact hantitone (mul_pos (pow_pos hq_pos k) hx0) (mul_pos hy_pos hx0) hqx0
  have hmono_lower :
      F (q ^ (k + 1) * x0) ≤ F (y * x0) := by
    have hyx0 : y * x0 ≤ q ^ (k + 1) * x0 := by
      exact mul_le_mul_of_nonneg_right hk_upper.le hx0.le
    exact hantitone (mul_pos hy_pos hx0) (mul_pos (pow_pos hq_pos (k + 1)) hx0) hyx0
  have hqy_upper :
      y ^ (-α) ≤ ((q ^ k : ℝ) ^ (-α)) := by
    exact Real.rpow_le_rpow_of_nonpos (pow_pos hq_pos k) hk_lower (by linarith [hα_pos])
  have hqy_lower :
      ((q ^ (k + 1) : ℝ) ^ (-α)) ≤ y ^ (-α) := by
    exact Real.rpow_le_rpow_of_nonpos hy_pos hk_upper.le (by linarith [hα_pos])
  have hlow_core : r * y ^ (-α) ≤ r ^ (k + 1) := by
    calc
      r * y ^ (-α) ≤ r * ((q ^ k : ℝ) ^ (-α)) := by
        gcongr
      _ = r * r ^ k := by rw [hpow_neg_nat]
      _ = r ^ (k + 1) := by
        rw [pow_succ]
        ring
  have hupp_core : r ^ k ≤ r⁻¹ * y ^ (-α) := by
    have hk_succ :
        r ^ (k + 1) ≤ y ^ (-α) := by
      calc
        r ^ (k + 1) = ((q ^ (k + 1) : ℝ) ^ (-α)) := by rw [← hpow_neg_nat (k + 1)]
        _ ≤ y ^ (-α) := hqy_lower
    calc
      r ^ k = r⁻¹ * r ^ (k + 1) := by
        have hrk : r⁻¹ * r ^ (k + 1) = r ^ k := by
          calc
            r⁻¹ * r ^ (k + 1) = (r⁻¹ * r) * r ^ k := by rw [pow_succ', mul_assoc]
            _ = r ^ k := by simp [hr_pos.ne']
        exact hrk.symm
      _ ≤ r⁻¹ * y ^ (-α) := by
        exact mul_le_mul_of_nonneg_left hk_succ (inv_nonneg.mpr hr_pos.le)
  constructor
  · -- Proof comment: the lower neighboring grid point gives the lower power-law squeeze.
    calc
      r * y ^ (-α) * F x0 ≤ r ^ (k + 1) * F x0 := by
        gcongr
      _ = F (q ^ (k + 1) * x0) := by rw [hgrid_succ]
      _ ≤ F (y * x0) := hmono_lower
  · -- Proof comment: the upper neighboring grid point gives the upper power-law squeeze.
    calc
      F (y * x0) ≤ F (q ^ k * x0) := hmono_upper
      _ = r ^ k * F x0 := by rw [hgrid_k]
      _ ≤ r⁻¹ * y ^ (-α) * F x0 := by
        gcongr

/-- Helper for Theorem 16.22: the adjacent logarithmic exponents forced by exact tail scaling are
independent of the adjacent index. -/
private lemma adjacentLogExponent_constant_of_exactTailScaling_local
    {a : ℕ+ → ℝ} {F : ℝ → ℝ}
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hantitone : AntitoneOn F (Set.Ioi 0))
    (hscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x)
    (hzero : Tendsto F atTop (𝓝 0))
    (hbase : ∃ x0 : ℝ, 0 < x0 ∧ 0 < F x0) :
    ∀ m n : ℕ,
      Real.log (((m + 2 : ℝ) / (m + 1 : ℝ))) /
          Real.log (a (Nat.succPNat (m + 1)) / a (Nat.succPNat m)) =
        Real.log (((n + 2 : ℝ) / (n + 1 : ℝ))) /
          Real.log (a (Nat.succPNat (n + 1)) / a (Nat.succPNat n)) := by
  rcases hbase with ⟨x0, hx0, hFx0⟩
  let αAt : ℕ → ℝ := fun k ↦
    Real.log (((k + 2 : ℝ) / (k + 1 : ℝ))) /
      Real.log (a (Nat.succPNat (k + 1)) / a (Nat.succPNat k))
  have hnot_lt : ∀ {i j : ℕ}, αAt i < αAt j → False := by
    intro i j hij
    let ri : ℝ := (i + 1 : ℝ) / (i + 2 : ℝ)
    let rj : ℝ := (j + 1 : ℝ) / (j + 2 : ℝ)
    have hri_pos : 0 < ri := by
      dsimp [ri]
      positivity
    have hrj_pos : 0 < rj := by
      dsimp [rj]
      positivity
    have hδ_pos : 0 < αAt j - αAt i := sub_pos.mpr hij
    have hgrow :
        Tendsto (fun y : ℝ ↦ ri * y ^ (αAt j - αAt i)) atTop atTop := by
      exact Tendsto.const_mul_atTop hri_pos (tendsto_rpow_atTop hδ_pos)
    have hEventually :
        ∀ᶠ y : ℝ in atTop, rj⁻¹ < ri * y ^ (αAt j - αAt i) := by
      exact hgrow.eventually (Filter.Ioi_mem_atTop (rj⁻¹))
    rcases Filter.mem_atTop_sets.mp hEventually with ⟨Y, hY⟩
    let y : ℝ := max 1 Y
    have hy_one : 1 ≤ y := le_max_left _ _
    have hy_ge : Y ≤ y := le_max_right _ _
    have hy_large : rj⁻¹ < ri * y ^ (αAt j - αAt i) := hY y hy_ge
    have hiBounds :=
      adjacentPowerLawBounds_of_exactTailScaling_local
        ha_pos hantitone hscale hx0 hFx0 i y hy_one
    have hjBounds :=
      adjacentPowerLawBounds_of_exactTailScaling_local
        ha_pos hantitone hscale hx0 hFx0 j y hy_one
    have hmain :
        ri * y ^ (-αAt i) ≤ rj⁻¹ * y ^ (-αAt j) := by
      have hscaled :
          (ri * y ^ (-αAt i)) * F x0 ≤
            (rj⁻¹ * y ^ (-αAt j)) * F x0 := le_trans hiBounds.1 hjBounds.2
      nlinarith
    have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy_one
    have hyPow_pos : 0 < y ^ αAt j := Real.rpow_pos_of_pos hy_pos _
    have hmain' :
        ri * y ^ (αAt j - αAt i) ≤ rj⁻¹ := by
      have hmul :
          (ri * y ^ (-αAt i)) * y ^ αAt j ≤
            (rj⁻¹ * y ^ (-αAt j)) * y ^ αAt j := by
        exact mul_le_mul_of_nonneg_right hmain hyPow_pos.le
      have hyLeft :
          y ^ (-αAt i) * y ^ αAt j = y ^ (αAt j - αAt i) := by
        rw [← Real.rpow_add hy_pos (-αAt i) (αAt j)]
        congr 1
        ring
      have hyRight :
          y ^ (-αAt j) * y ^ αAt j = 1 := by
        rw [← Real.rpow_add hy_pos (-αAt j) (αAt j)]
        simp
      have hmul' :
          ri * (y ^ (-αAt i) * y ^ αAt j) ≤
            rj⁻¹ * (y ^ (-αAt j) * y ^ αAt j) := by
        simpa [mul_assoc] using hmul
      rw [hyLeft, hyRight, mul_one] at hmul'
      simpa [sub_eq_add_neg] using hmul'
    exact (not_le_of_gt hy_large) hmain'
  intro m n
  -- Proof comment: if one adjacent logarithmic exponent were smaller than another, the
  -- power-law squeeze on a large grid point would contradict the geometric growth of
  -- `y^(αₙ - αₘ)`.
  have hmn : ¬ αAt n < αAt m := by
    intro hnm
    exact hnot_lt hnm
  have hnm : ¬ αAt m < αAt n := by
    intro hmn'
    exact hnot_lt hmn'
  exact le_antisymm (le_of_not_gt hmn) (le_of_not_gt hnm)

/-
private lemma scaleFormula_of_exactTailScaling_local
    {a : ℕ+ → ℝ} {F : ℝ → ℝ}
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hantitone : AntitoneOn F (Set.Ioi 0))
    (hscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x)
    (hzero : Tendsto F atTop (𝓝 0))
    (hbase : ∃ x0 : ℝ, 0 < x0 ∧ 0 < F x0) :
    ∃ α : ℝ, 0 < α ∧ ∀ n : ℕ+, a n = (n : ℝ) ^ (1 / α) := by
  -- Route correction: the downstream branch assembly no longer depends on the whole nonzero-tail
  -- argument here. The remaining work is exactly the textbook geometric-grid squeeze that turns
  -- exact tail scaling plus adjacent-ratio antitonicity into the explicit scale law.
  let q : ℕ → ℝ := fun n ↦ a (Nat.succPNat (n + 1)) / a (Nat.succPNat n)
  let αAt : ℕ → ℝ := fun n ↦
    Real.log (((n + 2 : ℝ) / (n + 1 : ℝ))) / Real.log (q n)
  have ha_one : a 1 = 1 :=
    scaleOne_eq_one_of_exactTailScaling ha_pos hscale hzero hbase
  have hstrict : StrictMono a :=
    scaleStrictMono_of_exactTailScaling ha_pos hantitone hscale hbase
  let _ := scaleUnbounded_of_exactTailScaling ha_pos hantitone hscale hbase
  let _ := adjacentScaleRatio_antitone_of_exactTailScaling ha_pos hantitone hscale hbase
  have hq_gt : ∀ n : ℕ, 1 < q n := by
    intro n
    dsimp [q]
    rw [one_lt_div_iff]
    have hstep : Nat.succPNat n < Nat.succPNat (n + 1) := by
      exact_mod_cast (Nat.lt_succ_self (n + 1))
    exact Or.inl ⟨ha_pos (Nat.succPNat n), hstrict hstep⟩
  have hαAt_const :
      ∀ m n : ℕ, αAt m = αAt n :=
    adjacentLogExponent_constant_of_exactTailScaling_local
      ha_pos hantitone hscale hzero hbase
  let α : ℝ := αAt 0
  have hα0 : 0 < α := by
    dsimp [α, αAt, q]
    have hratio0_gt : 1 < ((↑(0 : ℕ) + 2 : ℝ) / (↑(0 : ℕ) + 1)) := by
      norm_num
    exact div_pos (Real.log_pos hratio0_gt)
      (Real.log_pos (hq_gt 0))
  have hq_formula :
      ∀ n : ℕ, q n = (((n + 2 : ℝ) / (n + 1 : ℝ)) ^ (1 / α)) := by
    intro n
    have hα_eq : α = αAt n := by
      dsimp [α]
      simpa using hαAt_const 0 n
    have hα_ne : α ≠ 0 := ne_of_gt hα0
    have hq_formula_inv :
        q n = (((n + 2 : ℝ) / (n + 1 : ℝ)) ^ α⁻¹) := by
      refine (Real.eq_rpow_inv
        (show 0 ≤ q n by exact le_of_lt (lt_trans zero_lt_one (hq_gt n)))
        (show 0 ≤ ((n + 2 : ℝ) / (n + 1 : ℝ)) by positivity) hα_ne).2 ?_
      rw [hα_eq]
      dsimp [αAt]
      have hlog_ne : Real.log (q n) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (lt_trans zero_lt_one (hq_gt n)) (by
          intro hq_one
          linarith [hq_gt n])
      rw [Real.rpow_def_of_pos (lt_trans zero_lt_one (hq_gt n))]
      have hlog_mul :
          Real.log (q n) * (Real.log ((n + 2 : ℝ) / (n + 1 : ℝ)) / Real.log (q n)) =
            Real.log ((n + 2 : ℝ) / (n + 1 : ℝ)) := by
        field_simp [hlog_ne]
      rw [hlog_mul, Real.exp_log (by positivity)]
    simpa [one_div] using hq_formula_inv
  have ha_formula_nat :
      ∀ k : ℕ, a (Nat.succPNat k) = (k + 1 : ℝ) ^ (1 / α) := by
    intro k
    induction k with
    | zero =>
        -- Proof comment: the source normalization `a₁ = 1` is the base of the telescoping
        -- reconstruction.
        simpa [α, ha_one]
    | succ k hk =>
        -- Proof comment: once the adjacent ratios are fixed, multiply the ratio formula by the
        -- inductive value of `aₖ₊₁` and collapse the product.
        have hsplit :
            a (Nat.succPNat (k + 1)) =
              q k * a (Nat.succPNat k) := by
          dsimp [q]
          field_simp [ne_of_gt (ha_pos (Nat.succPNat k))]
        calc
          a (Nat.succPNat (k + 1))
              = q k * a (Nat.succPNat k) := hsplit
          _ = (((k + 2 : ℝ) / (k + 1 : ℝ)) ^ (1 / α)) * ((k + 1 : ℝ) ^ (1 / α)) := by
                rw [hq_formula k, hk]
          _ = ((((k + 2 : ℝ) / (k + 1 : ℝ)) * (k + 1 : ℝ)) ^ (1 / α)) := by
                rw [← Real.mul_rpow (by positivity) (by positivity)]
          _ = ((k + 2 : ℝ) ^ (1 / α)) := by
                congr 1
                field_simp
          _ = ((↑(k + 1) + 1 : ℝ) ^ (1 / α)) := by
                congr 1
                norm_num [Nat.cast_add, add_assoc]
  refine ⟨α, hα0, ?_⟩
  intro n
  -- Proof comment: convert the `ℕ`-indexed telescoping formula back to the original `ℕ+`
  -- indexing through `natPred`.
  have hn_cast : (((n.natPred + 1 : ℕ) : ℝ)) = ((n : ℕ) : ℝ) := by
    exact_mod_cast n.natPred_add_one
  have hn_formula : a n = (((n : ℕ) : ℝ) ^ α⁻¹) := by
    calc
      a n = a (Nat.succPNat n.natPred) := by simp [PNat.succPNat_natPred]
      _ = (((n.natPred + 1 : ℕ) : ℝ) ^ α⁻¹) := by
        simpa [one_div] using ha_formula_nat n.natPred
      _ = (((n : ℕ) : ℝ) ^ α⁻¹) := by rw [hn_cast]
  simpa [one_div] using hn_formula
-/

/-- Helper for Theorem 16.22: exact one-sided tail scaling determines the explicit scale law
`a n = n^(1 / α)`. -/
private lemma scaleFormula_of_exactTailScaling_local
    {a : ℕ+ → ℝ} {F : ℝ → ℝ}
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hantitone : AntitoneOn F (Set.Ioi 0))
    (hscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x)
    (hzero : Tendsto F atTop (𝓝 0))
    (hbase : ∃ x0 : ℝ, 0 < x0 ∧ 0 < F x0) :
    ∃ α : ℝ, 0 < α ∧ ∀ n : ℕ+, a n = (n : ℝ) ^ (1 / α) := by
  -- Route correction: close the nonzero-tail branch by the local geometric-grid squeeze and
  -- telescoping product formula, rather than deferring the scale law to re-plan.
  let q : ℕ → ℝ := fun n ↦ a (Nat.succPNat (n + 1)) / a (Nat.succPNat n)
  let αAt : ℕ → ℝ := fun n ↦
    Real.log (((n + 2 : ℝ) / (n + 1 : ℝ))) /
      Real.log (q n)
  have ha_one : a 1 = 1 :=
    scaleOne_eq_one_of_exactTailScaling ha_pos hscale hzero hbase
  have hstrict : StrictMono a :=
    scaleStrictMono_of_exactTailScaling ha_pos hantitone hscale hbase
  let _ := scaleUnbounded_of_exactTailScaling ha_pos hantitone hscale hbase
  let _ := adjacentScaleRatio_antitone_of_exactTailScaling ha_pos hantitone hscale hbase
  have hq_gt : ∀ n : ℕ, 1 < q n := by
    intro n
    dsimp [q]
    rw [one_lt_div_iff]
    have hstep : Nat.succPNat n < Nat.succPNat (n + 1) := by
      exact_mod_cast (Nat.lt_succ_self (n + 1))
    exact Or.inl ⟨ha_pos (Nat.succPNat n), hstrict hstep⟩
  have hαAt_const :
      ∀ m n : ℕ, αAt m = αAt n :=
    adjacentLogExponent_constant_of_exactTailScaling_local
      ha_pos hantitone hscale hzero hbase
  let α : ℝ := αAt 0
  have hα0 : 0 < α := by
    dsimp [α, αAt, q]
    have hratio0_gt : 1 < ((↑(0 : ℕ) + 2 : ℝ) / (↑(0 : ℕ) + 1)) := by
      norm_num
    exact div_pos (Real.log_pos hratio0_gt)
      (Real.log_pos (hq_gt 0))
  have hq_formula :
      ∀ n : ℕ, q n = (((n + 2 : ℝ) / (n + 1 : ℝ)) ^ (1 / α)) := by
    intro n
    have hα_eq : α = αAt n := by
      dsimp [α]
      simpa using hαAt_const 0 n
    have hα_ne : α ≠ 0 := ne_of_gt hα0
    have hq_formula_inv :
        q n = (((n + 2 : ℝ) / (n + 1 : ℝ)) ^ α⁻¹) := by
      refine (Real.eq_rpow_inv
        (show 0 ≤ q n by exact le_of_lt (lt_trans zero_lt_one (hq_gt n)))
        (show 0 ≤ ((n + 2 : ℝ) / (n + 1 : ℝ)) by positivity) hα_ne).2 ?_
      rw [hα_eq]
      dsimp [αAt]
      have hlog_ne : Real.log (q n) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (lt_trans zero_lt_one (hq_gt n)) (by
          intro hq_one
          linarith [hq_gt n])
      rw [Real.rpow_def_of_pos (lt_trans zero_lt_one (hq_gt n))]
      have hlog_mul :
          Real.log (q n) * (Real.log ((n + 2 : ℝ) / (n + 1 : ℝ)) / Real.log (q n)) =
            Real.log ((n + 2 : ℝ) / (n + 1 : ℝ)) := by
        field_simp [hlog_ne]
      rw [hlog_mul, Real.exp_log (by positivity)]
    simpa [one_div] using hq_formula_inv
  have ha_formula_nat :
      ∀ k : ℕ, a (Nat.succPNat k) = (k + 1 : ℝ) ^ (1 / α) := by
    intro k
    induction k with
    | zero =>
        -- Proof comment: the source normalization `a₁ = 1` is the base of the telescoping
        -- reconstruction.
        simpa [α, ha_one]
    | succ k hk =>
        -- Proof comment: once the adjacent ratios are fixed, multiply the ratio formula by the
        -- inductive value of `aₖ₊₁` and collapse the product.
        have hsplit :
            a (Nat.succPNat (k + 1)) =
              q k * a (Nat.succPNat k) := by
          dsimp [q]
          field_simp [ne_of_gt (ha_pos (Nat.succPNat k))]
        calc
          a (Nat.succPNat (k + 1))
              = q k * a (Nat.succPNat k) := hsplit
          _ = (((k + 2 : ℝ) / (k + 1 : ℝ)) ^ (1 / α)) * ((k + 1 : ℝ) ^ (1 / α)) := by
                rw [hq_formula k, hk]
          _ = ((((k + 2 : ℝ) / (k + 1 : ℝ)) * (k + 1 : ℝ)) ^ (1 / α)) := by
                rw [← Real.mul_rpow (by positivity) (by positivity)]
          _ = ((k + 2 : ℝ) ^ (1 / α)) := by
                congr 1
                field_simp
          _ = ((↑(k + 1) + 1 : ℝ) ^ (1 / α)) := by
                congr 1
                norm_num [Nat.cast_add, add_assoc]
  refine ⟨α, hα0, ?_⟩
  intro n
  -- Proof comment: convert the `ℕ`-indexed telescoping formula back to the original `ℕ+`
  -- indexing through `natPred`.
  have hn_formula : a n = (((n : ℕ) : ℝ) ^ α⁻¹) := by
    have hn_cast : (((n.natPred + 1 : ℕ) : ℝ)) = ((n : ℕ) : ℝ) := by
      exact_mod_cast n.natPred_add_one
    have hn_cast_add : ((n.natPred : ℝ) + 1) = ((n : ℕ) : ℝ) := by
      exact_mod_cast n.natPred_add_one
    have hpred : a (Nat.succPNat n.natPred) = (((n : ℕ) : ℝ) ^ α⁻¹) := by
      have hpred' := ha_formula_nat n.natPred
      rw [one_div] at hpred'
      rw [hn_cast_add] at hpred'
      exact hpred'
    simpa [PNat.succPNat_natPred] using hpred
  simpa [one_div] using hn_formula

/-- Helper for Theorem 16.22: once the exact one-sided tail scaling has been normalized to the
canonical scale law, the nonzero-Lévy branch forces `α < 2`. -/
private lemma alphaLtTwo_of_exactTailScaling_nonzeroLevy_local
    {τ : LevyKhinchinTriple} {a : ℕ+ → ℝ} {α : ℝ}
    (hτ : IsCanonicalTriple τ)
    (hnu : τ.ν ≠ 0)
    (ha_pos : ∀ n : ℕ+, 0 < a n)
    (hscaleν : ∀ n : ℕ+, (n : ℕ) • τ.ν = Measure.map (fun x : ℝ ↦ a n * x) τ.ν)
    (hα0 : 0 < α)
    (ha_formula : ∀ n : ℕ+, a n = (n : ℝ) ^ (1 / α)) :
    α < 2 := by
  by_contra hα_not_lt
  have hα_ge : 2 ≤ α := le_of_not_gt hα_not_lt
  have hbound : ∀ n : ℕ+, a n ≤ 1 * Real.sqrt (n : ℝ) := by
    intro n
    have hn_one_nat : 1 ≤ (n : ℕ) := Nat.succ_le_of_lt n.pos
    have hn_one : 1 ≤ (n : ℝ) := by exact_mod_cast hn_one_nat
    have hexp_le : 1 / α ≤ 1 / (2 : ℝ) := by
      simpa [one_div] using (inv_le_inv₀ hα0 (by positivity : 0 < (2 : ℝ))).2 hα_ge
    rw [ha_formula n]
    simpa [one_mul, Real.sqrt_eq_rpow] using
      (Real.rpow_le_rpow_of_exponent_le hn_one hexp_le)
  -- Proof comment: if `α ≥ 2`, then the canonical scale law is bounded by `sqrt n`, so the
  -- earlier Gaussian-branch contradiction forces the Lévy measure to vanish.
  have hzero : τ.ν = 0 :=
    levyMeasure_zero_of_scaleSqrtBounded hτ ha_pos hscaleν (C := 1) zero_lt_one hbound
  exact hnu hzero

/-- Helper for Theorem 16.22: once one chooses a nontrivial exact one-sided tail, the remaining
index recovery is the generic monotone-tail interpolation frontier. -/
private lemma stableBroad_index_of_oneSidedTailScaling_local
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ} {F : ℝ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (hnu : τ.ν ≠ 0)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable)
    (hFanti : AntitoneOn F (Set.Ioi 0))
    (hFscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x)
    (hFzero : Tendsto F atTop (𝓝 0))
    (hFbase : ∃ x0 : ℝ, 0 < x0 ∧ 0 < F x0) :
    ∃ α : ℝ, IsStableInBroadSenseWithIndex μ α := by
  have ha_pos : ∀ n : ℕ+, 0 < a n := scalePosOfBroadStable hμ ha_nonneg hscale
  have hscaleFormula :
      ∃ α : ℝ, 0 < α ∧ ∀ n : ℕ+, a n = (n : ℝ) ^ (1 / α) :=
    scaleFormula_of_exactTailScaling_local ha_pos hFanti hFscale hFzero hFbase
  rcases hscaleFormula with ⟨α, hα0, ha_formula⟩
  have hscaleν :
      ∀ n : ℕ+, (n : ℕ) • τ.ν = Measure.map (fun x : ℝ ↦ a n * x) τ.ν :=
    stableBroad_canonicalTriple_levyMeasureScaling hμ hτ ha_nonneg hscale
  have hα_lt_two : α < 2 :=
    alphaLtTwo_of_exactTailScaling_nonzeroLevy_local
      hτ.isCanonicalTriple hnu ha_pos hscaleν hα0 ha_formula
  -- Proof comment: once the nonzero-tail branch yields the exact scale law and the canonical
  -- Lévy contradiction rules out `α ≥ 2`, the original centering sequence `d` packages the
  -- broad-stability index directly.
  refine ⟨α, ?_⟩
  refine ⟨hμ.1, ⟨hα0, hα_lt_two.le⟩, ⟨d, ?_⟩⟩
  intro n
  simpa [ha_formula n] using hscale n

/-- Helper for Theorem 16.22: the nonzero-Lévy-measure branch reduces to the generic one-sided
tail interpolation theorem after choosing the nontrivial side once. -/
private lemma stableBroad_nonzeroLevyMeasure_existsIndex_local
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable)
    (hν : τ.ν ≠ 0) :
    ∃ α : ℝ, IsStableInBroadSenseWithIndex μ α := by
  have ha_pos : ∀ n : ℕ+, 0 < a n := scalePosOfBroadStable hμ ha_nonneg hscale
  have hscaleν :
      ∀ n : ℕ+, (n : ℕ) • τ.ν = Measure.map (fun x : ℝ ↦ a n * x) τ.ν :=
    stableBroad_canonicalTriple_levyMeasureScaling hμ hτ ha_nonneg hscale
  have htail :=
    oneSidedTailScaling_of_levyMeasureScaling hτ.isCanonicalTriple ha_pos hscaleν
  rcases oneSidedTailNontrivial_of_nonzeroLevyMeasure hτ.isCanonicalTriple hν with
      hright | hleft
  · let F : ℝ → ℝ := fun x ↦ (τ.ν (Set.Ici x)).toReal
    have hFanti : AntitoneOn F (Set.Ioi 0) :=
      canonicalTriple_rightTail_toReal_antitoneOn hτ.isCanonicalTriple
    have hFscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x := by
      intro n x hx
      simpa [F, mul_comm] using (htail.1 n x hx).symm
    have hFzero : Tendsto F atTop (𝓝 0) :=
      canonicalTriple_rightTail_toReal_tendsto_zero_atTop hτ.isCanonicalTriple
    -- Proof comment: once the right tail is known to be nontrivial, stay on that side and invoke
    -- the generic exact-tail interpolation frontier.
    exact
      stableBroad_index_of_oneSidedTailScaling_local
        hμ hτ hν ha_nonneg hscale hFanti hFscale hFzero hright
  · let F : ℝ → ℝ := fun x ↦ (τ.ν (Set.Iic (-x))).toReal
    have hFanti : AntitoneOn F (Set.Ioi 0) :=
      canonicalTriple_leftTail_toReal_antitoneOn hτ.isCanonicalTriple
    have hFscale : ∀ n : ℕ+, ∀ x : ℝ, 0 < x → F (x / a n) = (n : ℝ) * F x := by
      intro n x hx
      simpa [F, mul_comm] using (htail.2 n x hx).symm
    have hFzero : Tendsto F atTop (𝓝 0) :=
      canonicalTriple_leftTail_toReal_tendsto_zero_atTop hτ.isCanonicalTriple
    -- Proof comment: the left-tail branch is identical after the one-sided selector chooses the
    -- nontrivial negative half-line.
    exact
      stableBroad_index_of_oneSidedTailScaling_local
        hμ hτ hν ha_nonneg hscale hFanti hFscale hFzero hleft

-- Proof comment: the recovered file keeps the clause-(i) surface intact after the broken
-- imported 16.17 artifact made the original source inaccessible during this attempt.
/-- Clause (i) of Theorem 16.22: a broadly stable probability law has a stability index
`α ∈ (0, 2]`. -/
theorem stable_broad_exists_index
    {μ : ProbabilityMeasure ℝ} (hμ : IsStableInBroadSense μ) :
    ∃ α : ℝ, IsStableInBroadSenseWithIndex μ α := by
  -- Route correction: the verified frontier now extracts the broad-stability scaling data,
  -- proves that every scale factor is strictly positive, and reduces the remaining work to the
  -- canonical-triple branch split from the source proof.
  rcases hμ.exists_scale_shift with ⟨a, d, ha_nonneg, hscale⟩
  have ha_pos : ∀ n : ℕ+, 0 < a n := scalePosOfBroadStable hμ ha_nonneg hscale
  rcases levyKhinchinTriple_exists_of_broadStable hμ with ⟨τ, hτ⟩
  have hGaussianScaling :
      ∀ n : ℕ+, ((a n) ^ (2 : ℕ) - (n : ℝ)) * τ.sigma2 = 0 :=
    stableBroad_canonicalTriple_gaussianScaling hμ hτ ha_nonneg hscale
  have hLevyScaling :
      ∀ n : ℕ+, (n : ℕ) • τ.ν = Measure.map (fun x : ℝ ↦ a n * x) τ.ν :=
    stableBroad_canonicalTriple_levyMeasureScaling hμ hτ ha_nonneg hscale
  by_cases hν : τ.ν = 0
  · -- Proof comment: the zero-jump branch is exactly the Gaussian case, so the scale formula is
    -- forced to be `n^(1/2)` and yields the index `2`.
    exact ⟨2, (stableBroad_zeroLevyMeasure_indexTwo hμ hτ ha_nonneg hscale hν).1⟩
  · -- Proof comment: the nonzero-jump branch is now reduced to the one-sided tail interpolation
    -- frontier, with all canonical-triple setup already discharged.
    let _ := hGaussianScaling
    let _ := hLevyScaling
    exact
      stableBroad_nonzeroLevyMeasure_existsIndex_local
        hμ hτ ha_nonneg hscale hν

-- Proof comment: the Gaussian branch remains the source-faithful target for the index-`2` case.
/-- Clause (ii) of Theorem 16.22: stability in the broad sense with index `2` forces the law to
be Gaussian. -/
theorem stable_broad_index_two_isGaussian
    {μ : ProbabilityMeasure ℝ} (hμ : IsStableInBroadSenseWithIndex μ 2) :
    IsGaussian (μ : Measure ℝ) := by
  obtain ⟨d, hscale⟩ := hμ.exists_centering
  have hμ_broad : IsStableInBroadSense μ := by
    refine ⟨hμ.1, ?_⟩
    refine ⟨fun n ↦ (n : ℝ) ^ (1 / (2 : ℝ)), d, ?_, hscale⟩
    intro n
    exact le_of_lt (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨τ, hτ⟩ := levyKhinchinTriple_exists_of_broadStable hμ_broad
  have hν : τ.ν = 0 := stableBroad_indexTwo_zeroLevyMeasure hμ hτ
  -- Proof comment: once the jump part is removed, the earlier Gaussian branch package applies
  -- verbatim to the canonical triple of `μ`.
  simpa using
    (stableBroad_zeroLevyMeasure_indexTwo
      hμ_broad hτ
      (fun n ↦ le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
      hscale hν).2

/-- Helper for Theorem 16.22: on a positive tail, the full stable Lévy measure has the same
textbook right-tail formula as its right-only model. -/
private lemma stableLevyMeasure_rightTail_toReal_full
    {α cMinus cPlus x : ℝ} (hα0 : 0 < α) (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus)
    (hx : 0 < x) :
    ((stableLevyMeasure α cMinus cPlus) (Set.Ici x)).toReal = (cPlus / α) * x ^ (-α) := by
  have hmeas : Measurable (stableLevyDensity α cMinus cPlus) :=
    measurable_stableLevyDensity α cMinus cPlus
  rw [stableLevyMeasure_def, withDensity_apply _ measurableSet_Ici]
  change
    (∫⁻ a in Set.Ici x, ENNReal.ofReal (stableLevyDensity α cMinus cPlus a) ∂volume).toReal =
      (cPlus / α) * x ^ (-α)
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ici x)] fun a : ℝ ↦ stableLevyDensity α cMinus cPlus a := by
    filter_upwards with a
    exact stableLevyDensity_nonneg hcMinus hcPlus a
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable]
  have hkernel :
      ∫ a in Set.Ici x, stableLevyDensity α cMinus cPlus a ∂volume =
        ∫ a in Set.Ioi x, cPlus * a ^ (-α - 1) ∂volume := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun a ha ↦ ?_
    have ha_pos : 0 < a := lt_trans hx ha
    have hnot_neg : ¬ a < 0 := by
      linarith
    -- Proof comment: on a positive ray, only the positive branch of the stable density survives.
    rw [stableLevyDensity_apply]
    simp [hnot_neg, ha_pos]
  have hα_lt : -α - 1 < -1 := by
    linarith
  rw [hkernel, integral_const_mul, integral_Ioi_rpow_of_lt hα_lt hx]
  have hαne : α ≠ 0 := by
    linarith
  field_simp [hαne]
  ring

/-- Helper for Theorem 16.22: if the positive stable coefficient vanishes, then the model has no
right tail away from `0`. -/
private lemma stableLevyMeasure_rightTail_eq_zero_of_cPlus_zero
    {α cMinus x : ℝ} (hx : 0 < x) :
    stableLevyMeasure α cMinus 0 (Set.Ici x) = 0 := by
  rw [stableLevyMeasure_def, withDensity_apply _ measurableSet_Ici]
  refine MeasureTheory.lintegral_eq_zero_of_ae_eq_zero ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ici]
  filter_upwards with a ha
  have ha_pos : 0 < a := lt_of_lt_of_le hx ha
  rw [stableLevyDensity_apply]
  simp [not_lt.mpr ha_pos.le, ha_pos]

/-- Helper for Theorem 16.22: the right tails of the stable model are finite away from `0`. -/
private lemma stableLevyMeasure_rightTail_ltTop
    {α cMinus cPlus x : ℝ} (hα0 : 0 < α) (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus)
    (hx : 0 < x) :
    (stableLevyMeasure α cMinus cPlus) (Set.Ici x) < ⊤ := by
  by_cases hcPlus_zero : cPlus = 0
  · rw [hcPlus_zero]
    simpa [stableLevyMeasure_rightTail_eq_zero_of_cPlus_zero hx]
  · have hcPlus_pos : 0 < cPlus := by
      exact lt_of_le_of_ne hcPlus (by simpa [eq_comm] using hcPlus_zero)
    have htail :
        ((stableLevyMeasure α cMinus cPlus) (Set.Ici x)).toReal =
          (cPlus / α) * x ^ (-α) :=
      stableLevyMeasure_rightTail_toReal_full hα0 hcMinus hcPlus hx
    have htail_pos : 0 < ((cPlus / α) * x ^ (-α)) := by
      refine mul_pos ?_ ?_
      · exact div_pos hcPlus_pos hα0
      · exact Real.rpow_pos_of_pos hx _
    refine lt_top_iff_ne_top.mpr ?_
    intro htop
    rw [htop, ENNReal.toReal_top] at htail
    linarith

/-- Helper for Theorem 16.22: on a negative tail, the full stable Lévy measure has the same
textbook left-tail formula as its left-only model. -/
private lemma stableLevyMeasure_leftTail_toReal_full
    {α cMinus cPlus x : ℝ} (hα0 : 0 < α) (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus)
    (hx : 0 < x) :
    ((stableLevyMeasure α cMinus cPlus) (Set.Iic (-x))).toReal = (cMinus / α) * x ^ (-α) := by
  have hmeas : Measurable (stableLevyDensity α cMinus cPlus) :=
    measurable_stableLevyDensity α cMinus cPlus
  rw [stableLevyMeasure_def, withDensity_apply _ measurableSet_Iic]
  change
    (∫⁻ a in Set.Iic (-x), ENNReal.ofReal (stableLevyDensity α cMinus cPlus a) ∂volume).toReal =
      (cMinus / α) * x ^ (-α)
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Iic (-x))] fun a : ℝ ↦ stableLevyDensity α cMinus cPlus a := by
    filter_upwards with a
    exact stableLevyDensity_nonneg hcMinus hcPlus a
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable]
  have hkernel :
      ∫ a in Set.Iic (-x), stableLevyDensity α cMinus cPlus a ∂volume =
        ∫ a in Set.Iio (-x), cMinus * (-a) ^ (-α - 1) ∂volume := by
    rw [MeasureTheory.integral_Iic_eq_integral_Iio]
    refine setIntegral_congr_fun measurableSet_Iio fun a ha ↦ ?_
    have ha_lt : a < -x := ha
    have ha_neg : a < 0 := by
      linarith
    -- Proof comment: on a negative ray, only the negative branch of the stable density survives.
    rw [stableLevyDensity_apply]
    simp [ha_neg]
  have hcomp :
      ∫ a in Set.Iio (-x), cMinus * (-a) ^ (-α - 1) ∂volume =
        ∫ a in Set.Ioi x, cMinus * a ^ (-α - 1) ∂volume := by
    calc
      ∫ a in Set.Iio (-x), cMinus * (-a) ^ (-α - 1) ∂volume
          = ∫ a in Set.Iic (-x), cMinus * (-a) ^ (-α - 1) ∂volume := by
              rw [← MeasureTheory.integral_Iic_eq_integral_Iio]
      _ = ∫ a in Set.Ioi x, cMinus * a ^ (-α - 1) ∂volume := by
            simpa using
              (integral_comp_neg_Iic (-x) (fun t : ℝ ↦ cMinus * t ^ (-α - 1)))
  have hα_lt : -α - 1 < -1 := by
    linarith
  rw [hkernel, hcomp, integral_const_mul, integral_Ioi_rpow_of_lt hα_lt hx]
  have hαne : α ≠ 0 := by
    linarith
  field_simp [hαne]
  ring

/-- Helper for Theorem 16.22: if the negative stable coefficient vanishes, then the model has no
left tail away from `0`. -/
private lemma stableLevyMeasure_leftTail_eq_zero_of_cMinus_zero
    {α cPlus x : ℝ} (hx : 0 < x) :
    stableLevyMeasure α 0 cPlus (Set.Iic (-x)) = 0 := by
  rw [stableLevyMeasure_def, withDensity_apply _ measurableSet_Iic]
  refine MeasureTheory.lintegral_eq_zero_of_ae_eq_zero ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic]
  filter_upwards with a ha
  have ha_le : a ≤ -x := ha
  have ha_neg : a < 0 := by
    linarith [hx, ha_le]
  rw [stableLevyDensity_apply]
  simp [ha_neg]

/-- Helper for Theorem 16.22: the left tails of the stable model are finite away from `0`. -/
private lemma stableLevyMeasure_leftTail_ltTop
    {α cMinus cPlus x : ℝ} (hα0 : 0 < α) (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus)
    (hx : 0 < x) :
    (stableLevyMeasure α cMinus cPlus) (Set.Iic (-x)) < ⊤ := by
  by_cases hcMinus_zero : cMinus = 0
  · rw [hcMinus_zero]
    simpa [stableLevyMeasure_leftTail_eq_zero_of_cMinus_zero hx]
  · have hcMinus_pos : 0 < cMinus := by
      exact lt_of_le_of_ne hcMinus (by simpa [eq_comm] using hcMinus_zero)
    have htail :
        ((stableLevyMeasure α cMinus cPlus) (Set.Iic (-x))).toReal =
          (cMinus / α) * x ^ (-α) :=
      stableLevyMeasure_leftTail_toReal_full hα0 hcMinus hcPlus hx
    have htail_pos : 0 < ((cMinus / α) * x ^ (-α)) := by
      refine mul_pos ?_ ?_
      · exact div_pos hcMinus_pos hα0
      · exact Real.rpow_pos_of_pos hx _
    refine lt_top_iff_ne_top.mpr ?_
    intro htop
    rw [htop, ENNReal.toReal_top] at htail
    linarith

/-- Helper for Theorem 16.22: matched finite closed right tails determine the shell masses on
`(0, ∞)`. -/
private lemma rightIco_eq_of_closedTailEq
    {μ ν : Measure ℝ}
    (hμfin : ∀ x : ℝ, 0 < x → μ (Set.Ici x) < ⊤)
    (hνfin : ∀ x : ℝ, 0 < x → ν (Set.Ici x) < ⊤)
    (htail :
      ∀ x : ℝ, 0 < x → (μ (Set.Ici x)).toReal = (ν (Set.Ici x)).toReal) :
    ∀ {a b : ℝ}, 0 < a → a < b → μ (Set.Ico a b) = ν (Set.Ico a b) := by
  intro a b ha hab
  have hμa :
      μ (Set.Ici a) = ν (Set.Ici a) := by
    rw [← ENNReal.toReal_eq_toReal_iff' (hμfin a ha).ne (hνfin a ha).ne]
    exact htail a ha
  have hμb :
      μ (Set.Ici b) = ν (Set.Ici b) := by
    rw [← ENNReal.toReal_eq_toReal_iff' (hμfin b (lt_trans ha hab)).ne
      (hνfin b (lt_trans ha hab)).ne]
    exact htail b (lt_trans ha hab)
  -- Proof comment: `Ico a b` is the difference of the two closed tails, so finite-tail
  -- subtraction turns the matched tail values into matched shell masses.
  calc
    μ (Set.Ico a b) = μ (Set.Ici a) - μ (Set.Ici b) := by
      rw [← Set.Ici_diff_Ici, measure_diff (Set.Ici_subset_Ici.2 hab.le) nullMeasurableSet_Ici
        (hμfin b (lt_trans ha hab)).ne]
    _ = ν (Set.Ici a) - ν (Set.Ici b) := by rw [hμa, hμb]
    _ = ν (Set.Ico a b) := by
      rw [← Set.Ici_diff_Ici, measure_diff (Set.Ici_subset_Ici.2 hab.le) nullMeasurableSet_Ici
        (hνfin b (lt_trans ha hab)).ne]

/-- Helper for Theorem 16.22: matched finite closed left tails determine the shell masses on
`(-∞, 0)`. -/
private lemma leftIoc_eq_of_closedTailEq
    {μ ν : Measure ℝ}
    (hμfin : ∀ x : ℝ, 0 < x → μ (Set.Iic (-x)) < ⊤)
    (hνfin : ∀ x : ℝ, 0 < x → ν (Set.Iic (-x)) < ⊤)
    (htail :
      ∀ x : ℝ, 0 < x → (μ (Set.Iic (-x))).toReal = (ν (Set.Iic (-x))).toReal) :
    ∀ {a b : ℝ}, a < b → b < 0 → μ (Set.Ioc a b) = ν (Set.Ioc a b) := by
  intro a b hab hb0
  have hμa_fin : μ (Set.Iic a) < ⊤ := by
    simpa using hμfin (-a) (by linarith)
  have hνa_fin : ν (Set.Iic a) < ⊤ := by
    simpa using hνfin (-a) (by linarith)
  have hμb_fin : μ (Set.Iic b) < ⊤ := by
    simpa using hμfin (-b) (by linarith)
  have hνb_fin : ν (Set.Iic b) < ⊤ := by
    simpa using hνfin (-b) (by linarith)
  have hμa :
      μ (Set.Iic a) = ν (Set.Iic a) := by
    rw [← ENNReal.toReal_eq_toReal_iff' hμa_fin.ne hνa_fin.ne]
    simpa using htail (-a) (by linarith)
  have hμb :
      μ (Set.Iic b) = ν (Set.Iic b) := by
    rw [← ENNReal.toReal_eq_toReal_iff' hμb_fin.ne hνb_fin.ne]
    simpa using htail (-b) (by linarith)
  -- Proof comment: on the negative half-line, `Ioc a b` is the difference of the nested closed
  -- left tails `Iic b` and `Iic a`.
  calc
    μ (Set.Ioc a b) = μ (Set.Iic b) - μ (Set.Iic a) := by
      rw [← Set.Iic_diff_Iic, measure_diff (Set.Iic_subset_Iic.2 hab.le) nullMeasurableSet_Iic
        hμa_fin.ne]
    _ = ν (Set.Iic b) - ν (Set.Iic a) := by rw [hμa, hμb]
    _ = ν (Set.Ioc a b) := by
      rw [← Set.Iic_diff_Iic, measure_diff (Set.Iic_subset_Iic.2 hab.le) nullMeasurableSet_Iic
        hνa_fin.ne]

/-- Helper for Theorem 16.22: matching positive-shell masses identifies the positive
restrictions. -/
private lemma positiveRestrict_eq_of_rightIcoEq
    {μ ν : Measure ℝ}
    (hμfin : ∀ x : ℝ, 0 < x → μ (Set.Ici x) < ⊤)
    (hIco : ∀ {a b : ℝ}, 0 < a → a < b → μ (Set.Ico a b) = ν (Set.Ico a b)) :
    μ.restrict (Set.Ioi 0) = ν.restrict (Set.Ioi 0) := by
  let μplus : Measure (Set.Ioi (0 : ℝ)) := Measure.comap (↑) μ
  let νplus : Measure (Set.Ioi (0 : ℝ)) := Measure.comap (↑) ν
  have hplus : μplus = νplus := by
    apply Measure.ext_of_Ico'
    · intro a b hab
      have himage :
          ((↑) '' (Set.Ico a b : Set (Set.Ioi (0 : ℝ))) : Set ℝ) = Set.Ico (a : ℝ) b := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          refine ⟨⟨x, lt_of_lt_of_le a.2 hx.1⟩, hx, rfl⟩
      dsimp [μplus]
      rw [comap_subtype_coe_apply measurableSet_Ioi μ (Set.Ico a b), himage]
      exact (lt_of_le_of_lt (measure_mono fun y hy ↦ hy.1) (hμfin a a.2)).ne
    · intro a b hab
      have himage :
          ((↑) '' (Set.Ico a b : Set (Set.Ioi (0 : ℝ))) : Set ℝ) = Set.Ico (a : ℝ) b := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          refine ⟨⟨x, lt_of_lt_of_le a.2 hx.1⟩, hx, rfl⟩
      dsimp [μplus, νplus]
      rw [comap_subtype_coe_apply measurableSet_Ioi μ (Set.Ico a b),
        comap_subtype_coe_apply measurableSet_Ioi ν (Set.Ico a b)]
      simpa [himage] using hIco a.2 hab
  have hmap := congrArg (Measure.map ((↑) : Set.Ioi (0 : ℝ) → ℝ)) hplus
  calc
    μ.restrict (Set.Ioi 0) = Measure.map ((↑) : Set.Ioi (0 : ℝ) → ℝ) μplus := by
      symm
      simpa [μplus] using (map_comap_subtype_coe measurableSet_Ioi μ)
    _ = Measure.map ((↑) : Set.Ioi (0 : ℝ) → ℝ) νplus := by simpa using hmap
    _ = ν.restrict (Set.Ioi 0) := by
      simpa [νplus] using (map_comap_subtype_coe measurableSet_Ioi ν)

/-- Helper for Theorem 16.22: matching negative-shell masses identifies the negative
restrictions. -/
private lemma negativeRestrict_eq_of_leftIocEq
    {μ ν : Measure ℝ}
    (hμfin : ∀ x : ℝ, 0 < x → μ (Set.Iic (-x)) < ⊤)
    (hIoc : ∀ {a b : ℝ}, a < b → b < 0 → μ (Set.Ioc a b) = ν (Set.Ioc a b)) :
    μ.restrict (Set.Iio 0) = ν.restrict (Set.Iio 0) := by
  let μminus : Measure (Set.Iio (0 : ℝ)) := Measure.comap (↑) μ
  let νminus : Measure (Set.Iio (0 : ℝ)) := Measure.comap (↑) ν
  have hminus : μminus = νminus := by
    apply Measure.ext_of_Ioc'
    · intro a b hab
      have himage :
          ((↑) '' (Set.Ioc a b : Set (Set.Iio (0 : ℝ))) : Set ℝ) = Set.Ioc (a : ℝ) b := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          refine ⟨⟨x, lt_of_le_of_lt hx.2 b.2⟩, hx, rfl⟩
      dsimp [μminus]
      rw [comap_subtype_coe_apply measurableSet_Iio μ (Set.Ioc a b), himage]
      have hb_pos : 0 < -(b : ℝ) := by
        exact neg_pos.mpr b.2
      have hmono : μ (Set.Ioc (a : ℝ) b) ≤ μ (Set.Iic (b : ℝ)) :=
        measure_mono fun y hy ↦ hy.2
      exact (lt_of_le_of_lt hmono (by simpa [neg_neg] using hμfin (-(b : ℝ)) hb_pos)).ne
    · intro a b hab
      have himage :
          ((↑) '' (Set.Ioc a b : Set (Set.Iio (0 : ℝ))) : Set ℝ) = Set.Ioc (a : ℝ) b := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          refine ⟨⟨x, lt_of_le_of_lt hx.2 b.2⟩, hx, rfl⟩
      dsimp [μminus, νminus]
      rw [comap_subtype_coe_apply measurableSet_Iio μ (Set.Ioc a b),
        comap_subtype_coe_apply measurableSet_Iio ν (Set.Ioc a b)]
      simpa [himage] using hIoc hab b.2
  have hmap := congrArg (Measure.map ((↑) : Set.Iio (0 : ℝ) → ℝ)) hminus
  calc
    μ.restrict (Set.Iio 0) = Measure.map ((↑) : Set.Iio (0 : ℝ) → ℝ) μminus := by
      symm
      simpa [μminus] using (map_comap_subtype_coe measurableSet_Iio μ)
    _ = Measure.map ((↑) : Set.Iio (0 : ℝ) → ℝ) νminus := by simpa using hmap
    _ = ν.restrict (Set.Iio 0) := by
      simpa [νminus] using (map_comap_subtype_coe measurableSet_Iio ν)

/-- Helper for Theorem 16.22: the stable Lévy model has no atom at the origin. -/
private lemma stableLevyMeasure_singleton_zero (α cMinus cPlus : ℝ) :
    stableLevyMeasure α cMinus cPlus ({0} : Set ℝ) = 0 := by
  rw [stableLevyMeasure_def, withDensity_apply _ (measurableSet_singleton 0)]
  simp [stableLevyDensity_apply]

/-- Helper for Theorem 16.22: for `0 < α < 2`, the canonical scale at `n = 2` is strictly larger
than `2`. -/
private lemma stableScaleSquareAtTwo_gt_two_of_index_ltTwo_local
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    (Real.rpow (2 : ℝ) (1 / α)) ^ (2 : ℕ) > 2 := by
  have hExpLt : (1 : ℝ) < 2 / α := by
    rw [lt_div_iff₀ hα0]
    linarith
  have hpowLt :
      (2 : ℝ) ^ (1 : ℝ) < (2 : ℝ) ^ (2 / α) :=
    Real.rpow_lt_rpow_of_exponent_lt (show 1 < (2 : ℝ) by norm_num) hExpLt
  have hpowEq :
      (Real.rpow (2 : ℝ) (1 / α)) ^ (2 : ℕ) = (2 : ℝ) ^ (2 / α) := by
    change (((2 : ℝ) ^ (1 / α)) ^ (2 : ℕ)) = (2 : ℝ) ^ (2 / α)
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (show 0 ≤ (2 : ℝ) by positivity)]
    congr 1
    ring
  have hfinal : (2 : ℝ) < (Real.rpow (2 : ℝ) (1 / α)) ^ (2 : ℕ) := by
    rw [hpowEq]
    simpa using hpowLt
  simpa using hfinal

-- Proof comment: clause (iii) is the Levy-density identification for the non-Gaussian branch.
/-- Clause (iii) of Theorem 16.22: for index `α ∈ (0, 2)`, every canonical triple of a broadly
stable law has the power-law Levy density `c⁻(-x)^(-α-1)` on `(-∞,0)` and
`c⁺x^(-α-1)` on `(0,∞)`. -/
theorem stable_broad_levyMeasure_eq_stableLevyMeasure
    {μ : ProbabilityMeasure ℝ} {α : ℝ} {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ α) (hα₂ : α < 2)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    ∃ cMinus cPlus : ℝ,
      StableLevyCoefficients cMinus cPlus ∧
        τ.ν = stableLevyMeasure α cMinus cPlus := by
  -- Route correction: the blocked global interval comparison across `0` is replaced by sign-split
  -- shell reconstruction on `(0, ∞)` and `(-∞, 0)`, followed by recombining the two
  -- restrictions with the zero atom.
  have hα0 : 0 < α := hμ.index_mem_Ioc.1
  have hRightAll := fixedIndex_rightTail_powerLaw_allPos hμ hτ
  have hLeftAll := fixedIndex_leftTail_powerLaw_allPos hμ hτ
  let cPlus : ℝ := α * (τ.ν (Set.Ici 1)).toReal
  let cMinus : ℝ := α * (τ.ν (Set.Iic (-1))).toReal
  have hcPlus_nonneg : 0 ≤ cPlus := by
    dsimp [cPlus]
    exact mul_nonneg hα0.le ENNReal.toReal_nonneg
  have hcMinus_nonneg : 0 ≤ cMinus := by
    dsimp [cMinus]
    exact mul_nonneg hα0.le ENNReal.toReal_nonneg
  have hRightMatch :
      ∀ x : ℝ, 0 < x →
        (τ.ν (Set.Ici x)).toReal =
          ((stableLevyMeasure α cMinus cPlus) (Set.Ici x)).toReal := by
    intro x hx
    rw [hRightAll x hx,
      stableLevyMeasure_rightTail_toReal_full hα0 hcMinus_nonneg hcPlus_nonneg hx]
    have hαne : α ≠ 0 := by
      linarith
    -- Proof comment: the coefficient `c⁺ = α · ν([1, ∞))` was chosen so the model tail matches
    -- the recovered tail exactly at every positive cutoff.
    field_simp [cPlus, hαne]
    ring
  have hLeftMatch :
      ∀ x : ℝ, 0 < x →
        (τ.ν (Set.Iic (-x))).toReal =
          ((stableLevyMeasure α cMinus cPlus) (Set.Iic (-x))).toReal := by
    intro x hx
    rw [hLeftAll x hx,
      stableLevyMeasure_leftTail_toReal_full hα0 hcMinus_nonneg hcPlus_nonneg hx]
    have hαne : α ≠ 0 := by
      linarith
    -- Proof comment: the same normalization identifies the negative half-line coefficient `c⁻`.
    field_simp [cMinus, hαne]
    ring
  have hRightIco :
      ∀ {a b : ℝ}, 0 < a → a < b →
        τ.ν (Set.Ico a b) = (stableLevyMeasure α cMinus cPlus) (Set.Ico a b) :=
    rightIco_eq_of_closedTailEq
      (μ := τ.ν) (ν := stableLevyMeasure α cMinus cPlus)
      (fun x hx ↦ canonicalTriple_rightTail_lt_top hτ.isCanonicalTriple hx)
      (fun x hx ↦ stableLevyMeasure_rightTail_ltTop hα0 hcMinus_nonneg hcPlus_nonneg hx)
      hRightMatch
  have hLeftIoc :
      ∀ {a b : ℝ}, a < b → b < 0 →
        τ.ν (Set.Ioc a b) = (stableLevyMeasure α cMinus cPlus) (Set.Ioc a b) :=
    leftIoc_eq_of_closedTailEq
      (μ := τ.ν) (ν := stableLevyMeasure α cMinus cPlus)
      (fun x hx ↦ canonicalTriple_leftTail_lt_top hτ.isCanonicalTriple hx)
      (fun x hx ↦ stableLevyMeasure_leftTail_ltTop hα0 hcMinus_nonneg hcPlus_nonneg hx)
      hLeftMatch
  have hPos :
      τ.ν.restrict (Set.Ioi 0) =
        (stableLevyMeasure α cMinus cPlus).restrict (Set.Ioi 0) :=
    positiveRestrict_eq_of_rightIcoEq
      (μ := τ.ν) (ν := stableLevyMeasure α cMinus cPlus)
      (fun x hx ↦ canonicalTriple_rightTail_lt_top hτ.isCanonicalTriple hx) hRightIco
  have hNeg :
      τ.ν.restrict (Set.Iio 0) =
        (stableLevyMeasure α cMinus cPlus).restrict (Set.Iio 0) :=
    negativeRestrict_eq_of_leftIocEq
      (μ := τ.ν) (ν := stableLevyMeasure α cMinus cPlus)
      (fun x hx ↦ canonicalTriple_leftTail_lt_top hτ.isCanonicalTriple hx) hLeftIoc
  have hRestrictCompl :
      τ.ν.restrict ({0}ᶜ : Set ℝ) =
        (stableLevyMeasure α cMinus cPlus).restrict ({0}ᶜ : Set ℝ) := by
    have hsplit : ({0}ᶜ : Set ℝ) = Set.Iio 0 ∪ Set.Ioi 0 := by
      simpa using (Set.Iio_union_Ioi (a := (0 : ℝ))).symm
    have hτsplit :
        τ.ν.restrict ({0}ᶜ : Set ℝ) =
          τ.ν.restrict (Set.Iio 0) + τ.ν.restrict (Set.Ioi 0) := by
      rw [hsplit, Measure.restrict_union (Set.disjoint_left.2 <| by
        intro x hx hx'
        have hx_pos : 0 < x := by simpa using hx'
        exact (not_lt_of_ge hx.le) hx_pos) measurableSet_Ioi]
    have hModelSplit :
        (stableLevyMeasure α cMinus cPlus).restrict ({0}ᶜ : Set ℝ) =
          (stableLevyMeasure α cMinus cPlus).restrict (Set.Iio 0) +
            (stableLevyMeasure α cMinus cPlus).restrict (Set.Ioi 0) := by
      rw [hsplit, Measure.restrict_union (Set.disjoint_left.2 <| by
        intro x hx hx'
        have hx_pos : 0 < x := by simpa using hx'
        exact (not_lt_of_ge hx.le) hx_pos) measurableSet_Ioi]
    calc
      τ.ν.restrict ({0}ᶜ : Set ℝ)
          = τ.ν.restrict (Set.Iio 0) + τ.ν.restrict (Set.Ioi 0) := hτsplit
      _ =
          (stableLevyMeasure α cMinus cPlus).restrict (Set.Iio 0) +
            (stableLevyMeasure α cMinus cPlus).restrict (Set.Ioi 0) := by rw [hNeg, hPos]
      _ = (stableLevyMeasure α cMinus cPlus).restrict ({0}ᶜ : Set ℝ) := hModelSplit.symm
  have hν_eq :
      τ.ν = stableLevyMeasure α cMinus cPlus := by
    have hsingleton :
        τ.ν.restrict ({0} : Set ℝ) =
          (stableLevyMeasure α cMinus cPlus).restrict ({0} : Set ℝ) := by
      rw [Measure.restrict_singleton,
        hτ.isCanonicalTriple.isCanonicalMeasure.measure_singleton_zero, zero_smul,
        Measure.restrict_singleton, stableLevyMeasure_singleton_zero, zero_smul]
    have hcompl :
        τ.ν.restrict ({0}ᶜ : Set ℝ) =
          (stableLevyMeasure α cMinus cPlus).restrict ({0}ᶜ : Set ℝ) := by
      exact hRestrictCompl
    rw [← Measure.restrict_add_restrict_compl (μ := τ.ν) (measurableSet_singleton (0 : ℝ)),
      ← Measure.restrict_add_restrict_compl (μ := stableLevyMeasure α cMinus cPlus)
        (measurableSet_singleton (0 : ℝ)),
      hsingleton, hcompl]
  have hcoeff_sum_pos : 0 < cMinus + cPlus := by
    by_contra hnonpos
    have hsum_zero : cMinus + cPlus = 0 := by
      linarith
    have hcMinus_zero : cMinus = 0 := by
      linarith
    have hcPlus_zero : cPlus = 0 := by
      linarith
    have hνzero : τ.ν = 0 := by
      calc
        τ.ν = stableLevyMeasure α cMinus cPlus := hν_eq
        _ = stableLevyMeasure α 0 0 := by simpa [hcMinus_zero, hcPlus_zero]
        _ = 0 := stableLevyMeasure_zero_zero α
    obtain ⟨d, hscale⟩ := hμ.exists_centering
    have hμ_broad : IsStableInBroadSense μ := by
      refine ⟨hμ.1, ?_⟩
      refine ⟨fun n ↦ (n : ℝ) ^ (1 / α), d, ?_, hscale⟩
      intro n
      exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) _)
    have ha_nonneg : ∀ n : ℕ+, 0 ≤ (n : ℝ) ^ (1 / α) := by
      intro n
      exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) _)
    have hσscale :
        ((((2 : ℝ) ^ (1 / α)) ^ (2 : ℕ)) - (2 : ℝ)) * τ.sigma2 = 0 := by
      simpa using stableBroad_canonicalTriple_gaussianScaling hμ_broad hτ ha_nonneg hscale 2
    have hcoef_pos : 0 < (((2 : ℝ) ^ (1 / α)) ^ (2 : ℕ)) - (2 : ℝ) := by
      exact sub_pos.mpr (stableScaleSquareAtTwo_gt_two_of_index_ltTwo_local hα0 hα₂)
    have hσzero : τ.sigma2 = 0 := by
      exact (mul_eq_zero.mp hσscale).resolve_left (ne_of_gt hcoef_pos)
    exact hμ.1 τ.b (eq_diracProba_of_zeroGaussian_zeroLevy hτ hσzero hνzero)
  exact ⟨cMinus, cPlus, ⟨hcMinus_nonneg, hcPlus_nonneg, hcoeff_sum_pos⟩, hν_eq⟩

/-- Helper for Theorem 16.22: once the Lévy measure is known to be stable and `α ≠ 1`, the broad
centering sequence is the explicit affine correction from the source proof. -/
private lemma stableBroad_stableLevy_centering_eq_of_ne_one_local
    {μ : ProbabilityMeasure ℝ}
    {τ : LevyKhinchinTriple} {d : ℕ+ → ℝ} {α cMinus cPlus : ℝ}
    (hμ : IsStableInBroadSenseWithIndex μ α)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) =
        map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) (d n)).aemeasurable)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (hcoeff : StableLevyCoefficients cMinus cPlus)
    (hν : τ.ν = stableLevyMeasure α cMinus cPlus)
    (hα : α ∈ Set.Ioo (0 : ℝ) 2) (hα_ne : α ≠ 1) :
    ∀ n : ℕ+,
      d n = (τ.b + (cPlus - cMinus) / (α - 1)) * ((n : ℝ) - (n : ℝ) ^ (1 / α)) := by
  have hμ_broad : IsStableInBroadSense μ := by
    refine ⟨hμ.1, ?_⟩
    refine ⟨fun n ↦ (n : ℝ) ^ (1 / α), d, ?_, hscale⟩
    intro n
    exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) _)
  have ha_nonneg : ∀ n : ℕ+, 0 ≤ (n : ℝ) ^ (1 / α) := by
    intro n
    exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) _)
  intro n
  have hbField := stableBroad_bField_eq hμ_broad hτ ha_nonneg hscale n
  have hα0 : 0 < α := hα.1
  have hn_one_le : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast PNat.one_le n
  have hs_one : 1 ≤ (n : ℝ) ^ (1 / α) := by
    exact Real.one_le_rpow hn_one_le (one_div_nonneg.mpr hα0.le)
  have hcorrection :
      ((n : ℝ) ^ (1 / α)) *
          ∫ x : ℝ,
            ((if |x| < 1 / ((n : ℝ) ^ (1 / α)) then x else 0) -
                (if |x| < 1 then x else 0))
              ∂τ.ν =
        -((cPlus - cMinus) / (α - 1)) * ((n : ℝ) - (n : ℝ) ^ (1 / α)) := by
    rw [hν]
    have hcorr :=
      stableLevyCenteringCorrection_eq_of_ne_one_local
        (α := α) (cMinus := cMinus) (cPlus := cPlus)
        (s := (n : ℝ) ^ (1 / α)) hs_one hcoeff.1 hcoeff.2.1 hα0 hα_ne
    rw [stableScalePow_eq_natCast_local hα0 n] at hcorr
    exact hcorr
  -- Proof comment: insert the explicit shell-correction formula into the drift comparison.
  rw [hcorrection] at hbField
  linarith

/-- Helper for Theorem 16.22: translating by `-b` removes a centering sequence of the form
`b (n - n^(1 / α))`, so the translated law is strictly stable with index `α`. -/
private lemma translatedLaw_isStableWithIndex_of_centering_eq_local
    {μ : ProbabilityMeasure ℝ} {α : ℝ} {d : ℕ+ → ℝ} {b : ℝ}
    (hμ : IsStableInBroadSenseWithIndex μ α)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) =
        map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) (d n)).aemeasurable)
    (hd : ∀ n : ℕ+, d n = b * ((n : ℝ) - (n : ℝ) ^ (1 / α))) :
    IsStableWithIndex (map μ (measurable_affineMap 1 (-b)).aemeasurable) α := by
  refine ⟨shiftedLaw_not_dirac_local hμ.1 b, hμ.index_mem_Ioc, ?_⟩
  intro n
  let s : ℝ := (n : ℝ) ^ (1 / α)
  calc
    (map μ (measurable_affineMap 1 (-b)).aemeasurable) ^ (n : ℕ)
        = map (μ ^ (n : ℕ)) (measurable_affineMap 1 ((n : ℝ) * (-b))).aemeasurable := by
            simpa using map_affine_pow_eq_map_pow_affine μ 1 (-b) n
    _ = map (map μ (measurable_affineMap s (d n)).aemeasurable)
          (measurable_affineMap 1 ((n : ℝ) * (-b))).aemeasurable := by
            rw [hscale n]
    _ = map μ (measurable_affineMap (1 * s) (1 * d n + (n : ℝ) * (-b))).aemeasurable := by
          simpa [s] using
            (map_map_affine_eq_map_affine_local μ s (d n) 1 ((n : ℝ) * (-b)))
    _ = map μ (measurable_affineMap s (1 * d n + (n : ℝ) * (-b))).aemeasurable := by
          simp [one_mul]
    _ = map μ (measurable_affineMap s (-(s * b))).aemeasurable := by
          have hd' : 1 * d n + (n : ℝ) * (-b) = -(s * b) := by
            rw [hd n]
            dsimp [s]
            ring_nf
          rw [hd']
    _ = map (map μ (measurable_affineMap 1 (-b)).aemeasurable)
          (measurable_affineMap s 0).aemeasurable := by
            symm
            simpa [s] using
              (map_map_affine_eq_map_affine_local μ 1 (-b) s 0)

-- Proof comment: clause (iv) removes the broad centering term when `α ≠ 1`.
/-- Clause (iv) of Theorem 16.22: if `α ≠ 1`, a suitable translation of a broadly stable law with
index `α` is strictly stable with the same index. -/
theorem stable_broad_translate_isStable_of_ne_one
    {μ : ProbabilityMeasure ℝ} {α : ℝ}
    (hμ : IsStableInBroadSenseWithIndex μ α) (hα : α ≠ 1) :
    ∃ b : ℝ, IsStableWithIndex (map μ (measurable_affineMap 1 (-b)).aemeasurable) α := by
  obtain ⟨d, hscale⟩ := hμ.exists_centering
  by_cases hα_two : α = 2
  · subst hα_two
    have hμ_broad : IsStableInBroadSense μ := by
      refine ⟨hμ.1, ?_⟩
      refine ⟨fun n ↦ (n : ℝ) ^ (1 / (2 : ℝ)), d, ?_, hscale⟩
      intro n
      exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) _)
    obtain ⟨τ, hτ⟩ := levyKhinchinTriple_exists_of_broadStable hμ_broad
    have hν : τ.ν = 0 := stableBroad_indexTwo_zeroLevyMeasure hμ hτ
    have ha_nonneg : ∀ n : ℕ+, 0 ≤ (n : ℝ) ^ (1 / (2 : ℝ)) := by
      intro n
      exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) _)
    have hd :
        ∀ n : ℕ+, d n = τ.b * ((n : ℝ) - (n : ℝ) ^ (1 / (2 : ℝ))) :=
      stableBroad_zeroLevyMeasure_centering_eq hμ_broad hτ ha_nonneg hscale hν
    -- Proof comment: in the Gaussian branch, translating by the drift removes the entire
    -- broad-stability centering sequence.
    exact ⟨τ.b, translatedLaw_isStableWithIndex_of_centering_eq_local hμ hscale hd⟩
  · have hα_lt_two : α < 2 := lt_of_le_of_ne hμ.index_mem_Ioc.2 hα_two
    have hμ_broad : IsStableInBroadSense μ := by
      refine ⟨hμ.1, ?_⟩
      refine ⟨fun n ↦ (n : ℝ) ^ (1 / α), d, ?_, hscale⟩
      intro n
      exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) _)
    obtain ⟨τ, hτ⟩ := levyKhinchinTriple_exists_of_broadStable hμ_broad
    obtain ⟨cMinus, cPlus, hcoeff, hν⟩ :=
      stable_broad_levyMeasure_eq_stableLevyMeasure hμ hα_lt_two hτ
    have hα_mem : α ∈ Set.Ioo (0 : ℝ) 2 := ⟨hμ.index_mem_Ioc.1, hα_lt_two⟩
    let b : ℝ := τ.b + (cPlus - cMinus) / (α - 1)
    have hd :
        ∀ n : ℕ+, d n = b * ((n : ℝ) - (n : ℝ) ^ (1 / α)) := by
      intro n
      simpa [b] using
        stableBroad_stableLevy_centering_eq_of_ne_one_local
          hμ hscale hτ hcoeff hν hα_mem hα n
    -- Proof comment: once the Lévy measure is in stable normal form, the same translation
    -- cancellation removes the residual broad-stability drift.
    exact ⟨b, translatedLaw_isStableWithIndex_of_centering_eq_local hμ hscale hd⟩

-- Proof comment: clause (v) uses the coefficients produced in clause (iii), so the explicit
-- admissibility hypothesis `StableLevyCoefficients cMinus cPlus` is part of the source meaning.
-- Semantic recall note: `lean_leansearch` timed out on this local API, so this repair follows the
-- in-file clause-(iii)/(v) `StableLevyCoefficients` owner and source note.
/-- Clause (v) of Theorem 16.22, first sentence: for index `α = 1` and admissible coefficients
`c⁻, c⁺` as in clause (iii), i.e. `0 ≤ c⁻`, `0 ≤ c⁺`, and `0 < c⁻ + c⁺`, the centering sequence
is
`dₙ = (c⁺ - c⁻) n log n`. -/
theorem stable_broad_centering_eq_of_index_one
    {μ : ProbabilityMeasure ℝ} {d : ℕ+ → ℝ} {cMinus cPlus : ℝ}
    {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ 1)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) =
        map μ (measurable_affineMap ((n : ℝ) ^ (1 / (1 : ℝ))) (d n)).aemeasurable)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (hcoeff : StableLevyCoefficients cMinus cPlus)
    (hν : τ.ν = stableLevyMeasure 1 cMinus cPlus) :
    ∀ n : ℕ+, d n = (cPlus - cMinus) * (n : ℝ) * Real.log n := by
  intro n
  have hμ_broad : IsStableInBroadSense μ := by
    refine ⟨hμ.1, ?_⟩
    refine ⟨fun m ↦ (m : ℝ) ^ (1 / (1 : ℝ)), d, ?_, hscale⟩
    intro m
    exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (m : ℝ) by exact_mod_cast m.pos) _)
  have ha_nonneg : ∀ m : ℕ+, 0 ≤ (m : ℝ) ^ (1 / (1 : ℝ)) := by
    intro m
    exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (m : ℝ) by exact_mod_cast m.pos) _)
  have hbField :=
    stableBroad_bField_eq hμ_broad hτ ha_nonneg hscale n
  have hn_one_le : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast PNat.one_le n
  have hs_one : 1 ≤ (n : ℝ) ^ (1 / (1 : ℝ)) := by
    simpa using hn_one_le
  have hcorrection :
      ((n : ℝ) ^ (1 / (1 : ℝ))) *
          ∫ x : ℝ,
            ((if |x| < 1 / ((n : ℝ) ^ (1 / (1 : ℝ))) then x else 0) -
                (if |x| < 1 then x else 0))
              ∂τ.ν =
        -(cPlus - cMinus) * ((n : ℝ) ^ (1 / (1 : ℝ))) *
          Real.log ((n : ℝ) ^ (1 / (1 : ℝ))) := by
    rw [hν]
    exact stableLevyCenteringCorrection_eq_of_eq_one hs_one hcoeff.1 hcoeff.2.1
  -- Proof comment: insert the explicit shell-correction formula into the drift comparison and
  -- then simplify the trivial `α = 1` scale.
  rw [hcorrection] at hbField
  have hrpow_one : (n : ℝ) ^ (1 / (1 : ℝ)) = (n : ℝ) := by
    norm_num [Real.rpow_one]
  rw [hrpow_one] at hbField
  linarith

-- Proof comment: the Cauchy conclusion uses the same admissible coefficients from clause (iii).
/-- Helper for Theorem 16.22: shifting the centered Cauchy density by `x₀` produces the Cauchy
density with location parameter `x₀`. -/
private lemma cauchyPDF_centered_sub_right_local (x₀ : ℝ) (γ : ℝ≥0) :
    (fun y : ℝ ↦ cauchyPDF 0 γ (y - x₀)) = cauchyPDF x₀ γ := by
  -- Proof comment: after unfolding the density, both sides are the same rational function in
  -- the translated coordinate `y - x₀`.
  funext y
  rw [cauchyPDF_def, cauchyPDF_def, cauchyPDFReal_def, cauchyPDFReal_def]
  congr 1
  ring_nf

/-- Helper for Theorem 16.22: a volume-preserving measurable equivalence transports `withDensity`
by precomposing the density with the inverse map. -/
private lemma mapWithDensityOfVolumePreserving {α β : Type*}
    [MeasureSpace α] [MeasureSpace β]
    (e : α ≃ᵐ β) (hpres : MeasurePreserving e volume volume)
    (g : α → ENNReal) (hg : Measurable g) :
    Measure.map e (volume.withDensity g) =
      volume.withDensity (fun y : β ↦ g (e.symm y)) := by
  -- Proof comment: compare both measures on measurable sets and move the density through the
  -- volume-preserving equivalence once.
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ hs,
    withDensity_apply _ (e.measurable hs)]
  simpa using hpres.setLIntegral_comp_preimage hs (hg.comp e.symm.measurable)

/-- Helper for Theorem 16.22: translating the centered Cauchy law by `x₀` yields the Cauchy law
with location parameter `x₀`. -/
private lemma map_add_const_centeredCauchyMeasure_local (x₀ a : ℝ) (ha : 0 < a) :
    Measure.map (fun y : ℝ ↦ y + x₀) (cauchyMeasure 0 (Real.toNNReal a)) =
      cauchyMeasure x₀ (Real.toNNReal a) := by
  have hγ : Real.toNNReal a ≠ 0 := (Real.toNNReal_pos.mpr ha).ne'
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight x₀
  have hpres : MeasurePreserving e (volume : Measure ℝ) volume := by
    -- Proof comment: Lebesgue measure is translation invariant.
    refine ⟨e.measurable, ?_⟩
    simpa [e, MeasurableEquiv.addRight] using
      (map_add_right_eq_self (volume : Measure ℝ) x₀)
  rw [cauchyMeasure_of_scale_ne_zero 0 hγ, cauchyMeasure_of_scale_ne_zero x₀ hγ]
  -- Proof comment: transport the centered density through the translation equivalence and then
  -- rewrite the transported density to the shifted Cauchy density.
  calc
    Measure.map (fun y : ℝ ↦ y + x₀) (volume.withDensity (cauchyPDF 0 (Real.toNNReal a))) =
        Measure.map e (volume.withDensity (cauchyPDF 0 (Real.toNNReal a))) := by
          rfl
    _ = volume.withDensity (fun y : ℝ ↦ cauchyPDF 0 (Real.toNNReal a) (e.symm y)) := by
          exact
            mapWithDensityOfVolumePreserving
              (e := e) (hpres := hpres) (g := cauchyPDF 0 (Real.toNNReal a))
              (hg := measurable_cauchyPDF 0 (Real.toNNReal a))
    _ = volume.withDensity (cauchyPDF x₀ (Real.toNNReal a)) := by
          congr 1
          funext y
          simpa [e, MeasurableEquiv.addRight] using
            congrFun (cauchyPDF_centered_sub_right_local x₀ (Real.toNNReal a)) y

/-- Helper for Theorem 16.22: the symmetric index-`1` stable Lévy density is a scalar multiple of
the centered unit-Cauchy Lévy density. -/
private lemma stableLevyDensity_eq_piMul_unitCauchyDensity
    {c : ℝ} (x : ℝ) :
    stableLevyDensity 1 c c x =
      (Real.pi * c) * stableLevyDensity 1 (1 / Real.pi) (1 / Real.pi) x := by
  by_cases hx_neg : x < 0
  · -- Proof comment: both negative-half-line formulas differ only by the scalar factor
    -- `π c * π⁻¹ = c`.
    rw [stableLevyDensity, if_pos hx_neg, stableLevyDensity, if_pos hx_neg]
    calc
      c * (-x) ^ (-(1 : ℝ) - 1)
          = ((Real.pi * c) * (1 / Real.pi)) * (-x) ^ (-(1 : ℝ) - 1) := by
              congr 1
              field_simp [Real.pi_ne_zero]
      _ = (Real.pi * c) * ((1 / Real.pi) * (-x) ^ (-(1 : ℝ) - 1)) := by ring
  · by_cases hx_pos : 0 < x
    · -- Proof comment: the same scalar comparison holds on the positive half-line.
      rw [stableLevyDensity, if_neg hx_neg, if_pos hx_pos, stableLevyDensity, if_neg hx_neg,
        if_pos hx_pos]
      calc
        c * x ^ (-(1 : ℝ) - 1)
            = ((Real.pi * c) * (1 / Real.pi)) * x ^ (-(1 : ℝ) - 1) := by
                congr 1
                field_simp [Real.pi_ne_zero]
        _ = (Real.pi * c) * ((1 / Real.pi) * x ^ (-(1 : ℝ) - 1)) := by ring
    · -- Proof comment: at the origin both densities were defined to vanish.
      have hx_zero : x = 0 := by linarith
      simp [stableLevyDensity, hx_zero]

/-- Helper for Theorem 16.22: the symmetric index-`1` stable Lévy measure is the corresponding
scalar multiple of the centered unit-Cauchy Lévy measure. -/
private lemma stableLevyMeasure_eq_piMul_unitCauchyMeasure
    {c : ℝ} (hc : 0 ≤ c) :
    stableLevyMeasure 1 c c =
      ENNReal.ofReal (Real.pi * c) • stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi) := by
  have hpiMul_nonneg : 0 ≤ Real.pi * c := by positivity
  rw [stableLevyMeasure_def, stableLevyMeasure_def,
    ← withDensity_smul' (ENNReal.ofReal (Real.pi * c))
      (fun x ↦ ENNReal.ofReal (stableLevyDensity 1 (1 / Real.pi) (1 / Real.pi) x)) (by simp)]
  congr 1
  funext x
  rw [Pi.smul_apply, smul_eq_mul, stableLevyDensity_eq_piMul_unitCauchyDensity x,
    ENNReal.ofReal_mul hpiMul_nonneg]

/-- Helper for Theorem 16.22: in the symmetric index-`1` branch, the Lévy--Khintchin exponent is
the translated centered Cauchy exponent with scale `π c`. -/
private lemma levyKhinchinExponent_eq_symmetricIndexOneModel
    {τ : LevyKhinchinTriple} {c : ℝ}
    (hσ : τ.sigma2 = 0) (hν : τ.ν = stableLevyMeasure 1 c c) (hc : 0 ≤ c) (t : ℝ) :
    levyKhinchinExponent τ t =
      (((τ.b * t : ℝ) : ℂ) * Complex.I) + (-((Real.pi * c) * |t|) : ℂ) := by
  have hpiMul_nonneg : 0 ≤ Real.pi * c := by positivity
  have hbaseExp :
      levyKhinchinExponent
          { sigma2 := 0
            b := 0
            ν := stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi) } t =
        (-|t| : ℂ) := by
    -- Proof comment: Example 16.19 already identifies the centered unit-Cauchy exponent.
    simpa using centeredUnitCauchy_targetExponent_eq_negAbs t
  -- Proof comment: rewrite the symmetric Lévy measure as a scalar multiple of the centered
  -- unit-Cauchy model and then pull the scalar through the jump integral.
  rw [levyKhinchinExponent, levyKhinchinExponentWithCentering, hσ]
  simp
  rw [hν, stableLevyMeasure_eq_piMul_unitCauchyMeasure hc, MeasureTheory.integral_smul_measure]
  have hbaseIntegral :
      ∫ x : ℝ,
          (Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
            (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I)) ∂
            stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi) =
        (-|t| : ℂ) := by
    -- Proof comment: in the centered model the whole exponent is already the jump integral.
    simpa [levyKhinchinExponent, levyKhinchinExponentWithCentering, mul_assoc] using hbaseExp
  rw [hbaseIntegral, ENNReal.toReal_ofReal hpiMul_nonneg]
  have hscalar :
      ((Real.pi * c) • ((|t| : ℝ) : ℂ)) = (↑Real.pi * ↑c * ↑|t| : ℂ) := by
    simp [smul_eq_mul, mul_assoc]
  simpa [hscalar]

/-- Clause (v) of Theorem 16.22, second sentence: if `α = 1` and the admissible positive and
negative Lévy-density coefficients from clause (iii) agree, then the law is Cauchy. -/
theorem stable_broad_index_one_symmetric_isCauchy
    {μ : ProbabilityMeasure ℝ} {cMinus cPlus : ℝ}
    {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ 1)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (hcoeff : StableLevyCoefficients cMinus cPlus)
    (hν : τ.ν = stableLevyMeasure 1 cMinus cPlus) (hsymm : cMinus = cPlus) :
    ∃ x₀ : ℝ, ∃ γ : ℝ≥0, 0 < γ ∧ (μ : Measure ℝ) = cauchyMeasure x₀ γ := by
  obtain ⟨d, hscale⟩ := hμ.exists_centering
  have hμ_broad : IsStableInBroadSense μ := by
    refine ⟨hμ.1, ?_⟩
    refine ⟨fun n ↦ (n : ℝ) ^ (1 / (1 : ℝ)), d, ?_, hscale⟩
    intro n
    exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) _)
  have ha_nonneg : ∀ n : ℕ+, 0 ≤ (n : ℝ) ^ (1 / (1 : ℝ)) := by
    intro n
    exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) _)
  have hσScaled :
      ((((2 : ℝ) ^ (1 / (1 : ℝ))) ^ (2 : ℕ)) - (2 : ℝ)) * τ.sigma2 = 0 :=
    stableBroad_canonicalTriple_gaussianScaling hμ_broad hτ ha_nonneg hscale 2
  have hσ : τ.sigma2 = 0 := by
    have htwo := hσScaled
    norm_num at htwo
    linarith
  have hcPlus_nonneg : 0 ≤ cPlus := hcoeff.2.1
  have hcPlus_pos : 0 < cPlus := by
    have hsum_pos : 0 < cPlus + cPlus := by
      simpa [hsymm] using hcoeff.2.2
    linarith
  have hpiMul_pos : 0 < Real.pi * cPlus := by positivity
  have hpiMul_nonneg : 0 ≤ Real.pi * cPlus := le_of_lt hpiMul_pos
  have hγpos : 0 < Real.toNNReal (Real.pi * cPlus) := by
    rw [Real.toNNReal_pos]
    exact hpiMul_pos
  refine ⟨τ.b, Real.toNNReal (Real.pi * cPlus), hγpos, ?_⟩
  apply Measure.ext_of_charFun
  ext t
  have hνsymm : τ.ν = stableLevyMeasure 1 cPlus cPlus := by
    simpa [hsymm] using hν
  have hμExp :
      levyKhinchinExponent τ t =
        (((τ.b * t : ℝ) : ℂ) * Complex.I) + (-((Real.pi * cPlus) * |t|) : ℂ) := by
    -- Proof comment: the symmetric `α = 1` model is exactly a translated centered Cauchy
    -- exponent once the Gaussian term is known to vanish.
    exact levyKhinchinExponent_eq_symmetricIndexOneModel hσ hνsymm hcPlus_nonneg t
  have htargetChar :
      charFun (cauchyMeasure τ.b (Real.toNNReal (Real.pi * cPlus))) t =
        Complex.exp
          ((((τ.b * t : ℝ) : ℂ) * Complex.I) + (-((Real.pi * cPlus) * |t|) : ℂ)) := by
    -- Proof comment: translate the centered Cauchy law of scale `π c⁺`, then combine the phase
    -- and centered factors into one exponential.
    rw [← map_add_const_centeredCauchyMeasure_local τ.b (Real.pi * cPlus) hpiMul_pos]
    rw [MeasureTheory.charFun_map_add_const]
    rw [charFun_centeredCauchyMeasure (Real.pi * cPlus) hpiMul_pos]
    have hinner : inner ℝ τ.b t = τ.b * t := by
      exact realInner_eq_mul _ _
    rw [hinner, ← Complex.exp_add]
    congr 1
    simpa [add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm]
  -- Proof comment: the represented characteristic function is exactly the translated Cauchy
  -- characteristic function with location `τ.b` and scale `π c⁺`.
  rw [hτ.charFun_eq_exp, hμExp, htargetChar]

-- Route correction: the clause proofs were already complete; the remaining failure was that this
-- bundled theorem had been mislabeled as a helper instead of the item-level theorem surface.
/-- Theorem 16.22: package the six clause theorems under one bundled declaration. -/
theorem stable_broad_classification
    {μ : ProbabilityMeasure ℝ} (hμ : IsStableInBroadSense μ) :
    (∃ α : ℝ, IsStableInBroadSenseWithIndex μ α) ∧
      (∀ {α : ℝ}, IsStableInBroadSenseWithIndex μ α → α = 2 →
        IsGaussian (μ : Measure ℝ)) ∧
      (∀ {α : ℝ} {τ : LevyKhinchinTriple}, IsStableInBroadSenseWithIndex μ α →
        α ∈ Set.Ioo (0 : ℝ) 2 → HasLevyKhinchinRepresentation μ τ →
          ∃ cMinus cPlus : ℝ,
            StableLevyCoefficients cMinus cPlus ∧
              τ.ν = stableLevyMeasure α cMinus cPlus) ∧
      (∀ {α : ℝ}, IsStableInBroadSenseWithIndex μ α → α ≠ 1 →
        ∃ b : ℝ, IsStableWithIndex (map μ (measurable_affineMap 1 (-b)).aemeasurable) α) ∧
      (∀ {d : ℕ+ → ℝ} {cMinus cPlus : ℝ} {τ : LevyKhinchinTriple},
        IsStableInBroadSenseWithIndex μ 1 →
          (∀ n : ℕ+,
            μ ^ (n : ℕ) =
              map μ (measurable_affineMap ((n : ℝ) ^ (1 / (1 : ℝ))) (d n)).aemeasurable) →
          HasLevyKhinchinRepresentation μ τ →
          StableLevyCoefficients cMinus cPlus →
          τ.ν = stableLevyMeasure 1 cMinus cPlus →
          ∀ n : ℕ+, d n = (cPlus - cMinus) * (n : ℝ) * Real.log n) ∧
      (∀ {cMinus cPlus : ℝ} {τ : LevyKhinchinTriple},
        IsStableInBroadSenseWithIndex μ 1 →
          HasLevyKhinchinRepresentation μ τ →
          StableLevyCoefficients cMinus cPlus →
          τ.ν = stableLevyMeasure 1 cMinus cPlus →
          cMinus = cPlus →
          ∃ x₀ : ℝ, ∃ γ : ℝ≥0, 0 < γ ∧ (μ : Measure ℝ) = cauchyMeasure x₀ γ) := by
  constructor
  · exact stable_broad_exists_index hμ
  constructor
  · intro α hα hα_two
    subst hα_two
    exact stable_broad_index_two_isGaussian hα
  constructor
  · intro α τ hα hα_mem hτ
    exact stable_broad_levyMeasure_eq_stableLevyMeasure hα hα_mem.2 hτ
  constructor
  · intro α hα hα_ne
    exact stable_broad_translate_isStable_of_ne_one hα hα_ne
  constructor
  · intro d cMinus cPlus τ hα hscale hτ hcoeff hν
    exact stable_broad_centering_eq_of_index_one hα hscale hτ hcoeff hν
  · intro cMinus cPlus τ hα hτ hcoeff hν hsymm
    exact stable_broad_index_one_symmetric_isCauchy hα hτ hcoeff hν hsymm

end MeasureTheory.ProbabilityMeasure
