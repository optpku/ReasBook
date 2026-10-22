/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] {A B : Set Ω}

private theorem one_sub_one_div_fifty_eq_forty_nine_div_fifty :
    (1 : ENNReal) - (1 : ENNReal) / 50 = (49 : ENNReal) / 50 := by
  rw [show ((1 : ENNReal) / 50) = (((1 : NNReal) / 50 : NNReal) : ENNReal) by simp]
  rw [show ((49 : ENNReal) / 50) = (((49 : NNReal) / 50 : NNReal) : ENNReal) by simp]
  exact_mod_cast
    (show (1 : NNReal) - (1 : NNReal) / 50 = (49 : NNReal) / 50 by
      apply NNReal.coe_inj.mp
      have h : (1 : NNReal) / 50 ≤ 1 := by
        exact_mod_cast (show (1 : ℝ) / 50 ≤ 1 by norm_num)
      rw [NNReal.coe_sub h]
      norm_num)

private theorem one_sub_nineteen_div_twenty_eq_one_div_twenty :
    (1 : ENNReal) - (19 : ENNReal) / 20 = (1 : ENNReal) / 20 := by
  rw [show ((19 : ENNReal) / 20) = (((19 : NNReal) / 20 : NNReal) : ENNReal) by simp]
  rw [show ((1 : ENNReal) / 20) = (((1 : NNReal) / 20 : NNReal) : ENNReal) by simp]
  exact_mod_cast
    (show (1 : NNReal) - (19 : NNReal) / 20 = (1 : NNReal) / 20 by
      apply NNReal.coe_inj.mp
      have h : (19 : NNReal) / 20 ≤ 1 := by
        exact_mod_cast (show (19 : ℝ) / 20 ≤ 1 by norm_num)
      rw [NNReal.coe_sub h]
      norm_num)

private theorem one_sub_one_div_ten_eq_nine_div_ten :
    (1 : ENNReal) - (1 : ENNReal) / 10 = (9 : ENNReal) / 10 := by
  rw [show ((1 : ENNReal) / 10) = (((1 : NNReal) / 10 : NNReal) : ENNReal) by simp]
  rw [show ((9 : ENNReal) / 10) = (((9 : NNReal) / 10 : NNReal) : ENNReal) by simp]
  exact_mod_cast
    (show (1 : NNReal) - (1 : NNReal) / 10 = (9 : NNReal) / 10 by
      apply NNReal.coe_inj.mp
      have h : (1 : NNReal) / 10 ≤ 1 := by
        exact_mod_cast (show (1 : ℝ) / 10 ≤ 1 by norm_num)
      rw [NNReal.coe_sub h]
      norm_num)

private theorem nineteen_div_twenty_mul_one_div_fifty_add_one_div_ten_mul_forty_nine_div_fifty :
    (19 : ENNReal) / 20 * ((1 : ENNReal) / 50) + (1 : ENNReal) / 10 * ((49 : ENNReal) / 50) =
      (117 : ENNReal) / 1000 := by
  rw [show ((19 : ENNReal) / 20) = (((19 : NNReal) / 20 : NNReal) : ENNReal) by simp]
  rw [show ((1 : ENNReal) / 50) = (((1 : NNReal) / 50 : NNReal) : ENNReal) by simp]
  rw [show ((1 : ENNReal) / 10) = (((1 : NNReal) / 10 : NNReal) : ENNReal) by simp]
  rw [show ((49 : ENNReal) / 50) = (((49 : NNReal) / 50 : NNReal) : ENNReal) by simp]
  rw [show ((117 : ENNReal) / 1000) = (((117 : NNReal) / 1000 : NNReal) : ENNReal) by simp]
  exact_mod_cast
    (show
      (19 : NNReal) / 20 * ((1 : NNReal) / 50) + (1 : NNReal) / 10 * ((49 : NNReal) / 50) =
        (117 : NNReal) / 1000 by
      apply NNReal.coe_inj.mp
      norm_num)

private theorem one_div_twenty_mul_one_div_fifty_add_nine_div_ten_mul_forty_nine_div_fifty :
    (1 : ENNReal) / 20 * ((1 : ENNReal) / 50) + (9 : ENNReal) / 10 * ((49 : ENNReal) / 50) =
      (883 : ENNReal) / 1000 := by
  rw [show ((1 : ENNReal) / 20) = (((1 : NNReal) / 20 : NNReal) : ENNReal) by simp]
  rw [show ((1 : ENNReal) / 50) = (((1 : NNReal) / 50 : NNReal) : ENNReal) by simp]
  rw [show ((9 : ENNReal) / 10) = (((9 : NNReal) / 10 : NNReal) : ENNReal) by simp]
  rw [show ((49 : ENNReal) / 50) = (((49 : NNReal) / 50 : NNReal) : ENNReal) by simp]
  rw [show ((883 : ENNReal) / 1000) = (((883 : NNReal) / 1000 : NNReal) : ENNReal) by simp]
  exact_mod_cast
    (show
      (1 : NNReal) / 20 * ((1 : NNReal) / 50) + (9 : NNReal) / 10 * ((49 : NNReal) / 50) =
        (883 : NNReal) / 1000 by
      apply NNReal.coe_inj.mp
      norm_num)

private theorem one_hundred_seventeen_div_one_thousand_inv_mul_nineteen_div_twenty_mul_one_div_fifty :
    ((117 : ENNReal) / 1000)⁻¹ * ((19 : ENNReal) / 20) * ((1 : ENNReal) / 50) =
      (19 : ENNReal) / 117 := by
  rw [show ((117 : ENNReal) / 1000) = (((117 : NNReal) / 1000 : NNReal) : ENNReal) by simp]
  rw [show ((19 : ENNReal) / 20) = (((19 : NNReal) / 20 : NNReal) : ENNReal) by simp]
  rw [show ((1 : ENNReal) / 50) = (((1 : NNReal) / 50 : NNReal) : ENNReal) by simp]
  rw [show ((19 : ENNReal) / 117) = (((19 : NNReal) / 117 : NNReal) : ENNReal) by simp]
  rw [show ((((117 : NNReal) / 1000 : NNReal) : ENNReal)⁻¹) =
      ((((117 : NNReal) / 1000 : NNReal)⁻¹ : NNReal) : ENNReal) by
      simpa using (ENNReal.coe_inv (by norm_num : ((117 : NNReal) / 1000 : NNReal) ≠ 0)).symm]
  exact_mod_cast
    (show ((117 : NNReal) / 1000)⁻¹ * ((19 : NNReal) / 20) * ((1 : NNReal) / 50) =
        (19 : NNReal) / 117 by
      apply NNReal.coe_inj.mp
      norm_num)

private theorem eight_hundred_eighty_three_div_one_thousand_inv_mul_one_div_twenty_mul_one_div_fifty :
    ((883 : ENNReal) / 1000)⁻¹ * ((1 : ENNReal) / 20) * ((1 : ENNReal) / 50) =
      (1 : ENNReal) / 883 := by
  rw [show ((883 : ENNReal) / 1000) = (((883 : NNReal) / 1000 : NNReal) : ENNReal) by simp]
  rw [show ((1 : ENNReal) / 20) = (((1 : NNReal) / 20 : NNReal) : ENNReal) by simp]
  rw [show ((1 : ENNReal) / 50) = (((1 : NNReal) / 50 : NNReal) : ENNReal) by simp]
  rw [show ((1 : ENNReal) / 883) = (((1 : NNReal) / 883 : NNReal) : ENNReal) by simp]
  rw [show ((((883 : NNReal) / 1000 : NNReal) : ENNReal)⁻¹) =
      ((((883 : NNReal) / 1000 : NNReal)⁻¹ : NNReal) : ENNReal) by
      simpa using (ENNReal.coe_inv (by norm_num : ((883 : NNReal) / 1000 : NNReal) ≠ 0)).symm]
  exact_mod_cast
    (show ((883 : NNReal) / 1000)⁻¹ * ((1 : NNReal) / 20) * ((1 : NNReal) / 50) =
        (1 : NNReal) / 883 by
      apply NNReal.coe_inj.mp
      norm_num)

private theorem defective_compl_prob_eq_forty_nine_div_fifty
    (hB : MeasurableSet B) (hB_prob : P B = (1 : ENNReal) / 50) :
    P Bᶜ = (49 : ENNReal) / 50 := by
  rw [measure_compl hB (measure_ne_top P B), measure_univ, hB_prob]
  exact one_sub_one_div_fifty_eq_forty_nine_div_fifty

private theorem alarm_prob_eq_one_hundred_seventeen_div_one_thousand
    (hB : MeasurableSet B) (hB_prob : P B = (1 : ENNReal) / 50)
    (h_alarm_if_defective : P[A | B] = (19 : ENNReal) / 20)
    (h_false_alarm : P[A | Bᶜ] = (1 : ENNReal) / 10) :
    P A = (117 : ENNReal) / 1000 := by
  rw [← cond_add_cond_compl_eq hB P, h_alarm_if_defective, h_false_alarm, hB_prob,
    defective_compl_prob_eq_forty_nine_div_fifty P hB hB_prob]
  exact nineteen_div_twenty_mul_one_div_fifty_add_one_div_ten_mul_forty_nine_div_fifty

private theorem cond_compl_eq_one_sub_cond
    {C : Set Ω} (hA : MeasurableSet A) (hC_nonzero : P C ≠ 0) :
    P[Aᶜ | C] = 1 - P[A | C] := by
  let _ : IsProbabilityMeasure P[|C] := cond_isProbabilityMeasure hC_nonzero
  change P[|C] Aᶜ = 1 - P[|C] A
  rw [measure_compl hA (measure_ne_top P[|C] A), measure_univ]

private theorem no_alarm_given_defective_eq_one_div_twenty
    (hA : MeasurableSet A) (hB_prob : P B = (1 : ENNReal) / 50)
    (h_alarm_if_defective : P[A | B] = (19 : ENNReal) / 20) :
    P[Aᶜ | B] = (1 : ENNReal) / 20 := by
  have hB_nonzero : P B ≠ 0 := by
    rw [hB_prob]
    norm_num
  rw [cond_compl_eq_one_sub_cond P hA hB_nonzero, h_alarm_if_defective]
  exact one_sub_nineteen_div_twenty_eq_one_div_twenty

private theorem no_alarm_given_not_defective_eq_nine_div_ten
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hB_prob : P B = (1 : ENNReal) / 50)
    (h_false_alarm : P[A | Bᶜ] = (1 : ENNReal) / 10) :
    P[Aᶜ | Bᶜ] = (9 : ENNReal) / 10 := by
  have hB_compl_nonzero : P Bᶜ ≠ 0 := by
    rw [defective_compl_prob_eq_forty_nine_div_fifty P hB hB_prob]
    norm_num
  rw [cond_compl_eq_one_sub_cond P hA hB_compl_nonzero, h_false_alarm]
  exact one_sub_one_div_ten_eq_nine_div_ten

private theorem no_alarm_prob_eq_eight_hundred_eighty_three_div_one_thousand
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hB_prob : P B = (1 : ENNReal) / 50)
    (h_alarm_if_defective : P[A | B] = (19 : ENNReal) / 20)
    (h_false_alarm : P[A | Bᶜ] = (1 : ENNReal) / 10) :
    P Aᶜ = (883 : ENNReal) / 1000 := by
  rw [← cond_add_cond_compl_eq hB P, no_alarm_given_defective_eq_one_div_twenty P hA
      hB_prob h_alarm_if_defective, no_alarm_given_not_defective_eq_nine_div_ten P hA hB hB_prob
      h_false_alarm, hB_prob, defective_compl_prob_eq_forty_nine_div_fifty P hB hB_prob]
  exact one_div_twenty_mul_one_div_fifty_add_nine_div_ten_mul_forty_nine_div_fifty

-- Proof sketch: compute `P A` from the law of total probability
-- `cond_add_cond_compl_eq` applied to the event `A`, obtaining
-- `P A = (19 / 20) * (1 / 50) + (1 / 10) * (49 / 50) = 117 / 1000`. Then apply Bayes' formula
-- `cond_eq_inv_mul_cond_mul` to rewrite `P[B | A]` as `(P A)⁻¹ * P[A | B] * P B` and simplify.
/-- Example 8.8: In the quality-control setup where `A` is the event that the test gives an alarm
and `B` is the event that the device is defective, if `P B = 1 / 50`, `P[A | B] = 19 / 20`, and
`P[A | Bᶜ] = 1 / 10`, then the posterior defect probability after an alarm is `19 / 117`. -/
theorem defective_given_alarm_eq_nineteen_over_hundred_seventeen
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hB_prob : P B = (1 : ENNReal) / 50)
    (h_alarm_if_defective : P[A | B] = (19 : ENNReal) / 20)
    (h_false_alarm : P[A | Bᶜ] = (1 : ENNReal) / 10) :
    P[B | A] = (19 : ENNReal) / 117 := by
  rw [cond_eq_inv_mul_cond_mul hA hB P, alarm_prob_eq_one_hundred_seventeen_div_one_thousand P hB
      hB_prob h_alarm_if_defective h_false_alarm, h_alarm_if_defective, hB_prob]
  exact one_hundred_seventeen_div_one_thousand_inv_mul_nineteen_div_twenty_mul_one_div_fifty

-- Proof sketch: first rewrite the complementary conditional probabilities using
-- the fact that the conditioned measures `P[|B]` and `P[|Bᶜ]` are probability measures, so that
-- `P[Aᶜ | B] = 1 / 20` and `P[Aᶜ | Bᶜ] = 9 / 10`. Compute
-- `P Aᶜ = (1 / 20) * (1 / 50) + (9 / 10) * (49 / 50) = 883 / 1000`, then apply Bayes' formula to
-- `P[B | Aᶜ]` and simplify to `1 / 883`.
/-- In the same quality-control setup, the posterior defect probability after no alarm is
`1 / 883`. -/
theorem defective_given_no_alarm_eq_one_over_eight_hundred_eighty_three
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hB_prob : P B = (1 : ENNReal) / 50)
    (h_alarm_if_defective : P[A | B] = (19 : ENNReal) / 20)
    (h_false_alarm : P[A | Bᶜ] = (1 : ENNReal) / 10) :
    P[B | Aᶜ] = (1 : ENNReal) / 883 := by
  rw [cond_eq_inv_mul_cond_mul hA.compl hB P,
    no_alarm_prob_eq_eight_hundred_eighty_three_div_one_thousand P hA hB hB_prob
      h_alarm_if_defective h_false_alarm,
    no_alarm_given_defective_eq_one_div_twenty P hA hB_prob h_alarm_if_defective, hB_prob]
  exact eight_hundred_eighty_three_div_one_thousand_inv_mul_one_div_twenty_mul_one_div_fifty
