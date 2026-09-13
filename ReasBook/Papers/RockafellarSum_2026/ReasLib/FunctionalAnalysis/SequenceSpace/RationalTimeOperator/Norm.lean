/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator

/-!
# Sharp triangular-operator bound

The diagonal and strict upper tail occupy disjoint coordinates. Counting their
mass jointly improves the previously available bound from three to two.
-/

public section

namespace L1Seq

/-- The diagonal mass and strict upper tail together are bounded by the full
absolute sum. -/
theorem abs_add_strictTail_le_norm (a : L1Seq) (n : ℕ) :
    |a n| + (∑' m : ℕ, if n < m then |a m| else 0) ≤ ‖a‖ := by
  have hone : 0 < (1 : ENNReal).toReal := by norm_num
  have ha : Summable (fun m : ℕ ↦ |a m|) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      (lp.hasSum_norm hone a).summable
  have ht : Summable (fun m : ℕ ↦ if n < m then |a m| else 0) :=
    ha.summable_of_eq_zero_or_self fun m ↦ by
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  have hc : Summable (fun m : ℕ ↦ if m = n then 0 else |a m|) :=
    ha.summable_of_eq_zero_or_self fun m ↦ by
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
  have htail : (∑' m : ℕ, if n < m then |a m| else 0) ≤
      ∑' m : ℕ, if m = n then 0 else |a m| := by
    apply Summable.tsum_le_tsum _ ht hc
    intro m
    by_cases hmn : m = n
    · subst m
      simp
    · simp only [if_neg hmn]
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _
  rw [norm_eq_tsum_abs, ha.tsum_eq_add_tsum_ite n]
  exact add_le_add le_rfl htail

/-- The triangular rational-time operator has pointwise norm bound two. -/
theorem norm_positiveOperator_apply_le_two (a : L1Seq) :
    ‖positiveOperator a‖ ≤ 2 * ‖a‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (by norm_num) (norm_nonneg a))).2
  intro n
  have hcoord := abs_positiveOperator_apply_le a n
  have hmass := abs_add_strictTail_le_norm a n
  have hbound : |positiveOperator a n| ≤ 2 * ‖a‖ := by
    linarith [abs_nonneg (a n)]
  simpa only [ZeroAtInftyContinuousMap.toBCF_apply, Real.norm_eq_abs] using hbound

/-- The operator norm of the triangular rational-time operator is at most two. -/
theorem norm_positiveOperator_le_two : ‖positiveOperator‖ ≤ 2 := by
  exact positiveOperator.opNorm_le_bound (by norm_num) norm_positiveOperator_apply_le_two

end L1Seq
