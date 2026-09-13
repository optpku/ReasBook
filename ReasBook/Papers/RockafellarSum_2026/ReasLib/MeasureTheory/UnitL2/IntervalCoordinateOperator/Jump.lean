/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Pointwise

/-!
# Interval-coordinate jump remainders

This module defines the filtered series used to isolate finite-support jumps of
the interval-coordinate representative.
-/

noncomputable section

namespace L1Seq

/-- The contribution to a pointwise representative jump from coefficients outside
a finite set whose rational times lie in a given half-open interval. -/
public noncomputable def jumpRemainder (a : L1Seq) (J : Finset ℕ)
    (sLeft sRight : ℝ) : ℝ :=
  ∑' n : ℕ,
    if n ∉ J ∧ rationalTime n ∈ Set.Ioc sLeft sRight then a n else 0

/-- Evaluation of the jump remainder is its defining filtered series. -/
public theorem jumpRemainder_apply (a : L1Seq) (J : Finset ℕ) (sLeft sRight : ℝ) :
    jumpRemainder a J sLeft sRight =
      ∑' n : ℕ,
        if n ∉ J ∧ rationalTime n ∈ Set.Ioc sLeft sRight then a n else 0 := by
  -- The displayed filtered series is exactly the defining body of the remainder.
  rfl

/-- If a finite set isolates one rational breakpoint in a half-open interval, the
difference of the pointwise representative at the endpoints is the corresponding
coefficient plus the jump remainder. -/
public theorem pointwiseRepresentative_sub_eq_apply_add_jumpRemainder
    (a : L1Seq) (n₀ : ℕ) (J : Finset ℕ) (sLeft sRight : ℝ) (hn₀ : n₀ ∈ J)
    (hLeft : sLeft ∈ Set.Ioo (0 : ℝ) (rationalTime n₀))
    (hRight : sRight ∈ Set.Ioo (rationalTime n₀) 1)
    (hAvoid : ∀ n ∈ J, n ≠ n₀ → rationalTime n ∉ Set.Ioc sLeft sRight) :
    pointwiseRepresentative a sLeft - pointwiseRepresentative a sRight =
      a n₀ + jumpRemainder a J sLeft sRight := by
  classical
  -- Absolute convergence permits subtraction of the two endpoint series term by term.
  have hSummableLeft : Summable (fun n : ℕ ↦
      a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) sLeft) :=
    (summable_abs_pointwiseRepresentative a sLeft).of_abs
  have hSummableRight : Summable (fun n : ℕ ↦
      a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) sRight) :=
    (summable_abs_pointwiseRepresentative a sRight).of_abs
  have hEndpointOrder : sLeft < sRight := hLeft.2.trans hRight.1
  have hRightPositive : 0 < sRight :=
    (rationalTime_mem_Ioo n₀).1.trans hRight.1
  -- Each term changes precisely when its rational breakpoint lies in `(sLeft, sRight]`.
  have hTermDifference (n : ℕ) :
      a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) sLeft -
          a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) sRight =
        if rationalTime n ∈ Set.Ioc sLeft sRight then a n else 0 := by
    by_cases hnInterval : rationalTime n ∈ Set.Ioc sLeft sRight
    · have hLeftMem : sLeft ∈ Set.Ioo (0 : ℝ) (rationalTime n) := by
        constructor
        · exact hLeft.1
        · exact hnInterval.1
      have hRightNotMem : sRight ∉ Set.Ioo (0 : ℝ) (rationalTime n) := by
        intro hRightMem
        exact (not_lt_of_ge hnInterval.2) hRightMem.2
      simp only [Set.indicator_of_mem hLeftMem, Set.indicator_of_notMem hRightNotMem,
        mul_one, mul_zero, sub_zero, if_pos hnInterval]
    · by_cases hLeftLt : sLeft < rationalTime n
      · have hLeftMem : sLeft ∈ Set.Ioo (0 : ℝ) (rationalTime n) := by
          constructor
          · exact hLeft.1
          · exact hLeftLt
        have hRightLt : sRight < rationalTime n := by
          apply lt_of_not_ge
          intro hnLe
          exact hnInterval ⟨hLeftLt, hnLe⟩
        have hRightMem : sRight ∈ Set.Ioo (0 : ℝ) (rationalTime n) := by
          constructor
          · exact hRightPositive
          · exact hRightLt
        simp only [Set.indicator_of_mem hLeftMem, Set.indicator_of_mem hRightMem,
          mul_one, sub_self, if_neg hnInterval]
      · have hLeftNotMem : sLeft ∉ Set.Ioo (0 : ℝ) (rationalTime n) := by
          intro hLeftMem
          exact hLeftLt hLeftMem.2
        have hRightNotMem : sRight ∉ Set.Ioo (0 : ℝ) (rationalTime n) := by
          intro hRightMem
          exact hLeftLt (hEndpointOrder.trans hRightMem.2)
        simp only [Set.indicator_of_notMem hLeftNotMem,
          Set.indicator_of_notMem hRightNotMem, mul_zero, sub_self, if_neg hnInterval]
  have hDifferenceSummable : Summable (fun n : ℕ ↦
      a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) sLeft -
        a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator
          (fun _ ↦ (1 : ℝ)) sRight) :=
    hSummableLeft.sub hSummableRight
  have hIntervalSummable : Summable (fun n : ℕ ↦
      if rationalTime n ∈ Set.Ioc sLeft sRight then a n else 0) :=
    hDifferenceSummable.congr hTermDifference
  -- The isolated breakpoint contributes exactly `a n₀`.
  have hn₀Interval : rationalTime n₀ ∈ Set.Ioc sLeft sRight := by
    constructor
    · exact hLeft.2
    · exact hRight.1.le
  -- Away from `n₀`, the isolation hypothesis removes every index of `J`.
  have hRemainingTerms (n : ℕ) :
      (if n = n₀ then 0
        else if rationalTime n ∈ Set.Ioc sLeft sRight then a n else 0) =
      if n ∉ J ∧ rationalTime n ∈ Set.Ioc sLeft sRight then a n else 0 := by
    by_cases hnEq : n = n₀
    · subst n
      simp only [ite_true, hn₀, not_true_eq_false, false_and, if_false]
    · by_cases hnJ : n ∈ J
      · have hnOutside := hAvoid n hnJ hnEq
        simp only [if_neg hnEq, hnJ, not_true_eq_false, false_and, hnOutside, if_false]
      · simp only [if_neg hnEq, hnJ, not_false_eq_true, true_and]
  -- Split off `n₀`, then identify all remaining terms with the defined remainder.
  calc
    pointwiseRepresentative a sLeft - pointwiseRepresentative a sRight =
        ∑' n : ℕ,
          (a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator
              (fun _ ↦ (1 : ℝ)) sLeft -
            a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator
              (fun _ ↦ (1 : ℝ)) sRight) := by
      rw [pointwiseRepresentative_apply, pointwiseRepresentative_apply]
      exact (hSummableLeft.tsum_sub hSummableRight).symm
    _ = ∑' n : ℕ,
        if rationalTime n ∈ Set.Ioc sLeft sRight then a n else 0 :=
      tsum_congr hTermDifference
    _ = (if rationalTime n₀ ∈ Set.Ioc sLeft sRight then a n₀ else 0) +
        ∑' n : ℕ, if n = n₀ then 0
          else if rationalTime n ∈ Set.Ioc sLeft sRight then a n else 0 :=
      hIntervalSummable.tsum_eq_add_tsum_ite n₀
    _ = a n₀ + ∑' n : ℕ, if n = n₀ then 0
          else if rationalTime n ∈ Set.Ioc sLeft sRight then a n else 0 := by
      rw [if_pos hn₀Interval]
    _ = a n₀ + ∑' n : ℕ,
        if n ∉ J ∧ rationalTime n ∈ Set.Ioc sLeft sRight then a n else 0 := by
      exact congrArg (a n₀ + ·) (tsum_congr hRemainingTerms)
    _ = a n₀ + jumpRemainder a J sLeft sRight := by
      rw [jumpRemainder_apply]

/-- The absolute value of a jump remainder is strictly bounded by any strict bound
for the absolute coefficient sum outside the chosen finite set. -/
public theorem abs_jumpRemainder_lt (a : L1Seq) (J : Finset ℕ)
    (sLeft sRight ε : ℝ)
    (hTail : (∑' n : {n // n ∉ J}, |a n|) < ε) :
    |jumpRemainder a J sLeft sRight| < ε := by
  classical
  -- The coordinatewise absolute values form the summable majorant for every filter used below.
  have hOne : 0 < (1 : ENNReal).toReal := by
    norm_num
  have hAbs : Summable (fun n : ℕ ↦ |a n|) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      a.2.summable hOne
  have hTailSummable : Summable (fun n : {n // n ∉ J} ↦ |a n|) :=
    hAbs.subtype {n : ℕ | n ∉ J}
  have hFilteredTailSummable : Summable (fun n : {n // n ∉ J} ↦
      if rationalTime n ∈ Set.Ioc sLeft sRight then |a n| else 0) := by
    have hIndicator := hTailSummable.indicator
      {n : {n // n ∉ J} | rationalTime n ∈ Set.Ioc sLeft sRight}
    apply hIndicator.congr
    intro n
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hRemainderNormSummable : Summable (fun n : ℕ ↦
      ‖if n ∉ J ∧ rationalTime n ∈ Set.Ioc sLeft sRight then a n else 0‖) := by
    have hIndicator := hAbs.indicator
      {n : ℕ | n ∉ J ∧ rationalTime n ∈ Set.Ioc sLeft sRight}
    apply hIndicator.congr
    intro n
    by_cases hn : n ∉ J ∧ rationalTime n ∈ Set.Ioc sLeft sRight
    · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_pos hn,
        Real.norm_eq_abs]
    · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_neg hn, norm_zero]
  -- Reindexing by the complement subtype exposes exactly the tail appearing in `hTail`.
  have hFilteredSumEqSubtype :
      (∑' n : ℕ,
          if n ∉ J ∧ rationalTime n ∈ Set.Ioc sLeft sRight then |a n| else 0) =
        ∑' n : {n // n ∉ J},
          if rationalTime n ∈ Set.Ioc sLeft sRight then |a n| else 0 := by
    calc
      (∑' n : ℕ,
          if n ∉ J ∧ rationalTime n ∈ Set.Ioc sLeft sRight then |a n| else 0) =
          ∑' n : ℕ, Set.indicator {n : ℕ | n ∉ J}
            (fun n ↦ if rationalTime n ∈ Set.Ioc sLeft sRight then |a n| else 0) n := by
        apply tsum_congr
        intro n
        by_cases hnJ : n ∈ J
        · have hnNotComplement : n ∉ {m : ℕ | m ∉ J} := by
            intro hnComplement
            exact hnComplement hnJ
          simp only [hnJ, not_true_eq_false, false_and, if_false,
            Set.indicator_of_notMem hnNotComplement]
        · have hnComplement : n ∈ {n : ℕ | n ∉ J} := hnJ
          simp only [hnJ, not_false_eq_true, true_and,
            Set.indicator_of_mem hnComplement]
      _ = ∑' n : {n // n ∉ J},
          if rationalTime n ∈ Set.Ioc sLeft sRight then |a n| else 0 :=
        (tsum_subtype {n : ℕ | n ∉ J}
          (fun n ↦ if rationalTime n ∈ Set.Ioc sLeft sRight then |a n| else 0)).symm
  have hFilteredTailLe :
      (∑' n : {n // n ∉ J},
          if rationalTime n ∈ Set.Ioc sLeft sRight then |a n| else 0) ≤
        ∑' n : {n // n ∉ J}, |a n| := by
    apply hFilteredTailSummable.tsum_le_tsum
    · intro n
      by_cases hnInterval : rationalTime n ∈ Set.Ioc sLeft sRight
      · simp only [if_pos hnInterval, le_refl]
      · simp only [if_neg hnInterval, abs_nonneg]
    · exact hTailSummable
  -- The norm of the remainder is bounded by its absolute filtered series and hence by the tail.
  calc
    |jumpRemainder a J sLeft sRight| =
        ‖∑' n : ℕ,
          if n ∉ J ∧ rationalTime n ∈ Set.Ioc sLeft sRight then a n else 0‖ := by
      simp only [jumpRemainder_apply, Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ,
        ‖if n ∉ J ∧ rationalTime n ∈ Set.Ioc sLeft sRight then a n else 0‖ :=
      norm_tsum_le_tsum_norm hRemainderNormSummable
    _ = ∑' n : ℕ,
        if n ∉ J ∧ rationalTime n ∈ Set.Ioc sLeft sRight then |a n| else 0 := by
      apply tsum_congr
      intro n
      by_cases hn : n ∉ J ∧ rationalTime n ∈ Set.Ioc sLeft sRight
      · simp only [if_pos hn, Real.norm_eq_abs]
      · simp only [if_neg hn, norm_zero]
    _ = ∑' n : {n // n ∉ J},
        if rationalTime n ∈ Set.Ioc sLeft sRight then |a n| else 0 :=
      hFilteredSumEqSubtype
    _ ≤ ∑' n : {n // n ∉ J}, |a n| := hFilteredTailLe
    _ < ε := hTail

/-- If the pointwise representative vanishes at both endpoints of an interval that
isolates one rational breakpoint, the corresponding coefficient is strictly
bounded by any strict bound for the absolute coefficient sum outside the chosen
finite set. -/
public theorem abs_apply_lt_of_pointwiseRepresentative_eq_zero
    (a : L1Seq) (n₀ : ℕ) (J : Finset ℕ) (sLeft sRight ε : ℝ) (hn₀ : n₀ ∈ J)
    (hLeft : sLeft ∈ Set.Ioo (0 : ℝ) (rationalTime n₀))
    (hRight : sRight ∈ Set.Ioo (rationalTime n₀) 1)
    (hAvoid : ∀ n ∈ J, n ≠ n₀ → rationalTime n ∉ Set.Ioc sLeft sRight)
    (hTail : (∑' n : {n // n ∉ J}, |a n|) < ε)
    (hZeroLeft : pointwiseRepresentative a sLeft = 0)
    (hZeroRight : pointwiseRepresentative a sRight = 0) :
    |a n₀| < ε := by
  -- The jump identity and endpoint vanishing identify the coefficient with the negative remainder.
  have hJump := pointwiseRepresentative_sub_eq_apply_add_jumpRemainder
    a n₀ J sLeft sRight hn₀ hLeft hRight hAvoid
  rw [hZeroLeft, hZeroRight, sub_self] at hJump
  have hCoefficient : a n₀ = -jumpRemainder a J sLeft sRight := by
    linarith
  -- Taking absolute values removes the sign, so the remainder estimate closes the claim.
  rw [hCoefficient, abs_neg]
  exact abs_jumpRemainder_lt a J sLeft sRight ε hTail

end L1Seq
