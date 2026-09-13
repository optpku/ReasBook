/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.Analysis.Sequence.L1
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0
public import RockafellarSum_2026.ReasLib.Order.RationalTime

/-!
# Rational-time positive operator

This module defines the interval-coordinate positive operator on `L1Seq` and
its coordinate, norm, and pairing identities.
-/

public section

noncomputable section

open Filter Topology

namespace L1Seq

/-- The coordinate function underlying the positive operator. -/
private noncomputable def positiveOperatorCoord (a : L1Seq) (n : ℕ) : ℝ :=
  rationalTime n * a n +
    2 * ∑' m : ℕ, if n < m then min (rationalTime n) (rationalTime m) * a m else 0

/-- A strict upper tail is the sum over the complement of the corresponding finite prefix. -/
private theorem tsum_strictUpper_eq_compl (f : ℕ → ℝ) (n : ℕ) :
    (∑' m : ℕ, if n < m then f m else 0) =
      ∑' m : {m : ℕ // m ∈ (↑(Finset.range (n + 1)) : Set ℕ)ᶜ}, f m := by
  -- Rewrite the subtype sum as an indicator and identify its membership condition.
  simpa only [Set.indicator, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range,
    Nat.not_lt, Nat.succ_le_iff] using
    (tsum_subtype ((↑(Finset.range (n + 1)) : Set ℕ)ᶜ) f).symm

/-- The sum of a coordinate's absolute value and twice its strict upper absolute tail
tends to zero. -/
theorem positiveOperatorCoordBound_tendsto (a : L1Seq) :
    Filter.Tendsto
      (fun n : ℕ ↦ |a n| + 2 * ∑' m : ℕ, if n < m then |a m| else 0)
      Filter.atTop (nhds 0) := by
  -- Regard the strict upper tail as the complement of the prefix through `n`.
  have hComplement :
      Tendsto
        (fun n : ℕ ↦
          ∑' m : {m : ℕ // m ∈ (↑(Finset.range (n + 1)) : Set ℕ)ᶜ}, |a m|)
        atTop (𝓝 0) :=
    (tendsto_tsum_compl_atTop_zero (fun m : ℕ ↦ |a m|)).comp
      (Filter.tendsto_finset_range.comp (tendsto_add_atTop_nat 1))
  have hTail :
      Tendsto (fun n : ℕ ↦ ∑' m : ℕ, if n < m then |a m| else 0) atTop (𝓝 0) := by
    exact hComplement.congr'
      (Eventually.of_forall fun n ↦ (tsum_strictUpper_eq_compl (fun m ↦ |a m|) n).symm)
  -- Absolute summability also forces the individual coordinates to vanish.
  have hOne : 0 < (1 : ENNReal).toReal := by
    norm_num
  have hAbs : Summable (fun n : ℕ ↦ |a n|) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      (lp.hasSum_norm hOne a).summable
  simpa only [mul_zero, add_zero] using hAbs.tendsto_atTop_zero.add (hTail.const_mul 2)

/-- The sum of a coordinate's absolute value and twice its strict upper absolute tail
is at most three times the `L1Seq` norm. -/
theorem positiveOperatorCoordBound_le (a : L1Seq) (n : ℕ) :
    |a n| + 2 * (∑' m : ℕ, if n < m then |a m| else 0) ≤ 3 * ‖a‖ := by
  -- Both the selected coordinate and the strict tail are bounded by the full absolute sum.
  have hOne : 0 < (1 : ENNReal).toReal := by
    norm_num
  have hAbs : Summable (fun m : ℕ ↦ |a m|) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      (lp.hasSum_norm hOne a).summable
  have hCoord : |a n| ≤ ‖a‖ := by
    rw [norm_eq_tsum_abs]
    simpa only [Finset.sum_singleton] using
      hAbs.sum_le_tsum {n} (fun m _ ↦ abs_nonneg (a m))
  have hTailAbs : Summable (fun m : ℕ ↦ if n < m then |a m| else 0) :=
    hAbs.summable_of_eq_zero_or_self fun m ↦ by
      by_cases hnm : n < m
      · exact Or.inr (if_pos hnm)
      · exact Or.inl (if_neg hnm)
  have hTail : (∑' m : ℕ, if n < m then |a m| else 0) ≤ ‖a‖ := by
    rw [norm_eq_tsum_abs]
    refine Summable.tsum_le_tsum (fun m ↦ ?_) hTailAbs hAbs
    by_cases hnm : n < m
    · simp only [if_pos hnm, le_refl]
    · simp only [if_neg hnm, abs_nonneg]
  -- Add the two estimates and collect the norm coefficients.
  calc
    |a n| + 2 * (∑' m : ℕ, if n < m then |a m| else 0) ≤
        ‖a‖ + 2 * ‖a‖ :=
      add_le_add hCoord (mul_le_mul_of_nonneg_left hTail (by norm_num))
    _ = 3 * ‖a‖ := by ring

/-- The weighted strict upper tail in a positive-operator coordinate is summable. -/
private theorem summable_positiveOperatorTail (a : L1Seq) (n : ℕ) :
    Summable (fun m : ℕ ↦
      if n < m then min (rationalTime n) (rationalTime m) * a m else 0) := by
  -- Recover absolute summability of the coordinates from the `L1Seq` norm formula.
  have hOne : 0 < (1 : ENNReal).toReal := by
    norm_num
  have hAbs : Summable (fun m : ℕ ↦ |a m|) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      (lp.hasSum_norm hOne a).summable
  -- Each kernel coefficient lies in `[0, 1]`, so comparison with `|a m|` applies.
  refine hAbs.of_norm_bounded (fun m ↦ ?_)
  by_cases hnm : n < m
  · rw [if_pos hnm, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (le_min (rationalTime_mem_Ioo n).1.le
        (rationalTime_mem_Ioo m).1.le)]
    exact mul_le_of_le_one_left (abs_nonneg (a m))
      ((min_le_left _ _).trans (rationalTime_mem_Ioo n).2.le)
  · simp only [if_neg hnm, norm_zero, abs_nonneg]

/-- A positive-operator coordinate is dominated by its diagonal absolute value and
twice the absolute strict upper tail. -/
private theorem abs_positiveOperatorCoord_le (a : L1Seq) (n : ℕ) :
    |positiveOperatorCoord a n| ≤
      |a n| + 2 * ∑' m : ℕ, if n < m then |a m| else 0 := by
  -- The unweighted absolute tail is summable because it is a restriction of an
  -- absolutely summable `L1Seq` coordinate family.
  have hOne : 0 < (1 : ENNReal).toReal := by
    norm_num
  have hAbs : Summable (fun m : ℕ ↦ |a m|) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      (lp.hasSum_norm hOne a).summable
  have hTailAbs : Summable (fun m : ℕ ↦ if n < m then |a m| else 0) :=
    hAbs.summable_of_eq_zero_or_self fun m ↦ by
      by_cases hnm : n < m
      · exact Or.inr (if_pos hnm)
      · exact Or.inl (if_neg hnm)
  -- Compare the weighted series with the unweighted absolute tail term by term.
  have hWeightedSum :
      |∑' m : ℕ, if n < m then min (rationalTime n) (rationalTime m) * a m else 0| ≤
        ∑' m : ℕ, if n < m then |a m| else 0 := by
    rw [← Real.norm_eq_abs]
    refine tsum_of_norm_bounded hTailAbs.hasSum (fun m ↦ ?_)
    by_cases hnm : n < m
    · rw [if_pos hnm, if_pos hnm, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (le_min (rationalTime_mem_Ioo n).1.le
          (rationalTime_mem_Ioo m).1.le)]
      exact mul_le_of_le_one_left (abs_nonneg (a m))
        ((min_le_left _ _).trans (rationalTime_mem_Ioo n).2.le)
    · simp only [if_neg hnm, norm_zero, le_refl]
  -- Apply the triangle inequality, then insert the kernel and series bounds.
  have hDiagonalAbs : |rationalTime n * a n| = rationalTime n * |a n| := by
    rw [abs_mul, abs_of_nonneg (rationalTime_mem_Ioo n).1.le]
  have hTwiceAbs (x : ℝ) : |2 * x| = 2 * |x| := by
    rw [abs_mul, abs_two]
  calc
    |positiveOperatorCoord a n| ≤
        |rationalTime n * a n| +
          |2 * ∑' m : ℕ,
            if n < m then min (rationalTime n) (rationalTime m) * a m else 0| := by
      exact abs_add_le _ _
    _ = rationalTime n * |a n| +
        2 * |∑' m : ℕ,
          if n < m then min (rationalTime n) (rationalTime m) * a m else 0| := by
      rw [hDiagonalAbs, hTwiceAbs]
    _ ≤ |a n| + 2 * ∑' m : ℕ, if n < m then |a m| else 0 := by
      exact add_le_add
        (mul_le_of_le_one_left (abs_nonneg (a n)) (rationalTime_mem_Ioo n).2.le)
        (mul_le_mul_of_nonneg_left hWeightedSum (by norm_num))

/-- The coordinate function of the positive operator tends to zero. -/
private theorem positiveOperatorCoord_tendsto (a : L1Seq) :
    Tendsto (positiveOperatorCoord a) atTop (𝓝 0) := by
  -- Squeeze the absolute coordinate values by the convergent majorant.
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun n ↦ abs_nonneg (positiveOperatorCoord a n))
    (Eventually.of_forall fun n ↦ abs_positiveOperatorCoord_le a n)
    (positiveOperatorCoordBound_tendsto a)

/-- The `C0Seq` value determined by the positive-operator coordinates. -/
private noncomputable def positiveOperatorValue (a : L1Seq) : C0Seq :=
  C0Seq.ofTendsto (positiveOperatorCoord a) (positiveOperatorCoord_tendsto a)

/-- Evaluating the bundled `C0Seq` value recovers its defining coordinate. -/
private theorem positiveOperatorValue_apply (a : L1Seq) (n : ℕ) :
    positiveOperatorValue a n = positiveOperatorCoord a n := by
  -- Use the public projection rule instead of unfolding the `C0Seq` constructor.
  exact C0Seq.ofTendsto_apply (positiveOperatorCoord a) (positiveOperatorCoord_tendsto a) n

/-- The positive-operator value is additive. -/
private theorem positiveOperatorValue_add (a b : L1Seq) :
    positiveOperatorValue (a + b) = positiveOperatorValue a + positiveOperatorValue b := by
  -- Extensionality reduces the bundled equality to distributivity of the coordinate series.
  ext n
  have hTailAdd :
      (fun m : ℕ ↦ if n < m then
          min (rationalTime n) (rationalTime m) * (a m + b m) else 0) =
        fun m : ℕ ↦
          (if n < m then min (rationalTime n) (rationalTime m) * a m else 0) +
          (if n < m then min (rationalTime n) (rationalTime m) * b m else 0) := by
    funext m
    by_cases hnm : n < m
    · simp only [if_pos hnm, mul_add]
    · simp only [if_neg hnm, add_zero]
  simp only [positiveOperatorValue, C0Seq.ofTendsto_apply, positiveOperatorCoord,
    ZeroAtInftyContinuousMap.add_apply, lp.coeFn_add, Pi.add_apply]
  rw [hTailAdd, (summable_positiveOperatorTail a n).tsum_add
    (summable_positiveOperatorTail b n)]
  ring

/-- The positive-operator value is homogeneous over `ℝ`. -/
private theorem positiveOperatorValue_smul (c : ℝ) (a : L1Seq) :
    positiveOperatorValue (c • a) = c • positiveOperatorValue a := by
  -- Extensionality reduces homogeneity to extraction of a scalar from the tail sum.
  ext n
  have hTailSmul :
      (fun m : ℕ ↦ if n < m then
          min (rationalTime n) (rationalTime m) * (c * a m) else 0) =
        fun m : ℕ ↦ c *
          (if n < m then min (rationalTime n) (rationalTime m) * a m else 0) := by
    funext m
    by_cases hnm : n < m
    · simp only [if_pos hnm]
      ring
    · simp only [if_neg hnm, mul_zero]
  simp only [positiveOperatorValue, C0Seq.ofTendsto_apply, positiveOperatorCoord,
    ZeroAtInftyContinuousMap.smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [hTailSmul, (summable_positiveOperatorTail a n).tsum_mul_left c]
  ring

/-- The positive-operator formula as a real-linear map into `C0Seq`. -/
private noncomputable def positiveOperatorLinearMap : L1Seq →ₗ[ℝ] C0Seq where
  toFun := positiveOperatorValue
  map_add' := positiveOperatorValue_add
  map_smul' := positiveOperatorValue_smul

/-- Evaluating the linear map at a coordinate recovers the coordinate formula. -/
private theorem positiveOperatorLinearMap_apply_coe (a : L1Seq) (n : ℕ) :
    positiveOperatorLinearMap a n = positiveOperatorCoord a n := by
  -- First project the linear map to its value, then project that value to a coordinate.
  exact positiveOperatorValue_apply a n

/-- Every value of the positive-operator linear map has norm at most three times
the norm of its argument. -/
private theorem positiveOperatorLinearMap_norm_le (a : L1Seq) :
    ‖positiveOperatorLinearMap a‖ ≤ 3 * ‖a‖ := by
  -- Transfer the norm to bounded functions and prove the uniform coordinate estimate.
  have hNonneg : 0 ≤ 3 * ‖a‖ := mul_nonneg (by norm_num) (norm_nonneg a)
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le hNonneg).2 (fun n ↦ ?_)
  rw [Real.norm_eq_abs]
  simpa only [ZeroAtInftyContinuousMap.toBCF_apply, positiveOperatorLinearMap_apply_coe] using
    (abs_positiveOperatorCoord_le a n).trans (positiveOperatorCoordBound_le a n)

/-- The bounded linear operator determined by the triangular rational-time kernel. -/
noncomputable def positiveOperator : L1Seq →L[ℝ] C0Seq :=
  LinearMap.mkContinuous positiveOperatorLinearMap 3 positiveOperatorLinearMap_norm_le

/-- The coordinates of `positiveOperator` are given by the defining triangular formula. -/
theorem positiveOperator_apply (a : L1Seq) (n : ℕ) :
    positiveOperator a n = rationalTime n * a n +
      2 * ∑' m : ℕ, if n < m then min (rationalTime n) (rationalTime m) * a m else 0 := by
  -- Project the bundled continuous map through the linear map and `C0Seq` constructors.
  calc
    positiveOperator a n = positiveOperatorLinearMap a n := rfl
    _ = positiveOperatorCoord a n := positiveOperatorLinearMap_apply_coe a n
    _ = rationalTime n * a n +
        2 * ∑' m : ℕ,
          if n < m then min (rationalTime n) (rationalTime m) * a m else 0 := rfl

/-- Each coordinate is bounded by the corresponding coordinate and the strict upper tail. -/
theorem abs_positiveOperator_apply_le (a : L1Seq) (n : ℕ) :
    |positiveOperator a n| ≤ |a n| + 2 * ∑' m : ℕ, if n < m then |a m| else 0 := by
  -- Rewrite the public coordinate formula and apply the established pointwise estimate.
  rw [positiveOperator_apply]
  exact abs_positiveOperatorCoord_le a n

/-- The operator norm of `positiveOperator` is at most `3`. -/
theorem norm_positiveOperator_le : ‖positiveOperator‖ ≤ 3 := by
  -- The operator norm inherits the constant used by `LinearMap.mkContinuous`.
  unfold positiveOperator
  exact LinearMap.mkContinuous_norm_le positiveOperatorLinearMap (by norm_num)
    positiveOperatorLinearMap_norm_le

end L1Seq
