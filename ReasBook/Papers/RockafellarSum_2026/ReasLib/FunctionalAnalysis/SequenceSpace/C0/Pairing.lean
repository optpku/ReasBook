/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import RockafellarSum_2026.ReasLib.Analysis.Sequence.L1
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.Single

/-!
# The `C0Seq`--`L1Seq` pairing

This module develops the bounded coordinatewise pairing and its continuous-dual
API.
-/

public section

namespace C0Seq

/-- The absolute values of the coordinatewise products of a sequence tending to zero and a
summable sequence are summable. -/
theorem summable_abs_mul (x : C0Seq) (a : L1Seq) :
    Summable (fun n : ℕ ↦ |x n * a n|) := by
  -- Normalize the exponent-one `lp` sum to the absolute-value series of `a`.
  have hOne : 0 < (1 : ENNReal).toReal := by
    norm_num
  have hAbs : HasSum (fun n : ℕ ↦ |a n|) ‖a‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      lp.hasSum_norm hOne a
  -- Dominate each product by the norm-scaled absolutely summable majorant.
  refine Summable.of_nonneg_of_le (fun n ↦ abs_nonneg (x n * a n)) (fun n ↦ ?_)
    (hAbs.mul_left ‖x‖).summable
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_apply_le_norm x n) (abs_nonneg (a n))

/-- The coordinatewise products of a sequence tending to zero and a summable sequence are
summable. -/
theorem summable_mul (x : C0Seq) (a : L1Seq) :
    Summable (fun n : ℕ ↦ x n * a n) := by
  -- Absolute summability immediately implies summability of the signed products.
  exact (summable_abs_mul x a).of_abs

/-- The absolute value of the coordinatewise pairing of a sequence tending to zero with a
summable sequence is at most the product of their norms. -/
theorem abs_tsum_mul_le (x : C0Seq) (a : L1Seq) :
    |∑' n : ℕ, x n * a n| ≤ ‖x‖ * ‖a‖ := by
  -- Recover the exact sum of the absolute values of the `L1Seq` coordinates.
  have hOne : 0 < (1 : ENNReal).toReal := by
    norm_num
  have hAbs : HasSum (fun n : ℕ ↦ |a n|) ‖a‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      lp.hasSum_norm hOne a
  -- Compare the pairing series with the norm-scaled absolute-value series.
  have hBound : ‖∑' n : ℕ, x n * a n‖ ≤ ‖x‖ * ‖a‖ := by
    refine tsum_of_norm_bounded (hAbs.mul_left ‖x‖) (fun n ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_apply_le_norm x n) (abs_nonneg (a n))
  simpa only [Real.norm_eq_abs] using hBound

/-- The coordinatewise `C0Seq`–`L1Seq` pairing is a bounded real bilinear map. -/
private theorem isBoundedBilinearMap_pairing :
    IsBoundedBilinearMap ℝ
      (fun p : C0Seq × L1Seq ↦ ∑' n : ℕ, p.1 n * p.2 n) := by
  -- Distribute the summable coordinate products in the `C0Seq` argument.
  constructor
  · intro x₁ x₂ a
    simpa only [ZeroAtInftyContinuousMap.add_apply, Pi.add_apply, add_mul] using
      (summable_mul x₁ a).tsum_add (summable_mul x₂ a)
  -- Extract real scalars from the summable series in the `C0Seq` argument.
  · intro c x a
    simpa only [ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul, mul_assoc] using
      (summable_mul x a).tsum_mul_left c
  -- Distribute the summable coordinate products in the `L1Seq` argument.
  · intro x a₁ a₂
    simpa only [lp.coeFn_add, Pi.add_apply, mul_add] using
      (summable_mul x a₁).tsum_add (summable_mul x a₂)
  -- Commute a real scalar past the first factor before extracting it from the series.
  · intro c x a
    simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm] using
      (summable_mul x a).tsum_mul_left c
  -- The sharp pairing estimate supplies a positive bound constant equal to one.
  · refine ⟨1, ?_, ?_⟩
    · exact one_pos
    · intro x a
      simpa only [Real.norm_eq_abs, one_mul] using abs_tsum_mul_le x a

/-- The coordinatewise pairing of a sequence tending to zero and a summable sequence,
bundled as continuous linear maps in both variables. -/
noncomputable def pairingL : C0Seq →L[ℝ] L1Seq →L[ℝ] ℝ :=
  isBoundedBilinearMap_pairing.toContinuousLinearMap

/-- Evaluating `pairingL` gives the coordinatewise sum. -/
@[simp]
theorem pairingL_apply (x : C0Seq) (a : L1Seq) :
    pairingL x a = ∑' n : ℕ, x n * a n := by
  -- Evaluate through the public computation rule for the bounded bilinear construction.
  simpa only [pairingL] using isBoundedBilinearMap_pairing.toContinuousLinearMap_apply x a

/-- Evaluating the flipped currying of `pairingL` gives the same coordinatewise sum. -/
@[simp]
theorem pairingL_flip_apply (a : L1Seq) (x : C0Seq) :
    pairingL.flip a x = ∑' n : ℕ, x n * a n := by
  -- Flipping only exchanges the two curried arguments, so ordinary evaluation applies.
  rw [ContinuousLinearMap.flip_apply, pairingL_apply]

/-- The bundled `C0Seq`–`L1Seq` pairing has operator norm at most one. -/
theorem norm_pairingL_le : ‖pairingL‖ ≤ 1 := by
  -- Lift the pointwise product-norm estimate to the bilinear operator norm.
  refine pairingL.opNorm_le_bound₂ zero_le_one ?_
  intro x a
  simpa only [pairingL_apply, Real.norm_eq_abs, one_mul] using abs_tsum_mul_le x a

/-- Pairing against an `L1Seq` singleton reads the corresponding `C0Seq` coordinate. -/
private theorem pairingL_lpSingle_apply (x : C0Seq) (n : ℕ) (r : ℝ) :
    pairingL x (lp.single 1 n r) = x n * r := by
  -- Collapse the pairing sum to the sole coordinate supported by the singleton.
  rw [pairingL_apply, tsum_eq_single n]
  · rw [lp.single_apply_self]
  · intro m hm
    simp only [lp.single_apply, Pi.single_apply, if_neg hm, mul_zero]

/-- The coordinatewise pairing embeds `C0Seq` into the continuous dual of `L1Seq`. -/
theorem pairingL_injective : Function.Injective pairingL := by
  intro x y hxy
  -- Test equal paired functionals on each unit coordinate vector.
  ext n
  have hEvaluation :=
    congrArg (fun f : StrongDual ℝ L1Seq ↦ f (lp.single 1 n (1 : ℝ))) hxy
  simpa only [pairingL_lpSingle_apply, mul_one] using hEvaluation

/-- Pairing a standard coordinate vector with a summable sequence evaluates that sequence
at the chosen coordinate and scales the result. -/
@[simp]
theorem pairingL_c0Single_apply (n : ℕ) (r : ℝ) (a : L1Seq) :
    pairingL (c0Single n r) a = r * a n := by
  -- Collapse the coordinatewise sum to the support of `c0Single`.
  rw [pairingL_apply, tsum_eq_single n]
  · rw [c0Single_apply, if_pos rfl]
  · intro m hm
    rw [c0Single_apply, if_neg hm, zero_mul]

end C0Seq
