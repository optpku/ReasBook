/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Gram
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing

/-!
# Positive-operator quadratic identity

This module derives the row-wise triangular expansion of the positive-operator
quadratic form.
-/

namespace L1Seq

/-- Multiplying a weighted strict-upper tail by its row coordinate gives the
corresponding row of the quadratic kernel. -/
private theorem positiveOperatorTail_mul_eq_upperRow (a : L1Seq) (n : ℕ) :
    (∑' m : ℕ,
      if n < m then min (rationalTime n) (rationalTime m) * a m else 0) * a n =
      ∑' m : ℕ,
        if n < m then
          min (rationalTime n) (rationalTime m) * a n * a m else 0 := by
  -- Move the row coordinate into the series and normalize each kernel term.
  rw [← tsum_mul_right]
  apply tsum_congr
  intro m
  by_cases hnm : n < m
  · simp only [if_pos hnm]
    ring
  · simp only [if_neg hnm, zero_mul]

/-- The quadratic pairing for `positiveOperator` is its diagonal series plus
twice its strict-upper-triangle series. -/
private theorem positiveOperator_pairing_eq_diag_add_two_upper (a : L1Seq) :
    C0Seq.pairingL (positiveOperator a) a =
      (∑' n : ℕ, rationalTime n * (a n) ^ 2) +
        2 * (∑' n : ℕ, ∑' m : ℕ,
          if n < m then
            min (rationalTime n) (rationalTime m) * a n * a m else 0) := by
  -- Absolute summability justifies splitting the diagonal and tail contributions.
  have hDiagonal : Summable (fun n : ℕ ↦ rationalTime n * (a n) ^ 2) :=
    (summable_abs_positiveOperator_diagonal a).of_abs
  have hOffDiagonal : Summable (fun n : ℕ ↦
      (2 * ∑' m : ℕ,
        if n < m then min (rationalTime n) (rationalTime m) * a m else 0) * a n) :=
    (summable_abs_positiveOperator_offDiagonal a).of_abs
  -- Expand the pairing coordinatewise and split the resulting summable series.
  calc
    C0Seq.pairingL (positiveOperator a) a =
        ∑' n : ℕ, (rationalTime n * (a n) ^ 2 +
          (2 * ∑' m : ℕ,
            if n < m then min (rationalTime n) (rationalTime m) * a m else 0) * a n) := by
      rw [C0Seq.pairingL_apply]
      apply tsum_congr
      intro n
      rw [positiveOperator_apply]
      ring
    _ = (∑' n : ℕ, rationalTime n * (a n) ^ 2) +
        ∑' n : ℕ,
          (2 * ∑' m : ℕ,
            if n < m then min (rationalTime n) (rationalTime m) * a m else 0) * a n :=
      hDiagonal.tsum_add hOffDiagonal
    _ = (∑' n : ℕ, rationalTime n * (a n) ^ 2) +
        ∑' n : ℕ, 2 * (∑' m : ℕ,
          if n < m then
            min (rationalTime n) (rationalTime m) * a n * a m else 0) := by
      congr 1
      apply tsum_congr
      intro n
      rw [← positiveOperatorTail_mul_eq_upperRow a n]
      ring
    _ = (∑' n : ℕ, rationalTime n * (a n) ^ 2) +
        2 * (∑' n : ℕ, ∑' m : ℕ,
          if n < m then
            min (rationalTime n) (rationalTime m) * a n * a m else 0) := by
      rw [tsum_mul_left]

/-- The quadratic pairing of `positiveOperator a` with `a` is the rational-time
Gram double series. -/
public theorem positiveOperator_quadratic_eq_gramTsum (a : L1Seq) :
    C0Seq.pairingL (positiveOperator a) a =
      ∑' p : ℕ × ℕ,
        min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2 := by
  -- Pass through the diagonal-plus-upper expansion of the quadratic form.
  calc
    C0Seq.pairingL (positiveOperator a) a =
        (∑' n : ℕ, rationalTime n * (a n) ^ 2) +
          2 * (∑' n : ℕ, ∑' m : ℕ,
            if n < m then
              min (rationalTime n) (rationalTime m) * a n * a m else 0) :=
      positiveOperator_pairing_eq_diag_add_two_upper a
    _ = ∑' p : ℕ × ℕ,
        min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2 :=
      positiveOperator_diag_add_two_upper_eq_kernel a

/-- The quadratic pairing of `positiveOperator a` with `a` is the squared norm of
the image of `a` under `intervalCoordinateOperator`. -/
public theorem positiveOperator_quadratic_eq_norm_sq (a : L1Seq) :
    C0Seq.pairingL (positiveOperator a) a =
      ‖intervalCoordinateOperator a‖ ^ 2 := by
  -- Chain the quadratic Gram identity with the interval-coordinate norm identity.
  calc
    C0Seq.pairingL (positiveOperator a) a =
        ∑' p : ℕ × ℕ,
          min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2 :=
      positiveOperator_quadratic_eq_gramTsum a
    _ = ‖intervalCoordinateOperator a‖ ^ 2 :=
      gramTsum_eq_norm_intervalCoordinateOperator_sq a

end L1Seq
