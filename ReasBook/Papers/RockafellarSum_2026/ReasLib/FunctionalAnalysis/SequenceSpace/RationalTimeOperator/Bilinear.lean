/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator
public import RockafellarSum_2026.ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator

/-!
# Positive-operator bilinear form

This module records the bilinear and quadratic identities induced by the
positive interval-coordinate operator on `L1Seq`.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace L1Seq

/-- The continuous bilinear form obtained by pairing the positive operator with a second
`L1Seq` argument. -/
noncomputable def positiveOperatorForm : L1Seq →L[ℝ] L1Seq →L[ℝ] ℝ :=
  C0Seq.pairingL.comp positiveOperator

/-- Twice the real Hilbert inner product after applying the interval-coordinate operator
in both arguments. -/
noncomputable def intervalCoordinateForm : L1Seq →L[ℝ] L1Seq →L[ℝ] ℝ :=
  2 • (innerSL ℝ).bilinearComp intervalCoordinateOperator intervalCoordinateOperator

/-- The positive-operator form evaluates as the canonical `C0Seq`–`L1Seq` pairing. -/
@[simp]
theorem positiveOperatorForm_apply (a b : L1Seq) :
    positiveOperatorForm a b = C0Seq.pairingL (positiveOperator a) b := by
  -- Evaluating the bundled composition exposes the defining pairing.
  rfl

/-- The interval-coordinate form evaluates as twice the real Hilbert inner product. -/
@[simp]
theorem intervalCoordinateForm_apply (a b : L1Seq) :
    intervalCoordinateForm a b =
      2 * ⟪intervalCoordinateOperator a, intervalCoordinateOperator b⟫_ℝ := by
  -- Pointwise evaluation reduces scalar multiplication and bilinear composition.
  simp only [intervalCoordinateForm, smul_apply,
    ContinuousLinearMap.bilinearComp_apply, coe_innerSL_apply, nsmul_eq_mul,
    Nat.cast_ofNat]

/-- Flipping the two arguments leaves the interval-coordinate form unchanged. -/
@[simp]
theorem flip_intervalCoordinateForm :
    intervalCoordinateForm.flip = intervalCoordinateForm := by
  -- Compare the bundled forms pointwise, then use symmetry of the real inner product.
  ext a b
  rw [ContinuousLinearMap.flip_apply, intervalCoordinateForm_apply,
    intervalCoordinateForm_apply, real_inner_comm]

/-- The interval-coordinate form is symmetric in its two arguments. -/
theorem intervalCoordinateForm_comm (a b : L1Seq) :
    intervalCoordinateForm a b = intervalCoordinateForm b a := by
  -- Evaluate the flip equality at the reversed pair of arguments.
  simpa only [ContinuousLinearMap.flip_apply] using
    congrArg (fun form ↦ form b a) flip_intervalCoordinateForm

end L1Seq
