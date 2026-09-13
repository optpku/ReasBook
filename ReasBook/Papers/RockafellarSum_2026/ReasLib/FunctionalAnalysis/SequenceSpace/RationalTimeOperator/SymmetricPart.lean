/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.Transpose
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Bilinear
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.QuadraticIdentity
public import RockafellarSum_2026.ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Adjoint

/-!
# Symmetric part of the positive operator

This module identifies the symmetric part of the rational-time positive
operator with the interval-coordinate Gram operator.
-/

namespace L1Seq

/-- The symmetric part of the rational-time positive operator is twice the Gram
operator of the interval-coordinate map. -/
public theorem positiveOperator_symmetricPart :
    C0Seq.pairingL.comp positiveOperator + positiveOperator.reindexedTranspose =
      2 • (intervalCoordinateAdjoint.comp intervalCoordinateOperator) := by
  -- Evaluate both bundled operators on arbitrary vectors to expose the scalar bilinear identity.
  apply ContinuousLinearMap.ext
  intro b
  apply ContinuousLinearMap.ext
  intro a
  -- The reindexed transpose supplies the pairing with the two arguments exchanged.
  have h_pair_transpose :
      positiveOperator.reindexedTranspose b a = C0Seq.pairingL (positiveOperator a) b := by
    rw [ContinuousLinearMap.reindexedTranspose_apply_apply,
      C0Seq.pairingL_apply]
  simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply]
  rw [h_pair_transpose]
  -- Record the diagonal quadratic identity at the sum and at each individual argument.
  have hQ_add := positiveOperator_quadratic_eq_norm_sq (b + a)
  have hQ_b := positiveOperator_quadratic_eq_norm_sq b
  have hQ_a := positiveOperator_quadratic_eq_norm_sq a
  have hQ_add' :
      C0Seq.pairingL (positiveOperator (b + a)) (b + a) =
        ‖intervalCoordinateOperator b + intervalCoordinateOperator a‖ *
          ‖intervalCoordinateOperator b + intervalCoordinateOperator a‖ := by
    simpa [map_add, pow_two] using hQ_add
  have hQ_b' :
      C0Seq.pairingL (positiveOperator b) b = ‖intervalCoordinateOperator b‖ *
        ‖intervalCoordinateOperator b‖ := by
    simpa [pow_two] using hQ_b
  have hQ_a' :
      C0Seq.pairingL (positiveOperator a) a = ‖intervalCoordinateOperator a‖ *
        ‖intervalCoordinateOperator a‖ := by
    simpa [pow_two] using hQ_a
  -- Rewrite the adjoint composite as an inner product and polarize that inner product.
  simp only [intervalCoordinateAdjoint_apply, two_nsmul]
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  -- Substitute the three diagonal identities; bilinearity leaves a scalar polynomial identity.
  rw [← hQ_add', ← hQ_b', ← hQ_a']
  simp only [map_add, add_apply]
  ring

/-- Evaluating the symmetric-part identity at `b` and representing the transpose value
by `x` expresses the resulting Gram value through the canonical pairing. -/
public theorem two_smul_intervalCoordinateAdjoint_eq_pairingL (b : L1Seq) (x : C0Seq)
    (h_transpose : positiveOperator.reindexedTranspose b = C0Seq.pairingL x) :
    2 • intervalCoordinateAdjoint (intervalCoordinateOperator b) =
      C0Seq.pairingL (positiveOperator b + x) := by
  -- Evaluate the bundled symmetric-part identity at the chosen vector.
  have h_sym := positiveOperator_symmetricPart
  have h_sym_b := congrArg (fun f : L1Seq →L[ℝ] StrongDual ℝ L1Seq => f b) h_sym
  have h_sym_b' :
      C0Seq.pairingL (positiveOperator b) + positiveOperator.reindexedTranspose b =
        intervalCoordinateAdjoint (intervalCoordinateOperator b) +
          intervalCoordinateAdjoint (intervalCoordinateOperator b) := by
    simpa only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, two_nsmul] using h_sym_b
  -- Substitute the chosen transpose representative and combine the two canonical pairings.
  rw [h_transpose] at h_sym_b'
  rw [C0Seq.pairingL.map_add]
  simpa only [two_nsmul] using h_sym_b'.symm

end L1Seq
