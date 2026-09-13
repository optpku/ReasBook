/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.SymmetricPart

/-!
# Parametrized-point pairing

This module expands the symmetric pairing on the parametrized Lorentz
subspace.
-/

public section

open scoped InnerProductSpace

namespace Lorentz

/-- The symmetric pairing of `(x, u)` with the parametrized point at
`(a, -C0Seq.pairingL d a)` expands in terms of the positive operator,
interval-coordinate operator, and pairing with `d`. -/
theorem detectorPairingFormula (d x : C0Seq) (u a : L1Seq) :
    C0Seq.symmetricForm (x, u)
        (parametrization d (a, -C0Seq.pairingL d a)) =
      C0Seq.pairingL (x + L1Seq.positiveOperator u) a -
        2 * ⟪L1Seq.intervalCoordinateOperator u,
          L1Seq.intervalCoordinateOperator a⟫_ℝ -
        C0Seq.pairingL d u * C0Seq.pairingL d a := by
  -- Evaluate the transpose term in the symmetric-part identity as the reversed pairing.
  have h_transpose :
      L1Seq.positiveOperator.reindexedTranspose u a =
        C0Seq.pairingL (L1Seq.positiveOperator a) u := by
    rw [ContinuousLinearMap.reindexedTranspose_apply_apply, C0Seq.pairingL_apply]
  -- Specialize the operator identity twice to obtain the scalar polarization formula.
  have h_polarization :
      C0Seq.pairingL (L1Seq.positiveOperator u) a +
          C0Seq.pairingL (L1Seq.positiveOperator a) u =
        2 * ⟪L1Seq.intervalCoordinateOperator u,
          L1Seq.intervalCoordinateOperator a⟫_ℝ := by
    have h_symmetricPart := congrArg
      (fun operator : L1Seq →L[ℝ] StrongDual ℝ L1Seq => operator u)
      L1Seq.positiveOperator_symmetricPart
    have h_evaluated := congrArg (fun functional : StrongDual ℝ L1Seq => functional a)
      h_symmetricPart
    simpa only [add_apply, ContinuousLinearMap.comp_apply, smul_apply, h_transpose,
      L1Seq.intervalCoordinateAdjoint_apply, two_nsmul, two_mul] using h_evaluated
  -- Expand the two public evaluation interfaces, substitute polarization, and collect terms.
  rw [parametrization_apply, C0Seq.symmetricForm_apply]
  simp only [map_add, map_neg, map_smul, add_apply, neg_apply, smul_apply]
  rw [← h_polarization]
  ring

end Lorentz
