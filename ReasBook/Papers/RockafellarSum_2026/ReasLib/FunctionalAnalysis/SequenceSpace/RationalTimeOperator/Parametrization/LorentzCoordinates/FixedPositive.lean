/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates

/-!
# Fixed-positive Lorentz coordinates

This module adjusts the parametrization parameter to prescribe a positive
Lorentz coordinate.
-/

public section

namespace Lorentz

/-- Choosing `t = 2 * p - C0Seq.pairingL d a` makes the positive Lorentz
coordinate of `parametrizedPoint d a t` equal to `p`. -/
theorem positiveCoordinate_adjustedParameter (d : C0Seq) (hd : d ≠ 0)
    (a : L1Seq) (p : ℝ) :
    positiveCoordinate d hd
        (parametrizedPoint d a (2 * p - C0Seq.pairingL d a)) = p := by
  -- Evaluate the positive coordinate, then cancel the pairing terms.
  rw [positiveCoordinate_apply]
  ring

/-- The negative Lorentz coordinate at the parameter adjusted to prescribe its
positive coordinate. -/
theorem negativeCoordinate_adjustedParameter (d : C0Seq) (hd : d ≠ 0)
    (a : L1Seq) (p : ℝ) :
    negativeCoordinate d hd
        (parametrizedPoint d a (2 * p - C0Seq.pairingL d a)) =
      HilbertProd2.mk (L1Seq.intervalCoordinateOperator a)
        (p - C0Seq.pairingL d a) := by
  -- Evaluate the negative coordinate and normalize its scalar component.
  rw [negativeCoordinate_apply]
  congr 1
  ring

end Lorentz
