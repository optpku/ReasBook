/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy

/-!
# Same-positive-coordinate rigidity

This module records quadratic-pairing and rigidity consequences for parametrized
points sharing a positive coordinate.
-/

public section

namespace Lorentz

/-- The quadratic pairing of the difference of two parametrized points with
the same positive coordinate is the negative squared distance between their
negative coordinates. -/
theorem sameP_quadraticPairing (d : C0Seq) (hd : d ≠ 0)
    (w mP : parametrizedSubspace d)
    (hP : positiveCoordinate d hd w = positiveCoordinate d hd mP) :
    C0Seq.quadraticPairing (w - mP) =
      -(‖negativeCoordinate d hd w - negativeCoordinate d hd mP‖ ^ 2) := by
  -- Identify subspace subtraction with subtraction in the ambient product.
  have hco : ((w - mP : parametrizedSubspace d) : C0Seq × L1Seq) =
      (w : C0Seq × L1Seq) - (mP : C0Seq × L1Seq) :=
    Submodule.coe_sub (parametrizedSubspace d) w mP
  rw [← hco]
  -- Apply the Lorentz identity and annihilate the positive-coordinate term.
  rw [quadraticIdentity d hd]
  have hPsub : positiveCoordinate d hd (w - mP) = 0 := by
    rw [map_sub, hP, sub_self]
  rw [hPsub]
  -- Linearity normalizes the remaining negative-coordinate difference.
  norm_num

/-- If two parametrized points have the same positive coordinate and the
quadratic pairing of their difference is nonnegative, then their negative
coordinates coincide. -/
theorem sameP_rigidity (d : C0Seq) (hd : d ≠ 0)
    (w mP : parametrizedSubspace d)
    (hP : positiveCoordinate d hd w = positiveCoordinate d hd mP)
    (h_nonneg : 0 ≤ C0Seq.quadraticPairing (w - mP)) :
    negativeCoordinate d hd w = negativeCoordinate d hd mP := by
  -- The exact formula and external nonnegativity force the squared norm to vanish.
  have hformula := sameP_quadraticPairing d hd w mP hP
  have hsq : ‖negativeCoordinate d hd w - negativeCoordinate d hd mP‖ ^ 2 = 0 := by
    nlinarith [h_nonneg, hformula]
  -- A zero norm separates points, yielding equality of the two coordinates.
  have hnorm : ‖negativeCoordinate d hd w - negativeCoordinate d hd mP‖ = 0 := by
    nlinarith [sq_nonneg (‖negativeCoordinate d hd w - negativeCoordinate d hd mP‖)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end Lorentz
