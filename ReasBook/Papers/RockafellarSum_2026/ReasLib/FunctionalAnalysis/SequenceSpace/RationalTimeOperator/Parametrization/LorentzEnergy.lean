/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.Analysis.Normed.LorentzCone.HilbertProd2
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.QuadraticIdentity
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.SymmetricPart

/-!
# Parametrized Lorentz energy

This module supplies the quadratic and symmetric pairing formulas for
parametrized Lorentz points.
-/

public section

open scoped InnerProductSpace

namespace Lorentz

/-- The quadratic pairing of a parametrized point is its representative-level
operator expression. -/
theorem quadraticPairing_parametrization (d : C0Seq) (a : L1Seq) (t : ℝ) :
    C0Seq.quadraticPairing (parametrization d (a, t)) =
      -(‖L1Seq.intervalCoordinateOperator a‖ ^ 2) + t * C0Seq.pairingL d a := by
  -- Expand the parametrization and distribute the dual pairing over its three terms.
  rw [parametrization_apply, C0Seq.quadraticPairing_apply]
  rw [map_add, map_smul]
  rw [map_neg]
  -- Replace the positive-operator quadratic form by the squared interval norm.
  rw [← L1Seq.positiveOperator_quadratic_eq_norm_sq]
  simp only [add_apply, neg_apply, smul_apply, smul_eq_mul]

/-- On a subspace parametrized by a nonzero vector, the quadratic pairing is
the Lorentz energy of the intrinsic coordinates. -/
theorem quadraticPairing_eq_energy (d : C0Seq) (hd : d ≠ 0)
    (z : parametrizedSubspace d) :
    C0Seq.quadraticPairing z =
      energy (positiveCoordinate d hd z, negativeCoordinate d hd z) := by
  -- Choose representative parameters for the point in the parametrized subspace.
  have hzmem := (mem_parametrizedSubspace d z.1).mp z.property
  rcases hzmem with ⟨a, t, hu⟩
  have hz : z = parametrizedPoint d a t := by
    apply Subtype.ext
    rw [parametrizedPoint_apply, parametrization_apply]
    exact hu
  subst z
  -- Rewrite all three quantities on the canonical representative and complete the square.
  rw [parametrizedPoint_apply, quadraticPairing_parametrization]
  rw [positiveCoordinate_apply, negativeCoordinate_apply]
  exact completeSquareEnergy (L1Seq.intervalCoordinateOperator a)
    (C0Seq.pairingL d a) t

/-- On a subspace parametrized by a nonzero vector, the quadratic pairing is
the square of the positive coordinate minus the squared norm of the negative
coordinate. -/
theorem quadraticIdentity (d : C0Seq) (hd : d ≠ 0) (z : parametrizedSubspace d) :
    C0Seq.quadraticPairing z =
      positiveCoordinate d hd z ^ 2 - ‖negativeCoordinate d hd z‖ ^ 2 := by
  -- Pass through Lorentz energy, whose definition is the required difference of squares.
  rw [quadraticPairing_eq_energy]
  rfl

end Lorentz
