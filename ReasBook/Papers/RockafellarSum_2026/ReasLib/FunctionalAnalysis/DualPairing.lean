/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Continuous dual pairings

This module defines the bundled continuous dual pairing and its quadratic,
bilinear, and symmetric-form API.
-/

public section

universe u v

/-- An explicit continuous pairing of `X` with `Xstar`, nondegenerate in the `Xstar`
argument. -/
structure DualPairing (X : Type u) (Xstar : Type v) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar] where
  toDual : Xstar →L[ℝ] StrongDual ℝ X
  injective_toDual : Function.Injective toDual

namespace DualPairing

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/-- The standard pairing between a real normed space and its strong dual. -/
noncomputable def strongDual : DualPairing X (StrongDual ℝ X) :=
  ⟨ContinuousLinearMap.id ℝ (StrongDual ℝ X), Function.injective_id⟩

/-- The map underlying the standard strong-dual pairing is the identity. -/
@[simp]
theorem strongDual_toDual :
    (strongDual : DualPairing X (StrongDual ℝ X)).toDual =
      ContinuousLinearMap.id ℝ (StrongDual ℝ X) := by
  -- Projecting the map field of the standard pairing recovers the identity map.
  rfl

/-- The pairing as a bilinear map, with the primal argument first. -/
def toLinearPairing (P : DualPairing X Xstar) : X →ₗ[ℝ] Xstar →ₗ[ℝ] ℝ :=
  ((topDualPairing ℝ X).comp P.toDual.toLinearMap).flip

/-- Evaluation of the algebraic view of a continuous dual pairing. -/
@[simp]
theorem toLinearPairing_apply (P : DualPairing X Xstar) (x : X) (xstar : Xstar) :
    P.toLinearPairing x xstar = P.toDual xstar x := by
  -- Flipping the canonical dual evaluation puts the primal variable first.
  rfl

/-- Injectivity of `P.toDual` makes the pairing separating in its right argument. -/
theorem toLinearPairing_separatingRight (P : DualPairing X Xstar) :
    P.toLinearPairing.SeparatingRight := by
  -- Pointwise vanishing makes the corresponding strong-dual functional zero.
  intro xstar hzero
  apply P.injective_toDual
  ext x
  simpa only [toLinearPairing_apply, map_zero, zero_apply] using hzero x

/-- The cross term on the product, pairing the first component on the left with the second
component on the right. -/
def cross (P : DualPairing X Xstar) : LinearMap.BilinForm ℝ (X × Xstar) :=
  P.toLinearPairing.compl₁₂ (LinearMap.fst ℝ X Xstar) (LinearMap.snd ℝ X Xstar)

/-- Evaluation of the cross term on two product elements. -/
@[simp]
theorem cross_apply (P : DualPairing X Xstar) (z w : X × Xstar) :
    P.cross z w = P.toDual w.2 z.1 := by
  -- The product projections feed the primal and dual components to the pairing.
  rfl

/-- The quadratic form on `X × Xstar` obtained by evaluating the dual component at the
primal component. -/
def quadratic (P : DualPairing X Xstar) : QuadraticForm ℝ (X × Xstar) :=
  P.cross.toQuadraticMap

/-- Evaluation of the quadratic pairing. -/
@[simp]
theorem quadratic_apply (P : DualPairing X Xstar) (x : X) (xstar : Xstar) :
    P.quadratic (x, xstar) = P.toDual xstar x := by
  -- Evaluating the quadratic map means evaluating the cross form on the diagonal.
  rfl

/-- The symmetric bilinear form on `X × Xstar` obtained by summing the two cross-pairings. -/
def symmetric (P : DualPairing X Xstar) : LinearMap.BilinForm ℝ (X × Xstar) :=
  P.cross + P.cross.flip

/-- Evaluation of the symmetric bilinear form. -/
@[simp]
theorem symmetric_apply (P : DualPairing X Xstar) (x y : X) (xstar ystar : Xstar) :
    P.symmetric (x, xstar) (y, ystar) = P.toDual ystar x + P.toDual xstar y := by
  -- The form and its flip contribute the two cross-pairings.
  rfl

/-- The polarized form associated to `P.quadratic` is `P.symmetric`. -/
theorem polarBilin_quadratic (P : DualPairing X Xstar) :
    P.quadratic.polarBilin = P.symmetric := by
  -- Polarizing the diagonal of a bilinear map adds that map to its flip.
  exact LinearMap.BilinMap.polarBilin_toQuadraticMap

/-- The product bilinear form associated to a dual pairing is symmetric. -/
theorem symmetric_isSymm (P : DualPairing X Xstar) : P.symmetric.IsSymm := by
  -- Swapping the arguments exchanges the two summands in the evaluation formula.
  constructor
  rintro ⟨x, xstar⟩ ⟨y, ystar⟩
  rw [symmetric_apply, symmetric_apply, add_comm]

end DualPairing
