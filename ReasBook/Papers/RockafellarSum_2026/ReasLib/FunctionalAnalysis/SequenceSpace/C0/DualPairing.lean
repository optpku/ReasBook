/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.Dual
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.DualPairing.Monotone

/-!
# Coordinate dual pairing

This module specializes the generic dual-pairing and monotone-polar API to
`C0Seq` and `L1Seq`.
-/

public section

namespace C0Seq

/-- The separating dual pairing between real `C0Seq` and real `L1Seq` induced by
coordinatewise summation. -/
noncomputable def coordinateDualPairing : DualPairing C0Seq L1Seq :=
  ⟨l1ToDual.toContinuousLinearMap, l1ToDual.injective⟩

/-- The dual map of `coordinateDualPairing` is the coordinatewise `L1Seq` embedding. -/
@[simp]
theorem coordinateDualPairing_toDual :
    coordinateDualPairing.toDual = l1ToDual.toContinuousLinearMap := by
  -- The bundled pairing stores precisely the established coordinate embedding.
  rfl

/-- The quadratic form on `C0Seq × L1Seq` induced by the coordinate dual pairing. -/
noncomputable def quadraticPairing : QuadraticForm ℝ (C0Seq × L1Seq) :=
  coordinateDualPairing.quadratic

/-- Evaluation of the quadratic pairing is the coordinatewise `C0Seq`–`L1Seq` pairing. -/
@[simp]
theorem quadraticPairing_apply (x : C0Seq) (a : L1Seq) :
    quadraticPairing (x, a) = pairingL x a := by
  -- First expose the generic quadratic evaluation through the bundled dual map.
  rw [quadraticPairing, DualPairing.quadratic_apply]
  -- Replace that dual map by the coordinatewise continuous pairing.
  rw [coordinateDualPairing_toDual, C0Seq.l1ToDual_toContinuousLinearMap]
  -- Its two evaluation rules now identify the result with `pairingL x a`.
  rw [C0Seq.pairingL_flip_apply, C0Seq.pairingL_apply]

/-- The C0-specific quadratic owner and the generic dual-pairing quadratic agree on
all product points; this bridge avoids relying on hidden module definitions. -/
theorem quadraticPairing_eq_coordinateQuadratic (z : C0Seq × L1Seq) :
    quadraticPairing z = coordinateDualPairing.quadratic z := by
  rcases z with ⟨x, a⟩
  rw [quadraticPairing_apply, DualPairing.quadratic_apply]
  rw [coordinateDualPairing_toDual, C0Seq.l1ToDual_toContinuousLinearMap]
  rw [C0Seq.pairingL_flip_apply, C0Seq.pairingL_apply]

/-- The symmetric bilinear form on `C0Seq × L1Seq` induced by the coordinate dual
pairing. -/
noncomputable def symmetricForm : LinearMap.BilinForm ℝ (C0Seq × L1Seq) :=
  coordinateDualPairing.symmetric

/-- Evaluation of the symmetric form is the sum of its two cross-pairings. -/
@[simp]
theorem symmetricForm_apply (x y : C0Seq) (a b : L1Seq) :
    symmetricForm (x, a) (y, b) = pairingL x b + pairingL y a := by
  -- Reduce the specialized form to the two generic cross-evaluations.
  rw [symmetricForm, DualPairing.symmetric_apply]
  -- Identify the bundled dual map with the coordinate pairing map.
  rw [coordinateDualPairing_toDual, C0Seq.l1ToDual_toContinuousLinearMap]
  -- Evaluate both cross-terms in the source-facing notation.
  simp only [C0Seq.pairingL_flip_apply, C0Seq.pairingL_apply]

/-- The quadratic pairing of a difference is the sum of the quadratic pairings minus
the symmetric cross term. -/
theorem quadraticPairing_sub (z w : C0Seq × L1Seq) :
    quadraticPairing (z - w) = quadraticPairing z + quadraticPairing w - symmetricForm z w := by
  -- Split the product points so subtraction is componentwise in the pairing formula.
  rcases z with ⟨x, a⟩
  rcases w with ⟨y, b⟩
  -- Evaluate the quadratic term of the difference through the coordinate pairing bridge.
  have hleft : quadraticPairing ((x, a) - (y, b)) = pairingL (x - y) (a - b) := by
    exact quadraticPairing_apply (x - y) (a - b)
  -- Rewrite every quadratic or symmetric term into its coordinatewise pairing expression.
  rw [hleft, quadraticPairing_apply, quadraticPairing_apply, symmetricForm_apply]
  -- Bilinearity expands the left side into four scalar terms.
  simp only [map_sub, sub_apply]
  -- The expanded cross terms cancel by commutative-ring normalization.
  ring

/-- The monotone polar on `C0Seq × L1Seq` associated with the coordinate dual pairing. -/
noncomputable def monotonePolar (S : Set (C0Seq × L1Seq)) : Set (C0Seq × L1Seq) :=
  coordinateDualPairing.monotonePolar S

/-- Membership in the coordinatewise monotone polar is nonnegativity of the quadratic
pairing against every point of the original set. -/
@[simp]
theorem mem_monotonePolar (S : Set (C0Seq × L1Seq)) (z : C0Seq × L1Seq) :
    z ∈ monotonePolar S ↔ ∀ s ∈ S, 0 ≤ quadraticPairing (z - s) := by
  -- Specialize the generic polar membership criterion to the coordinate pairing.
  rw [monotonePolar, DualPairing.mem_monotonePolar]
  -- The specialized quadratic form is definitionally the generic one here.
  rfl

/-- The source-facing polar notation is definitionally represented by the generic
dual-pairing polar, but this named equality is the stable cross-module API. -/
theorem monotonePolar_eq_coordinateDualPairing (S : Set (C0Seq × L1Seq)) :
    monotonePolar S = coordinateDualPairing.monotonePolar S := by
  ext z
  rw [mem_monotonePolar, DualPairing.mem_monotonePolar]
  simp_rw [quadraticPairing_eq_coordinateQuadratic]

end C0Seq
