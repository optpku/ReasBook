/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set

/-- Remark 1.3 (1): the textbook ray `[0,+∞[` is the closed ray `Set.Ici 0`. -/
theorem positiveReals_eq_Ici : {ξ : ℝ | 0 ≤ ξ} = Ici 0 :=
  rfl

/-- Remark 1.3 (2): the textbook ray `]0,+∞[` is the open ray `Set.Ioi 0`. -/
theorem strictlyPositiveReals_eq_Ioi : {ξ : ℝ | 0 < ξ} = Ioi 0 :=
  rfl

/-- Remark 1.3 (3): the textbook ray `]-∞,0]` is the closed ray `Set.Iic 0`. -/
theorem negativeReals_eq_Iic : {ξ : ℝ | ξ ≤ 0} = Iic 0 :=
  rfl

/-- Remark 1.3 (4): the textbook ray `]-∞,0[` is the open ray `Set.Iio 0`. -/
theorem strictlyNegativeReals_eq_Iio : {ξ : ℝ | ξ < 0} = Iio 0 :=
  rfl

/-- Remark 1.3 (5): the textbook orthant `[0,+∞[^N` is the positive cone `Set.Ici 0`
for the pointwise order on `Fin N → ℝ`. -/
theorem positiveOrthant_eq_Ici {N : ℕ} : {x : Fin N → ℝ | ∀ i, 0 ≤ x i} = Ici 0 :=
  rfl

/-- Remark 1.3 (6): the textbook orthant `]0,+∞[^N` is the product of the open rays
`Set.Ioi 0`. -/
theorem strictlyPositiveOrthant_eq_pi_Ioi {N : ℕ} :
    {x : Fin N → ℝ | ∀ i, 0 < x i} = pi (univ : Set (Fin N)) (fun _ ↦ Ioi (0 : ℝ)) := by
  ext x
  simp

/-- Remark 1.3 (7): the textbook orthant `]-∞,0]^N` is the negative cone `Set.Iic 0`
for the pointwise order on `Fin N → ℝ`. -/
theorem negativeOrthant_eq_Iic {N : ℕ} : {x : Fin N → ℝ | ∀ i, x i ≤ 0} = Iic 0 :=
  rfl

/-- Remark 1.3 (8): the textbook orthant `]-∞,0[^N` is the product of the open rays
`Set.Iio 0`. -/
theorem strictlyNegativeOrthant_eq_pi_Iio {N : ℕ} :
    {x : Fin N → ℝ | ∀ i, x i < 0} = pi (univ : Set (Fin N)) (fun _ ↦ Iio (0 : ℝ)) := by
  ext x
  simp

/-- Remark 1.3 (9): for a function `f : D → [-∞,+∞]`, the textbook notion of being increasing on
`D` is the canonical predicate `MonotoneOn f D`. -/
theorem increasingOn_iff_monotoneOn {D : Set ℝ} {f : ℝ → EReal} :
    (∀ ⦃ξ : ℝ⦄, ξ ∈ D → ∀ ⦃η : ℝ⦄, η ∈ D → ξ < η → f ξ ≤ f η) ↔ MonotoneOn f D :=
  monotoneOn_iff_forall_lt.symm

/-- Remark 1.3 (10): for a function `f : D → [-∞,+∞]`, the textbook notion of being strictly
increasing on `D` is the canonical predicate `StrictMonoOn f D`. -/
theorem strictlyIncreasingOn_iff_strictMonoOn {D : Set ℝ} {f : ℝ → EReal} :
    (∀ ⦃ξ : ℝ⦄, ξ ∈ D → ∀ ⦃η : ℝ⦄, η ∈ D → ξ < η → f ξ < f η) ↔ StrictMonoOn f D :=
  Iff.rfl

/-- Remark 1.3 (11): for a function `f : D → [-∞,+∞]`, the textbook notion of being decreasing on
`D` means that `-f` is increasing on `D`; canonically this is `AntitoneOn f D`. -/
theorem decreasingOn_iff_antitoneOn {D : Set ℝ} {f : ℝ → EReal} :
    MonotoneOn (fun ξ ↦ -f ξ) D ↔ AntitoneOn f D := by
  constructor
  · intro h ξ hξ η hη hξη
    exact EReal.neg_le_neg_iff.mp (h hξ hη hξη)
  · intro h ξ hξ η hη hξη
    exact EReal.neg_le_neg_iff.mpr (h hξ hη hξη)

/-- Remark 1.3 (12): for a function `f : D → [-∞,+∞]`, the textbook notion of being strictly
decreasing on `D` means that `-f` is strictly increasing on `D`; canonically this is
`StrictAntiOn f D`. -/
theorem strictlyDecreasingOn_iff_strictAntiOn {D : Set ℝ} {f : ℝ → EReal} :
    StrictMonoOn (fun ξ ↦ -f ξ) D ↔ StrictAntiOn f D := by
  constructor
  · intro h ξ hξ η hη hξη
    exact EReal.neg_lt_neg_iff.mp (h hξ hη hξη)
  · intro h ξ hξ η hη hξη
    exact EReal.neg_lt_neg_iff.mpr (h hξ hη hξη)
