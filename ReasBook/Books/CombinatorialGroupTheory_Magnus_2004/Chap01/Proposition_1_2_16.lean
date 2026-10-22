/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_26

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-2-16: a free group has solvable conjugacy problem, equivalently conjugacy is a
decidable relation on `F`. -/
-- Layer: `source-facing`.
-- `core/canonical`: `IsConj`.
-- `bridge/view`: specialize the tuple common-conjugator decision procedure
-- `exists_common_conjugator_decidable` to the one-point index type `Fin 1`.
noncomputable instance decidableIsConjOfIsFreeGroup : DecidableRel (IsConj : F → F → Prop) := by
  intro x y
  letI := exists_common_conjugator_decidable (fun _ ↦ x : Fin 1 → F) (fun _ ↦ y)
  have hsingle :
      (∃ w : F, ∀ i : Fin 1, w⁻¹ * (fun _ ↦ x : Fin 1 → F) i * w = (fun _ ↦ y) i) ↔
        ∃ w : F, w⁻¹ * x * w = y := by
    simp
  have hconj : (∃ w : F, w⁻¹ * x * w = y) ↔ IsConj x y := by
    rw [isConj_iff]
    constructor <;> rintro ⟨w, hw⟩ <;> refine ⟨w⁻¹, ?_⟩ <;> simpa [mul_assoc] using hw
  exact decidable_of_iff _ (hsingle.trans hconj)

end
