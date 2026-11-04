/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
import Mathlib.Algebra.BigOperators.Fin

open scoped Matrix

section Definition19

variable {n p : ℕ}

/- Definition 1.9 (1). For `K ⊆ ℝ^d`, the existing project owner
`is_valid_inequality K α β` is the notion that `α u ≤ β` is valid for `K`. -/
#check is_valid_inequality

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_2/ch1_sec1_2_2_definition_1_9.lean
Definition 1.9 (2). An inequality `α x + γ y ≤ β` is a cutting plane for
`S ⊆ ℝ^n × ℝ^p` at `xy0` when it is valid on `S` and is strictly violated at `xy0`. -/
structure isCuttingPlaneAt
    (S : Set (MixedRealPoint n p))
    (xy0 : MixedRealPoint n p)
    (α : Fin n → ℝ)
    (γ : Fin p → ℝ)
    (β : ℝ) : Prop where
  validOnSet : is_valid_inequality ((Fin.appendEquiv n p) '' S) (Fin.append α γ) β
  strictViolation : β < α ⬝ᵥ xy0.1 + γ ⬝ᵥ xy0.2

/-- Build a cutting plane at `xy0` from validity on `S` and strict violation at `xy0`. -/
def isCuttingPlaneAt.ofConditions
    (S : Set (MixedRealPoint n p))
    (xy0 : MixedRealPoint n p)
    (α : Fin n → ℝ)
    (γ : Fin p → ℝ)
    (β : ℝ)
    (hvalid : is_valid_inequality ((Fin.appendEquiv n p) '' S) (Fin.append α γ) β)
    (hcutsOff : β < α ⬝ᵥ xy0.1 + γ ⬝ᵥ xy0.2) :
    isCuttingPlaneAt S xy0 α γ β :=
  ⟨hvalid, hcutsOff⟩

/-- Unfolding `isCuttingPlaneAt` yields flattened validity on `S` together with strict violation
at the chosen mixed point `(x0, y0)`. -/
theorem isCuttingPlaneAt_iff
    (S : Set (MixedRealPoint n p))
    (x0 : Fin n → ℝ)
    (y0 : Fin p → ℝ)
    (α : Fin n → ℝ)
    (γ : Fin p → ℝ)
    (β : ℝ) :
    isCuttingPlaneAt S (x0, y0) α γ β ↔
      is_valid_inequality ((Fin.appendEquiv n p) '' S) (Fin.append α γ) β ∧
        β < α ⬝ᵥ x0 + γ ⬝ᵥ y0 := by
  -- Read the two defining conditions from a cutting plane, and rebuild the structure conversely.
  constructor
  · intro hcut
    exact ⟨hcut.validOnSet, hcut.strictViolation⟩
  · rintro ⟨hvalid, hcutsOff⟩
    exact isCuttingPlaneAt.ofConditions S (x0, y0) α γ β hvalid hcutsOff

/-- A cutting plane at `xy0` is valid on the flattened image of `S`. -/
theorem isCuttingPlaneAt.valid
    {S : Set (MixedRealPoint n p)}
    {xy0 : MixedRealPoint n p}
    {α : Fin n → ℝ}
    {γ : Fin p → ℝ}
    {β : ℝ}
    (hcut : isCuttingPlaneAt S xy0 α γ β) :
    is_valid_inequality ((Fin.appendEquiv n p) '' S) (Fin.append α γ) β :=
  hcut.validOnSet

/-- A cutting plane at `xy0` is strictly violated by the chosen mixed point. -/
theorem isCuttingPlaneAt.cutsOff
    {S : Set (MixedRealPoint n p)}
    {xy0 : MixedRealPoint n p}
    {α : Fin n → ℝ}
    {γ : Fin p → ℝ}
    {β : ℝ}
    (hcut : isCuttingPlaneAt S xy0 α γ β) :
    β < α ⬝ᵥ xy0.1 + γ ⬝ᵥ xy0.2 :=
  hcut.strictViolation

/-- A cutting plane at `xy0` excludes `xy0` from the feasible set `S`. -/
theorem isCuttingPlaneAt.not_mem
    {S : Set (MixedRealPoint n p)}
    {xy0 : MixedRealPoint n p}
    {α : Fin n → ℝ}
    {γ : Fin p → ℝ}
    {β : ℝ}
    (hcut : isCuttingPlaneAt S xy0 α γ β) :
    xy0 ∉ S := by
  -- Membership of `xy0` puts its flattened image in the set where the cut is valid.
  intro hxy0
  have hflatValid :
      (Fin.append α γ) ⬝ᵥ (Fin.appendEquiv n p xy0) ≤ β :=
    hcut.validOnSet (Set.mem_image_of_mem (Fin.appendEquiv n p) hxy0)
  -- Splitting the flattened dot product contradicts the strict violation at `xy0`.
  have hvalid : α ⬝ᵥ xy0.1 + γ ⬝ᵥ xy0.2 ≤ β := by
    simpa [Fin.appendEquiv, dotProduct, Fin.sum_univ_add] using hflatValid
  exact (not_lt_of_ge hvalid) hcut.strictViolation

end Definition19
