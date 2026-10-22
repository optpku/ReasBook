/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Logic.ExistsUnique

public section

universe u v

variable {Q : Type u} {Y : Type v}

/-- Assumption 6.3-extra-2. The datum `F qTrue` has no second preimage: if `F q = F qTrue`,
then necessarily `q = qTrue`. This packages the local uniqueness assumption `(6.37)` as a
reusable predicate on `F` and the distinguished point `qTrue`. -/
def IsIdentifiableAt (F : Q → Y) (qTrue : Q) : Prop :=
  ∀ ⦃q : Q⦄, F q = F qTrue → q = qTrue

namespace IsIdentifiableAt

/-- Recover the distinguished point from equality of images under `F`. -/
theorem eq_of_apply_eq {F : Q → Y} {qTrue q : Q} (h : IsIdentifiableAt F qTrue)
    (hq : F q = F qTrue) : q = qTrue :=
  h hq

/-- A point distinct from `qTrue` cannot map to `F qTrue` under an identifiable datum. -/
theorem ne_apply_of_ne {F : Q → Y} {qTrue q : Q} (h : IsIdentifiableAt F qTrue)
    (hq : q ≠ qTrue) : F q ≠ F qTrue :=
  fun hF ↦ hq (h hF)

/-- Under identifiability at `qTrue`, the fiber over `F qTrue` is exactly `{qTrue}`. -/
theorem preimage_eq_singleton {F : Q → Y} {qTrue : Q} (h : IsIdentifiableAt F qTrue) :
    F ⁻¹' {F qTrue} = ({qTrue} : Set Q) := by
  ext q
  constructor
  · intro hq
    rw [Set.mem_singleton_iff]
    exact h (by simpa using hq)
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    rw [hq]
    simp

end IsIdentifiableAt

/-- The source clause `(6.37)` is equivalent to `IsIdentifiableAt F qTrue`. -/
theorem isIdentifiableAt_iff_ne_apply_ne {F : Q → Y} {qTrue : Q} :
    IsIdentifiableAt F qTrue ↔ ∀ ⦃q : Q⦄, q ≠ qTrue → F q ≠ F qTrue := by
  constructor
  · intro h q hq
    exact h.ne_apply_of_ne hq
  · intro h q hF
    by_contra hq
    exact h hq hF

/-- `IsIdentifiableAt F qTrue` is equivalent to the fiber over `F qTrue` being `{qTrue}`. -/
theorem isIdentifiableAt_iff_preimage_eq_singleton {F : Q → Y} {qTrue : Q} :
    IsIdentifiableAt F qTrue ↔ F ⁻¹' {F qTrue} = ({qTrue} : Set Q) := by
  constructor
  · exact IsIdentifiableAt.preimage_eq_singleton
  · intro h q hq
    have hq_mem : q ∈ F ⁻¹' {F qTrue} := by
      simpa using hq
    have : q ∈ ({qTrue} : Set Q) := by
      simpa [h] using hq_mem
    simpa using this

/-- `IsIdentifiableAt F qTrue` is equivalent to `qTrue` being the unique preimage of
`F qTrue`. -/
theorem isIdentifiableAt_iff_existsUnique {F : Q → Y} {qTrue : Q} :
    IsIdentifiableAt F qTrue ↔ ∃! q : Q, F q = F qTrue := by
  constructor
  · intro h
    exact ⟨qTrue, rfl, fun q hq ↦ h hq⟩
  · intro h q hq
    exact h.unique hq rfl

namespace Function.Injective

/-- Global injectivity of `F` implies identifiability at every distinguished point. -/
theorem isIdentifiableAt {F : Q → Y} (hF : Function.Injective F) (qTrue : Q) :
    IsIdentifiableAt F qTrue :=
  fun {_} hq ↦ hF hq

end Function.Injective
