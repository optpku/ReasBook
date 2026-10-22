/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

open scoped BigOperators

universe u v

open List

namespace Cycle

variable {X : Type u}

/-- Cyclic reduction of a representative list is invariant under cyclic permutation. -/
theorem isCyclicallyReduced_iff_of_isRotated {L₁ L₂ : List (X × Bool)} (h : L₁ ~r L₂) :
    FreeGroup.IsCyclicallyReduced L₁ ↔ FreeGroup.IsCyclicallyReduced L₂ := sorry

/-- A cyclically ordered word is reduced when one, equivalently every, representative list is a
cyclically reduced free-group word. -/
def IsCyclicallyReduced (w : Cycle (X × Bool)) : Prop :=
  Quotient.liftOn w FreeGroup.IsCyclicallyReduced fun _ _ h ↦
    propext (isCyclicallyReduced_iff_of_isRotated h)

@[simp] theorem isCyclicallyReduced_coe_iff {L : List (X × Bool)} :
    IsCyclicallyReduced (L : Cycle (X × Bool)) ↔ FreeGroup.IsCyclicallyReduced L :=
  Iff.rfl

/-- Cyclic permutation does not change the conjugacy class of the represented free-group word. -/
theorem conjClasses_mk_eq_of_isRotated {L₁ L₂ : List (X × Bool)} (h : L₁ ~r L₂) :
    ConjClasses.mk (FreeGroup.mk L₁) = ConjClasses.mk (FreeGroup.mk L₂) := by
  rw [List.isRotated_iff_mod] at h
  rcases h with ⟨n, -, rfl⟩
  let A : FreeGroup X := FreeGroup.mk (L₁.take (n % L₁.length))
  let B : FreeGroup X := FreeGroup.mk (L₁.drop (n % L₁.length))
  have hsplit : FreeGroup.mk L₁ = A * B := by
    dsimp [A, B]
    simpa only [FreeGroup.mul_mk] using
      congrArg FreeGroup.mk (List.take_append_drop (n % L₁.length) L₁).symm
  have hrotate : FreeGroup.mk (L₁.rotate n) = B * A := by
    have hrotateList : L₁.rotate n = L₁.drop (n % L₁.length) ++ L₁.take (n % L₁.length) :=
      List.rotate_eq_drop_append_take_mod
    dsimp [A, B]
    simpa [FreeGroup.mul_mk] using
      congrArg FreeGroup.mk hrotateList
  apply ConjClasses.mk_eq_mk_iff_isConj.2
  rw [isConj_iff]
  refine ⟨A⁻¹, ?_⟩
  calc
    A⁻¹ * FreeGroup.mk L₁ * (A⁻¹)⁻¹ = A⁻¹ * (A * B) * A := by rw [hsplit, inv_inv]
    _ = B * A := by group
    _ = FreeGroup.mk (L₁.rotate n) := hrotate.symm

end Cycle

/-- Definition 1-4-17: a cyclic word on the alphabet `X` is a cyclically ordered list of letters
from `X^{±1}`, understood by default to be reduced. The owner abstraction is the rotation quotient
`List.Cycle (X × Bool)`, with cyclic reduction imposed as a predicate on the quotient. -/
abbrev CyclicWord (X : Type u) :=
  { w : Cycle (X × Bool) // w.IsCyclicallyReduced }

namespace CyclicWord

variable {X : Type u}
variable {ι : Type v}

/-- The length of a cyclic word is the length of any representative list. -/
abbrev length (w : CyclicWord X) : ℕ :=
  w.1.length

@[simp] theorem length_mk {L : List (X × Bool)} (hL : (L : Cycle (X × Bool)).IsCyclicallyReduced) :
    length ⟨(L : Cycle (X × Bool)), hL⟩ = L.length :=
  rfl

/-- Forgetting signs yields the cyclic sequence of underlying letters. -/
abbrev letters (w : CyclicWord X) : Cycle X :=
  w.1.map Prod.fst

/-- The unsigned support of a cyclic word. -/
abbrev support [DecidableEq X] (w : CyclicWord X) : Finset X :=
  w.letters.toFinset

/-- A cyclic word has full support when every basis letter occurs, ignoring sign. -/
abbrev HasFullSupport (w : CyclicWord X) : Prop :=
  ∀ x : X, x ∈ w.letters

/-- A reduced cyclic word determines the conjugacy class of the corresponding free-group element. -/
def toConjClasses (w : CyclicWord X) : ConjClasses (FreeGroup X) :=
  Quotient.liftOn w.1 (ConjClasses.mk ∘ FreeGroup.mk) fun _ _ h ↦
    Cycle.conjClasses_mk_eq_of_isRotated h

@[simp] theorem toConjClasses_mk {L : List (X × Bool)}
    (hL : (L : Cycle (X × Bool)).IsCyclicallyReduced) :
    toConjClasses ⟨L, hL⟩ = ConjClasses.mk (FreeGroup.mk L) :=
  rfl

/-- Reduced cyclic words are in one-to-one correspondence with conjugacy classes in the free
group on the same alphabet. -/
private theorem toConjClasses_bijective : Function.Bijective (toConjClasses : CyclicWord X →
    ConjClasses (FreeGroup X)) := sorry

/-- The canonical equivalence between reduced cyclic words and conjugacy classes in the free group
on the same alphabet. -/
noncomputable def conjClassesEquiv : CyclicWord X ≃ ConjClasses (FreeGroup X) :=
  Equiv.ofBijective toConjClasses toConjClasses_bijective

/-- An automorphism of the free group acts on cyclic words via the canonical action on conjugacy
classes. -/
noncomputable def map (α : MulAut (FreeGroup X)) : CyclicWord X → CyclicWord X :=
  conjClassesEquiv.symm ∘ ConjClasses.map α.toMonoidHom ∘ conjClassesEquiv

@[simp] theorem toConjClasses_map (α : MulAut (FreeGroup X)) (w : CyclicWord X) :
    toConjClasses (map α w) = ConjClasses.map α.toMonoidHom (toConjClasses w) := by
  change conjClassesEquiv (map α w) = ConjClasses.map α.toMonoidHom (conjClassesEquiv w)
  simp [map, conjClassesEquiv]

/-- The canonical `Aut(F(X))`-action on cyclic words over `X`, transported from conjugacy
classes. -/
@[reducible] noncomputable instance : MulAction (MulAut (FreeGroup X)) (CyclicWord X) where
  smul α w := map α w
  one_smul w := by
    apply toConjClasses_bijective.1
    change toConjClasses (map 1 w) = toConjClasses w
    rw [toConjClasses_map]
    obtain ⟨a, ha⟩ := ConjClasses.exists_rep (toConjClasses w)
    rw [← ha]
    rfl
  mul_smul α β w := by
    apply toConjClasses_bijective.1
    change toConjClasses (map (α * β) w) = toConjClasses (map α (map β w))
    rw [toConjClasses_map, toConjClasses_map, toConjClasses_map]
    obtain ⟨a, ha⟩ := ConjClasses.exists_rep (toConjClasses w)
    rw [← ha]
    rfl

/-- The total cyclic length of a finite family of cyclic words. -/
def totalLength [Fintype ι] (w : ι → CyclicWord X) : ℕ :=
  ∑ i, (w i).length

end CyclicWord
