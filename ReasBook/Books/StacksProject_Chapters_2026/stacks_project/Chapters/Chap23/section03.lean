module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.DividedPowers.DPMorphism

@[expose] public section

open CategoryTheory
open DividedPowers

universe u

/-- A divided power ring is a commutative ring equipped with an ideal carrying divided powers. -/
structure DividedPowerRing where
  /-- The underlying commutative ring. -/
  carrier : Type u
  /-- The commutative ring structure on the underlying type. -/
  [commRing : CommRing carrier]
  /-- The distinguished ideal with divided powers. -/
  ideal : Ideal carrier
  /-- The divided power structure on the distinguished ideal. -/
  dividedPowers : DividedPowers ideal

attribute [instance] DividedPowerRing.commRing

instance : CoeSort DividedPowerRing (Type u) := ⟨DividedPowerRing.carrier⟩

namespace DividedPowerRing

/-- Morphisms of divided power rings are the canonical bundled divided power morphisms. -/
instance : Category DividedPowerRing where
  Hom A B := DPMorphism A.dividedPowers B.dividedPowers
  id A := DPMorphism.id A.dividedPowers
  comp f g := DPMorphism.comp g f
  id_comp := by
    intro A B f
    ext x
    rfl
  comp_id := by
    intro A B f
    ext x
    rfl
  assoc := by
    intro A B C D f g h
    ext x
    rfl

end DividedPowerRing
