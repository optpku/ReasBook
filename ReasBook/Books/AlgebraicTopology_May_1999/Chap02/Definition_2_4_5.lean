/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

namespace CategoryTheory.HomRel

variable {C : Type u} [Category.{v} C] (r : HomRel C)

/-- Definition 2.4.5: a morphism is a homotopy equivalence if it admits a two-sided inverse up to
the homotopy relation `r`. This always becomes an isomorphism after passing to the quotient
category `CategoryTheory.Quotient r`, and the converse holds when `r` is a congruence. -/
def IsHomotopyEquivalence {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, r (g ≫ f) (𝟙 Y) ∧ r (f ≫ g) (𝟙 X)

namespace IsHomotopyEquivalence

-- Proof sketch: if `g` is a homotopy inverse for `f`, then `Quotient.sound` turns the relations
-- `g ≫ f ∼ 𝟙` and `f ≫ g ∼ 𝟙` into equalities in `CategoryTheory.Quotient r`, so the images of
-- `f` and `g` are inverse morphisms there.
/-- A homotopy equivalence becomes an isomorphism in the quotient category. -/
theorem isIso_map {X Y : C} {f : X ⟶ Y} (hf : IsHomotopyEquivalence r f) :
    IsIso ((Quotient.functor r).map f) := by
  rcases hf with ⟨g, hgf, hfg⟩
  refine IsIso.mk' ⟨(Quotient.functor r).map g, ?_, ?_⟩
  · calc
      (Quotient.functor r).map g ≫ (Quotient.functor r).map f
          = (Quotient.functor r).map (g ≫ f) := by simp
      _ = (Quotient.functor r).map (𝟙 Y) := by
        simpa using CategoryTheory.Quotient.sound r hgf
      _ = 𝟙 _ := by simp
  · calc
      (Quotient.functor r).map f ≫ (Quotient.functor r).map g
          = (Quotient.functor r).map (f ≫ g) := by simp
      _ = (Quotient.functor r).map (𝟙 X) := by
        simpa using CategoryTheory.Quotient.sound r hfg
      _ = 𝟙 _ := by simp

/-- If `r` is a congruence, any morphism whose image in the quotient is invertible is already a
homotopy equivalence for `r`. -/
theorem of_isIso_map [Congruence r] {X Y : C} {f : X ⟶ Y}
    (hf : IsIso ((Quotient.functor r).map f)) :
    IsHomotopyEquivalence r f := by
  obtain ⟨g, hg : (Quotient.functor r).map g = inv ((Quotient.functor r).map f)⟩ :=
    (Quotient.functor r).map_surjective (inv ((Quotient.functor r).map f))
  refine ⟨g, ?_, ?_⟩
  · rw [← Quotient.functor_map_eq_iff r (g ≫ f) (𝟙 Y)]
    calc
      (Quotient.functor r).map (g ≫ f)
          = (Quotient.functor r).map g ≫ (Quotient.functor r).map f := by simp
      _ = inv ((Quotient.functor r).map f) ≫ (Quotient.functor r).map f := by simp [hg]
      _ = 𝟙 _ := by simp
      _ = (Quotient.functor r).map (𝟙 Y) := by simp
  · rw [← Quotient.functor_map_eq_iff r (f ≫ g) (𝟙 X)]
    calc
      (Quotient.functor r).map (f ≫ g)
          = (Quotient.functor r).map f ≫ (Quotient.functor r).map g := by simp
      _ = (Quotient.functor r).map f ≫ inv ((Quotient.functor r).map f) := by simp [hg]
      _ = 𝟙 _ := by simp
      _ = (Quotient.functor r).map (𝟙 X) := by simp

/-- For a congruence relation, homotopy equivalences are exactly the morphisms that become
isomorphisms in the quotient category. -/
theorem iff_isIso_map [Congruence r] {X Y : C} {f : X ⟶ Y} :
    IsHomotopyEquivalence r f ↔ IsIso ((Quotient.functor r).map f) :=
  ⟨isIso_map r, of_isIso_map r⟩

end IsHomotopyEquivalence

end CategoryTheory.HomRel
