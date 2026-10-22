/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]
variable (F G : C ⥤ D)

/- Definition 2.3.1: a natural transformation from `F` to `G` is the canonical mathlib structure
`CategoryTheory.NatTrans F G`, written `F ⟶ G`, consisting of component morphisms
`α.app A : F.obj A ⟶ G.obj A` for each object `A`, subject to the naturality condition for
every morphism `f : A ⟶ B`. -/
#check (F ⟶ G)

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {F G : C ⥤ D}

/- A natural transformation has a component morphism at each object of the source category. -/
recall NatTrans.app (α : F ⟶ G) (A : C) :
    F.obj A ⟶ G.obj A

/- The components of a natural transformation commute with the functorial action on every
morphism. -/
recall NatTrans.naturality (α : F ⟶ G) {A B : C} (f : A ⟶ B) :
    F.map f ≫ α.app B = α.app A ≫ G.map f
