/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

/- Definition 2.3.4: categories `C` and `D` are equivalent via the canonical mathlib notion
`C ≌ D`, which packages a forward functor, an inverse functor, and natural isomorphisms
identifying each composite with the corresponding identity functor. -/
#check (C ≌ D)

/- An equivalence of categories has a forward functor from `C` to `D`. -/
recall CategoryTheory.Equivalence.functor {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
    [Category.{v₂} D] (e : C ≌ D) : C ⥤ D

/- An equivalence of categories has an inverse functor from `D` to `C`. -/
recall CategoryTheory.Equivalence.inverse {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
    [Category.{v₂} D] (e : C ≌ D) : D ⥤ C

/- The unit of an equivalence is a natural isomorphism from the identity on `C` to the composite
of the forward and inverse functors. -/
recall CategoryTheory.Equivalence.unitIso {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
    [Category.{v₂} D] (e : C ≌ D) : 𝟭 C ≅ e.functor ⋙ e.inverse

/- The counit of an equivalence is a natural isomorphism from the composite of the inverse and
forward functors to the identity on `D`. -/
recall CategoryTheory.Equivalence.counitIso {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
    [Category.{v₂} D] (e : C ≌ D) : e.inverse ⋙ e.functor ≅ 𝟭 D
