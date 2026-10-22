/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

variable {T : Type u} [Category.{v} T] {X Y : T}
variable (C : Type u) [Category.{v} C] (x : C)

/- Definition 3.3.1: the under-category `x\C` is the canonical category `Under x`, whose
objects are morphisms with source `x` and whose morphisms are commutative triangles over `x`. -/
#check Under x

/- An object of the under-category `Under x` is given by a morphism `x ⟶ y`. -/
recall Under.mk (f : X ⟶ Y) : Under X

/- A morphism in `Under x` is a map between codomains whose triangle with the structure maps
commutes. -/
recall Under.homMk {U V : Under X} (γ : U.right ⟶ V.right)
    (hγ : U.hom ≫ γ = V.hom) : U ⟶ V

/- Every morphism in the under-category satisfies the defining commutative-triangle relation. -/
recall Under.w {U V : Under X} (γ : U ⟶ V) : U.hom ≫ γ.right = V.hom

/- The under-category inherits its category structure from the canonical mathlib instance. -/
#check (inferInstance : Category (Under x))
