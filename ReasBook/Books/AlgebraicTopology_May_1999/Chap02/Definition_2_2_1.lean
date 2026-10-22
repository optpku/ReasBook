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

/- Definition 2.2.1: a covariant functor from `C` to `D` is the canonical mathlib notion
`C ⥤ D` (equivalently, `CategoryTheory.Functor C D`), with an object map, a morphism map, and
axioms expressing preservation of identity morphisms and composition. -/
#check (C ⥤ D)
