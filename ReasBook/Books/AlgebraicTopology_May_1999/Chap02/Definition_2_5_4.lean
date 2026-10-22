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

/- Definition 2.5.4: a skeleton of a category `C` is expressed by the canonical predicate
`IsSkeletonOf F`, saying that `F : D ⥤ C` exhibits `D` as a skeletal full
subcategory of `C`, equivalently one containing exactly one object from each isomorphism class
of objects of `C`. -/
recall IsSkeletonOf (F : D ⥤ C) : Prop
