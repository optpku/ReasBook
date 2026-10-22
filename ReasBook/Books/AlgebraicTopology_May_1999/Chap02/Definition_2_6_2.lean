/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (D : Type u₁) [Category.{v₁} D]
variable (C : Type u₂) [Category.{v₂} C]
variable (F G : D ⥤ C)
variable (X : C)

/- Definition 2.6.2: a morphism of `D`-shaped diagrams is the canonical natural transformation
between functors `F G : D ⥤ C`, namely `F ⟶ G`; for a fixed object `X : C`, the constant
diagram is the functor sending every object of `D` to `X` and every morphism to `𝟙 X`. -/
#check (F ⟶ G)

/- A fixed object `X : C` determines the constant `D`-shaped diagram in `C`. -/
#check ((Functor.const D).obj X)
