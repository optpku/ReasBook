/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v u₁ u₂

open CategoryTheory Limits

variable (D : Type u₁) [Category.{v} D]
variable (C : Type u₂) [Category.{v} C]
variable (F : D ⥤ C)
variable [HasColimit F]

/- Definition 2.6.3: the colimit of a diagram `F` is the canonical object `colimit F` of `C`. -/
#check (colimit F : C)

/- The colimit object carries its canonical cocone over `F`. -/
recall colimit.cocone (F : D ⥤ C) [HasColimit F] : Cocone F

/- Equivalently, the colimit cocone provides a diagram map from `F` to the constant diagram on
`colimit F`. -/
#check ((colimit.cocone F).ι : F ⟶ (Functor.const D).obj (colimit F))

/- The canonical cocone on `colimit F` is initial among cocones over `F`. -/
recall colimit.isColimit (F : D ⥤ C) [HasColimit F] : IsColimit (colimit.cocone F)
