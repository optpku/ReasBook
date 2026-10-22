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
variable [HasLimit F]

/- Definition 2.6.4: the limit of a diagram `F` is the canonical object `limit F` of `C`. -/
#check (limit F : C)

/- The limit object carries its canonical cone over `F`. -/
recall limit.cone (F : D ⥤ C) [HasLimit F] : Cone F

/- Equivalently, the limit cone provides a diagram map from the constant diagram on `limit F`
to `F`. -/
#check ((limit.cone F).π : (Functor.const D).obj (limit F) ⟶ F)

/- The canonical cone on `limit F` is terminal among cones over `F`. -/
recall limit.isLimit (F : D ⥤ C) [HasLimit F] : IsLimit (limit.cone F)
