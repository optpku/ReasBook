/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.CategoryTheory.Comma.Over.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

variable {E E' B : Type u} [Groupoid.{v} E] [Groupoid.{v} E'] [Groupoid.{v} B]
  (p : E ⥤ B) (p' : E' ⥤ B)

/- Definition 3.5.4: a map of coverings of `B`, from `p : E ⥤ B` to `p' : E' ⥤ B`, is a
morphism in the over-category `Over (Cat.of B)`. Equivalently, it is a functor `g : E ⥤ E'`
such that `g ⋙ p' = p`. -/
#check (Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom)
