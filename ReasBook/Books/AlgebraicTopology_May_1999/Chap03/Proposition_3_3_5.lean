/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- Proposition 3.3.5: for a covering functor of groupoids `p : E ⥤ B`, the induced map on the
vertex group at `e` is injective. -/
-- Proof sketch: if two loops at `e` have the same image in the vertex group at `p.obj e`, view
-- them as objects of the star `Under e`. The induced star map `Under.post p` sends these two
-- objects to the same object of `Under (p.obj e)`, so injectivity from `hp.star_bijective e`
-- forces the original loops to agree.
theorem mapVertexGroup_injective (hp : Functor.IsCovering p) (e : E) :
    Function.Injective (Functor.mapVertexGroup p e) := by
  intro γ δ hγδ
  have hUnder :
      (Under.post p).obj (Under.mk γ) = (Under.post p).obj (Under.mk δ) :=
    congrArg Under.mk hγδ
  have hEq : Under.mk γ = Under.mk δ := (hp.star_bijective e).injective hUnder
  cases hEq
  rfl

end CategoryTheory.Functor.IsCovering
