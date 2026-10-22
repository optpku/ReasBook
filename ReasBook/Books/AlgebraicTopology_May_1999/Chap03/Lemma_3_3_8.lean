/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Tactic.Recall
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/- Lemma 3.3.8: the fiber translation assignment `T(p)` of Definition 3.3.7 is the canonical
functor sending each object of the base groupoid to its fiber and each morphism to the induced
translation map between fibers. -/
recall fiberTranslationFunctor (hp : Functor.IsCovering p) : B ⥤ Type u₁

end CategoryTheory.Functor.IsCovering
