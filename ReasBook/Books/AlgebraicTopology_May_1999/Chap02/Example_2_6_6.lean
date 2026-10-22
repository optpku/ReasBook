/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y Z : C}

/- Example 2.6.6: for a diagram shape `Y ← X → Z`, the corresponding colimit is a pushout; for a
parallel pair it is a coequalizer, and reversing the arrows gives pullbacks and equalizers. -/
recall pushout.isColimit (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
  IsColimit (pushout.cocone f g)

/- A coequalizer is the colimit of a parallel pair. -/
recall coequalizerIsCoequalizer (p q : X ⟶ Y) [HasCoequalizer p q] :
  IsColimit (Cofork.ofπ (coequalizer.π p q) (coequalizer.condition p q))

/- Reversing the arrows in a span gives a pullback as the corresponding limit. -/
recall pullback.isLimit (a : X ⟶ Z) (b : Y ⟶ Z) [HasPullback a b] :
  IsLimit (pullback.cone a b)

/- Reversing the arrows in a parallel pair gives an equalizer as the corresponding limit. -/
recall equalizerIsEqualizer (p q : X ⟶ Y) [HasEqualizer p q] :
  IsLimit (Fork.ofι (equalizer.ι p q) (equalizer.condition p q))
