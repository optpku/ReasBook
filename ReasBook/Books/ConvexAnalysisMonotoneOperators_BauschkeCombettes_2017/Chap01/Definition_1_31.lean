/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

namespace ERealFunction

variable {X : Type u} [TopologicalSpace X]

/-- The lower semicontinuous minorants of an extended-real-valued function. -/
def lowerSemicontinuousMinorants (f : X → EReal) : Set (X → EReal) :=
  {g | LowerSemicontinuous g ∧ g ≤ f}

/-- A function is a lower semicontinuous minorant of `f` exactly when it is lower semicontinuous
and lies below `f` pointwise. -/
theorem mem_lowerSemicontinuousMinorants_iff (f g : X → EReal) :
    g ∈ lowerSemicontinuousMinorants f ↔ LowerSemicontinuous g ∧ g ≤ f :=
  Iff.rfl

/-- Definition 1.31: the lower semicontinuous envelope of `f` is the supremum, in the function
lattice, of all lower semicontinuous extended-real-valued minorants of `f`. -/
noncomputable def lowerSemicontinuousEnvelope (f : X → EReal) : X → EReal :=
  sSup (lowerSemicontinuousMinorants f)

/-- The lower semicontinuous envelope is computed pointwise as the supremum of the values of all
lower semicontinuous minorants of `f` at that point. -/
theorem lowerSemicontinuousEnvelope_apply (f : X → EReal) (x : X) :
    lowerSemicontinuousEnvelope f x =
      sSup ((fun g : X → EReal ↦ g x) '' lowerSemicontinuousMinorants f) := by
  change sSup (lowerSemicontinuousMinorants f) x =
    sSup ((fun g : X → EReal ↦ g x) '' lowerSemicontinuousMinorants f)
  exact sSup_apply_eq_sSup_image

end ERealFunction
