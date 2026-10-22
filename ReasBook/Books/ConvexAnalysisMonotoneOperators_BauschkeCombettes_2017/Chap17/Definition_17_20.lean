/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- Definition 17.20: a vector `y` is a descent direction of a proper convex `]-∞,+∞]`-valued
function `f` at a point `x` of its effective domain when there is a positive radius `ε` such that
every step `x + α • y` with `α ∈ ]0, ε]` strictly decreases the value of `f`. -/
def IsDescentDirectionAt (f : H → Set.Ioi (⊥ : EReal)) (x y : H) : Prop :=
  x ∈ effectiveDomain f ∧
    ∃ ε > (0 : ℝ), ∀ ⦃α : ℝ⦄, α ∈ Set.Ioc (0 : ℝ) ε →
      f.asEReal (x + α • y) < f.asEReal x

end ERealFunction
