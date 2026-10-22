/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- Definition 17.1: `ξ` is the directional derivative of a proper `]-∞,+∞]`-valued function
`f` at `x` in the direction `y` when `x` belongs to the domain of `f` and the difference quotient
`(f (x + α • y) - f x) / α` tends to `ξ` as `α ↓ 0`. -/
def HasDirectionalDerivativeAt
    (f : H → Set.Ioi (⊥ : EReal)) (x y : H) (ξ : EReal) : Prop :=
  x ∈ effectiveDomain f ∧
    Filter.Tendsto
      (fun α : ℝ ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ξ)

/-- The right derivative of an `]-∞,+∞]`-valued function on `ℝ` is the directional derivative in
the direction `1`. -/
abbrev HasRightDerivativeAt
    (f : ℝ → Set.Ioi (⊥ : EReal)) (x : ℝ) (ξ : EReal) : Prop :=
  HasDirectionalDerivativeAt f x 1 ξ

/-- The left derivative of an `]-∞,+∞]`-valued function on `ℝ` is the directional derivative in
the direction `-1`; equivalently, it is the left-hand limit of the usual difference quotient. -/
abbrev HasLeftDerivativeAt
    (f : ℝ → Set.Ioi (⊥ : EReal)) (x : ℝ) (ξ : EReal) : Prop :=
  HasDirectionalDerivativeAt f x (-1) (-ξ)

end ERealFunction
