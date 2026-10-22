/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- The unit proximal objective at `x`, whose minimizers are the proximal points of `f` at `x`. -/
noncomputable def proximalObjective (f : H → Set.Ioi (⊥ : EReal)) (x : H) : H → EReal :=
  fun y ↦ (f y : EReal) + ((((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal))

/-- Definition 12.23: the proximal points of `f` at `x` are the minimizers of the regularized
objective `y ↦ f y + (1 / 2) ‖x - y‖^2`. -/
def proximalPoints (f : H → Set.Ioi (⊥ : EReal)) (x : H) : Set H :=
  Argmin (proximalObjective f x)

/-- Definition 12.23: `p` is a proximal point of `f` at `x` when it belongs to the argmin set of
the regularized objective at `x`. -/
abbrev IsProxPoint (f : H → Set.Ioi (⊥ : EReal)) (x p : H) : Prop :=
  p ∈ proximalPoints f x

-- Proof sketch: unfold `IsProxPoint`, then rewrite the unit Moreau envelope with
-- `moreauEnvelope_apply` at the parameter `γ = 1`.
/-- A point is proximal exactly when it realizes the value of the unit Moreau envelope. -/
theorem isProxPoint_iff_moreauEnvelope_eq (f : H → Set.Ioi (⊥ : EReal)) (x p : H) :
    IsProxPoint f x p ↔
      ({}^[⟨(1 : ℝ), by simp [Set.mem_Ioi]⟩] f) x =
        (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := sorry

/-- A function has a unique proximal point at every base point when the regularized objective
`y ↦ f y + (1 / 2) ‖x - y‖^2` admits a unique minimizer for every `x`. -/
def HasUniqueProxPoint (f : H → Set.Ioi (⊥ : EReal)) : Prop :=
  ∀ x : H, ∃! p : H, p ∈ proximalPoints f x

/-- The proximity operator attached to a function with unique proximal points sends `x` to its
unique proximal point. -/
noncomputable def proximityOperator (f : H → Set.Ioi (⊥ : EReal)) (hf : HasUniqueProxPoint f) :
    H → H :=
  fun x ↦ (hf x).choose

-- Proof sketch: unfold `proximityOperator` and use the defining `ExistsUnique` witness from
-- `HasUniqueProxPoint`.
/-- The value of the proximity operator is a proximal point. -/
theorem proximityOperator_isProxPoint (f : H → Set.Ioi (⊥ : EReal))
    (hf : HasUniqueProxPoint f) (x : H) :
    IsProxPoint f x (proximityOperator f hf x) := sorry

-- Proof sketch: apply the uniqueness clause in `hf x` to the given proximal point and to
-- `proximityOperator f hf x`.
/-- Any proximal point at `x` coincides with the value of the proximity operator at `x`. -/
theorem eq_proximityOperator_of_isProxPoint (f : H → Set.Ioi (⊥ : EReal))
    (hf : HasUniqueProxPoint f) {x p : H} (hp : IsProxPoint f x p) :
    p = proximityOperator f hf x := sorry

end ERealFunction
