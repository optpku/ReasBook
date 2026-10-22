/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic

-- Semantic recall: `lean_leansearch` surfaced `StrictAntiOn` and `StrictMonoOn`
-- as the canonical mathlib predicates for strict monotonicity on intervals, so
-- this item packages the textbook's unimodality terminology around that API.

universe u v

variable {α : Type u} {β : Type v} [Preorder α] [Preorder β]

section

/-- Chapter02 Definition 2.1.3. A function `φ : α → β` is unimodal on the interval
`Set.Icc a b` if there exists `αStar ∈ Set.Icc a b` such that `φ` is strictly decreasing on
`Set.Icc a αStar` and strictly increasing on `Set.Icc αStar b`. Such an interval `Set.Icc a b`
is then called a unimodal interval related to `φ`. -/
def unimodalOn (φ : α → β) (a b : α) : Prop :=
  ∃ αStar ∈ Set.Icc a b,
    StrictAntiOn φ (Set.Icc a αStar) ∧
      StrictMonoOn φ (Set.Icc αStar b)

/-- Expanding `unimodalOn φ a b` produces a turning point `αStar ∈ Set.Icc a b`
with strict decrease on the left subinterval and strict increase on the right subinterval. -/
theorem unimodalOn.exists_turningPoint {φ : α → β} {a b : α} (h : unimodalOn φ a b) :
    ∃ αStar ∈ Set.Icc a b,
      StrictAntiOn φ (Set.Icc a αStar) ∧
        StrictMonoOn φ (Set.Icc αStar b) :=
  h

/-- Expanding `unimodalOn φ a b` yields a turning point `αStar ∈ Set.Icc a b`
with strict decrease on the left subinterval and strict increase on the right subinterval. -/
theorem unimodalOn_iff {φ : α → β} {a b : α} :
    unimodalOn φ a b ↔
      ∃ αStar ∈ Set.Icc a b,
        StrictAntiOn φ (Set.Icc a αStar) ∧
          StrictMonoOn φ (Set.Icc αStar b) :=
  Iff.rfl

end
