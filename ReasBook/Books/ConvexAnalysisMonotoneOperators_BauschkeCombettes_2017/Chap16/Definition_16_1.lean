/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section Subdifferential

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The canonical codomain bridge from `]-∞,+∞]`-valued functions to `EReal`-valued functions. -/
instance {X : Type*} : CoeTC (X → Set.Ioi (⊥ : EReal)) (X → EReal) := ⟨Function.asEReal⟩

/-- Definition 16.1: the subdifferential of a function with canonical `EReal`-valued codomain
coercion sends `x` to the set of vectors `u` such that the affine function
`y ↦ ⟪y - x, u⟫ + f x` minorizes `f` everywhere. In particular, the same owner surface applies
directly to both `EReal`-valued and `]-∞,+∞]`-valued functions. -/
def subdifferential {α : Type*} [CoeTC α EReal] (f : H → α) : SetValuedOperator H H :=
  fun x ↦ {u | ∀ y : H, (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal)}

scoped prefix:100 "∂ " => ERealFunction.subdifferential

/-- The function `f` is subdifferentiable at `x` when `x` belongs to the domain of the
subdifferential operator. -/
abbrev SubdifferentiableAt {α : Type*} [CoeTC α EReal] (f : H → α) (x : H) : Prop :=
  x ∈ SetValuedOperator.dom (∂ f)

/-- Subdifferentiability at `x` is membership of `x` in the domain of the subdifferential
operator. -/
@[simp] theorem subdifferentiableAt_iff_mem_dom
    {α : Type*} [CoeTC α EReal] (f : H → α) (x : H) :
    SubdifferentiableAt f x ↔ x ∈ SetValuedOperator.dom (∂ f) :=
  Iff.rfl

/-- Membership in the subdifferential is exactly the global affine-minorant inequality. -/
@[simp] theorem mem_subdifferential_iff
    {α : Type*} [CoeTC α EReal] (f : H → α) (x u : H) :
    u ∈ subdifferential f x ↔
      ∀ y : H, (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) :=
  Iff.rfl

end Subdifferential

end

end ERealFunction
