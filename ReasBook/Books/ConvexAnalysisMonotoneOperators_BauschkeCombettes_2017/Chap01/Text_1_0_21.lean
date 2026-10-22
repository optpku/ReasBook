/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v} [AddGroup X]

/-- Text 1.0.21: The translation of a set-valued operator `A` by `y` sends `x` to the value
of `A` at `x - y`. -/
def translate (A : SetValuedOperator X Y) (y : X) : SetValuedOperator X Y :=
  fun x ↦ A (x - y)

/-- Applying the translation of `A` by `y` at `x` evaluates `A` at `x - y`. -/
@[simp] theorem translate_apply (A : SetValuedOperator X Y) (y x : X) :
    translate A y x = A (x - y) :=
  rfl

/-- Membership in the translation of a set-valued operator is equivalent to membership in the
original operator after translating the input by `-y`. -/
@[simp]
theorem mem_translate_iff (A : SetValuedOperator X Y) (y x : X) (u : Y) :
    u ∈ translate A y x ↔ u ∈ A (x - y) :=
  Iff.rfl

/-- The reversal of a set-valued operator sends `x` to the value of `A` at `-x`. -/
def reverse (A : SetValuedOperator X Y) : SetValuedOperator X Y :=
  fun x ↦ A (-x)

/- Lean cannot use the textbook ASCII surface `A^∨` here. We therefore use the postfix vee token
`Aᵛ` as the direct Lean surface for operator reversal. -/
scoped postfix:max "ᵛ" => SetValuedOperator.reverse

/-- Applying the reversal of `A` at `x` evaluates `A` at `-x`. -/
@[simp] theorem reverse_apply (A : SetValuedOperator X Y) (x : X) :
    reverse A x = A (-x) :=
  rfl

/-- Membership in the reversal of a set-valued operator is equivalent to membership in the
original operator at the negated input. -/
@[simp]
theorem mem_reverse_iff (A : SetValuedOperator X Y) (x : X) (u : Y) :
    u ∈ reverse A x ↔ u ∈ A (-x) :=
  Iff.rfl

end SetValuedOperator
