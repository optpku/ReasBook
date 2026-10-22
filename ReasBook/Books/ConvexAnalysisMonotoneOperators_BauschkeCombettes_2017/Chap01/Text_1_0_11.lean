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

variable {X : Type u} {Y : Type v}

/-- Text 1.0.11: The inverse of a set-valued operator is the operator obtained by reversing
its graph, equivalently by sending `u : Y` to the set of `x : X` such that `u ∈ A x`. -/
def inverse (A : SetValuedOperator X Y) : SetValuedOperator Y X := fun u ↦ { x | u ∈ A x }

/- Lean can use the standard inverse surface directly here, so the source-facing owner notation
for the inverse set-valued operator is `A⁻¹`. -/
scoped postfix:max "⁻¹" => SetValuedOperator.inverse

open scoped SetValuedOperator

/-- Membership in the inverse operator is equivalent to reversing the membership relation in
the original operator. -/
@[simp] theorem mem_inverse_iff (A : SetValuedOperator X Y) (u : Y) (x : X) :
    x ∈ A⁻¹ u ↔ u ∈ A x := by
  rfl

/-- The zero set of a set-valued operator consists of the points mapped to a set containing
`0`. -/
def zeros [Zero Y] (A : SetValuedOperator X Y) : Set X := A⁻¹ 0

/-- Membership in the zero set means that `0` belongs to the corresponding value set. -/
@[simp] theorem mem_zeros_iff [Zero Y] (A : SetValuedOperator X Y) (x : X) :
    x ∈ A.zeros ↔ (0 : Y) ∈ A x := by
  rfl

end SetValuedOperator

namespace Function

variable {X : Type u} {Y : Type v}

/-- Dot-notation bridge for the inverse of a set-valued operator presented as a function
`X → Set Y`. -/
abbrev inverse (A : X → Set Y) : SetValuedOperator Y X := SetValuedOperator.inverse A

/-- Dot-notation bridge for the zero set of a set-valued operator presented as a function
`X → Set Y`. -/
abbrev zeros [Zero Y] (A : X → Set Y) : Set X := SetValuedOperator.zeros A

end Function
