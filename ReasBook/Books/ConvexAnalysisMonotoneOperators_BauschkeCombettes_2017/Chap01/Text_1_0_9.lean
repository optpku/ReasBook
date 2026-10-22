/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace SetValuedOperator

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Text 1.0.9: The image `A(C)` of a set `C` under a set-valued operator `A` is the union of
the value sets `A x` for `x ∈ C`. -/
def image (A : SetValuedOperator X Y) (C : Set X) : Set Y := ⋃ x ∈ C, A x

/-- Membership in the image of a set under a set-valued operator is equivalent to belonging to
one of the value sets over that set. -/
@[simp] theorem mem_image (A : SetValuedOperator X Y) (C : Set X) (y : Y) :
    y ∈ A.image C ↔ ∃ x ∈ C, y ∈ A x := by
  simp [image]

/-- The composition of set-valued operators sends `x` to the image of the value set `A x` under
`B`. -/
def comp (B : SetValuedOperator Y Z) (A : SetValuedOperator X Y) : SetValuedOperator X Z :=
  fun x ↦ B.image (A x)

/-- Evaluating the composition of set-valued operators amounts to taking the image of the value
set under the second operator. -/
@[simp] theorem comp_apply (B : SetValuedOperator Y Z) (A : SetValuedOperator X Y) (x : X) :
    B.comp A x = B.image (A x) :=
  rfl

/-- Membership in the composition of set-valued operators is equivalent to the existence of an
intermediate point in the first value set whose image under the second operator contains the
element. -/
@[simp] theorem mem_comp (B : SetValuedOperator Y Z) (A : SetValuedOperator X Y) (x : X) (z : Z) :
    z ∈ B.comp A x ↔ ∃ y ∈ A x, z ∈ B y := by
  simp [comp]

end SetValuedOperator
