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

/-- Text 1.0.10: The domain of a set-valued operator `A` is the set of points `x` for which
`A x` is nonempty. -/
def dom (A : SetValuedOperator X Y) : Set X := { x | (A x).Nonempty }

/-- The range of a set-valued operator `A` is the union of all of its value sets. -/
def range (A : SetValuedOperator X Y) : Set Y := ⋃ x, A x

/-- A point belongs to the domain exactly when the corresponding value set is nonempty. -/
theorem mem_dom_iff (A : SetValuedOperator X Y) (x : X) :
    x ∈ A.dom ↔ (A x).Nonempty := by
  rfl

/-- A point belongs to the range exactly when it lies in the value set `A x` for some `x`. -/
theorem mem_range_iff (A : SetValuedOperator X Y) (y : Y) :
    y ∈ A.range ↔ ∃ x, y ∈ A x := by
  simp [range]

end SetValuedOperator
