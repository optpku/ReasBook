/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

variable {A : SetValuedOperator X Y}

/-- Text 1.0.14: a selection of `A` is an operator `T : A.dom → Y` such that `T x ∈ A x`
for every `x ∈ A.dom`. -/
abbrev Selection (A : SetValuedOperator X Y) : Type (max u v) := ∀ x : A.dom, A x

/-- A selection takes each point of the domain of `A` to a point of the corresponding value
set. -/
@[simp] theorem selection_apply_mem (T : Selection A) (x : A.dom) :
    (T x : Y) ∈ A x :=
  (T x).property

end SetValuedOperator
