/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

/-- Text 1.0.12 (1): the domain of the inverse of a set-valued operator is the range of the
original operator. -/
@[simp] theorem dom_inverse (A : SetValuedOperator X Y) :
    A.inverse.dom = A.range := by
  ext u
  rw [mem_dom_iff, mem_range_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_inverse_iff A u x).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_inverse_iff A u x).mpr hx⟩

/-- Text 1.0.12 (2): the range of the inverse of a set-valued operator is the domain of the
original operator. -/
@[simp] theorem range_inverse (A : SetValuedOperator X Y) :
    A.inverse.range = A.dom := by
  ext x
  rw [mem_range_iff, mem_dom_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (mem_inverse_iff A u x).mp hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, (mem_inverse_iff A u x).mpr hu⟩

end SetValuedOperator
