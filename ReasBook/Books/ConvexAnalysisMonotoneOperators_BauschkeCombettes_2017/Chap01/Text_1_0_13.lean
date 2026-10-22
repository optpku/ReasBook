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

/-- Text 1.0.13: a set-valued operator is at most single-valued when each value set has at most
one element, equivalently when every value over its domain is a singleton. -/
def IsAtMostSingleValued (A : SetValuedOperator X Y) : Prop :=
  ∀ x, (A x).Subsingleton

/-- Textbook reformulation of `IsAtMostSingleValued`: over the domain, every value set is a
singleton. -/
theorem isAtMostSingleValued_iff_forall_eq_singleton (A : SetValuedOperator X Y) :
    IsAtMostSingleValued A ↔ ∀ x ∈ A.dom, ∃ y, A x = ({y} : Set Y) := by
  constructor
  · intro hA x hx
    rcases (mem_dom_iff A x).mp hx with ⟨y, hy⟩
    exact ⟨y, (hA x).eq_singleton_of_mem hy⟩
  · intro hA x
    by_cases hx : x ∈ A.dom
    · rcases hA x hx with ⟨y, hy⟩
      rw [hy]
      exact Set.subsingleton_singleton
    · rw [mem_dom_iff] at hx
      rw [Set.not_nonempty_iff_eq_empty] at hx
      rw [hx]
      exact Set.subsingleton_empty

/-- The set-valued operator associated with a function `T : D → Y` sends points of `D` to the
corresponding singleton values and points outside `D` to the empty set. -/
def ofFunction (D : Set X) (T : D → Y) : SetValuedOperator X Y :=
  fun x ↦ { y | ∃ hx : x ∈ D, y = T ⟨x, hx⟩ }

/-- On points of the domain, the operator associated with a function takes the corresponding
singleton value. -/
theorem ofFunction_apply_of_mem (D : Set X) (T : D → Y) {x : X} (hx : x ∈ D) :
    ofFunction D T x = ({T ⟨x, hx⟩} : Set Y) := by
  ext y
  constructor
  · rintro ⟨hx', rfl⟩
    have hsub : (⟨x, hx'⟩ : D) = ⟨x, hx⟩ := Subtype.ext <| by rfl
    rw [hsub]
    exact Set.mem_singleton _
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hx, rfl⟩

/-- Outside the domain, the operator associated with a function takes the empty value set. -/
theorem ofFunction_apply_of_not_mem (D : Set X) (T : D → Y) {x : X} (hx : x ∉ D) :
    ofFunction D T x = (∅ : Set Y) := by
  ext y
  constructor
  · rintro ⟨hx', _⟩
    exact (hx hx').elim
  · intro hy
    exact False.elim <| Set.notMem_empty y hy

/-- The operator associated with a function on a subset is at most single-valued. -/
theorem isAtMostSingleValued_ofFunction (D : Set X) (T : D → Y) :
    IsAtMostSingleValued (ofFunction D T) := by
  intro x
  by_cases hx : x ∈ D
  · rw [ofFunction_apply_of_mem D T hx]
    exact Set.subsingleton_singleton
  · rw [ofFunction_apply_of_not_mem D T hx]
    exact Set.subsingleton_empty

end SetValuedOperator

namespace Function

variable {X : Type u} {Y : Type v}

/-- The singleton-valued set-valued operator associated with a single-valued map on the whole
space. This is the `Set.univ` specialization of `SetValuedOperator.ofFunction`. -/
abbrev toSetValuedOperator (T : X → Y) : SetValuedOperator X Y :=
  SetValuedOperator.ofFunction Set.univ (fun x : Set.univ ↦ T x)

/-- Evaluating `Function.toSetValuedOperator` recovers the corresponding singleton value set. -/
@[simp] theorem toSetValuedOperator_apply (T : X → Y) (x : X) :
    T.toSetValuedOperator x = ({T x} : Set Y) := by
  ext y
  constructor
  · rintro ⟨hx, rfl⟩
    rw [Set.mem_singleton_iff]
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨by simp, rfl⟩

end Function

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NormedField 𝕜]
variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]

/-- The singleton-valued set-valued operator associated with a bounded linear map. This is the
function-level owner `Function.toSetValuedOperator` viewed through the canonical coercion from
`ContinuousLinearMap` to functions. -/
abbrev toSetValuedOperator (T : X →L[𝕜] Y) : SetValuedOperator X Y :=
  Function.toSetValuedOperator T

end ContinuousLinearMap
