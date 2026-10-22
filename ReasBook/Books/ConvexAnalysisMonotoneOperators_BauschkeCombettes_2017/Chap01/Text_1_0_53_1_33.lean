/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u v

/-
Text 1.0.53 (1.33): the source’s notion of lower semicontinuity at a point is the canonical
predicate `LowerSemicontinuousAt`; the textbook’s extended-real-valued case is a specialization of
this mathlib definition.
-/
recall LowerSemicontinuousAt
    {X : Type u} {Y : Type v} [TopologicalSpace X] [Preorder Y] (f : X → Y) (x : X) : Prop

/-- Text 1.0.53 (1.33), neighborhood form: lower semicontinuity of an extended-real-valued
function at a point is equivalently the condition that every strict lower bound of `f x` remains a
strict lower bound of `f` on some neighborhood of `x`. -/
theorem lowerSemicontinuousAt_iff_exists_mem_nhds_forall_lt
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    LowerSemicontinuousAt f x ↔
      ∀ ξ, ξ < f x → ∃ V : Set X, V ∈ 𝓝 x ∧ ∀ y ∈ V, ξ < f y := by
  rw [lowerSemicontinuousAt_iff]
  constructor
  · intro h ξ hξ
    have hlt : {y : X | ξ < f y} ∈ 𝓝 x := h ξ hξ
    rcases
        (Filter.exists_mem_subset_iff :
          (∃ V ∈ 𝓝 x, V ⊆ {y : X | ξ < f y}) ↔ {y : X | ξ < f y} ∈ 𝓝 x).2 hlt with
      ⟨V, hV, hltV⟩
    exact ⟨V, hV, fun y hy ↦ hltV hy⟩
  · intro h ξ hξ
    rcases h ξ hξ with ⟨V, hV, hlt⟩
    exact mem_of_superset hV (fun y hy ↦ hlt y hy)
