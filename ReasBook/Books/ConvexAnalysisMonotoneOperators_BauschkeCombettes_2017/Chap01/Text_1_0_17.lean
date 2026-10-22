/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v} [AddCommGroup Y] [Module ℝ Y]

/-- Membership in `(A + r • B) x` means being representable as `u + r • v` with
`u ∈ A x` and `v ∈ B x`. -/
theorem mem_add_smul_iff (A B : SetValuedOperator X Y) (r : ℝ) (x : X) (w : Y) :
    w ∈ (A + r • B) x ↔ ∃ u ∈ A x, ∃ v ∈ B x, w = u + r • v := by
  constructor
  · intro hw
    -- Expand membership in the pointwise sum, then unpack the scalar-multiple witness.
    rw [add_smul_apply, Set.mem_add] at hw
    rcases hw with ⟨u, hu, z, hz, huz⟩
    rw [Set.mem_smul_set] at hz
    rcases hz with ⟨v, hv, hvz⟩
    refine ⟨u, hu, v, hv, ?_⟩
    simpa [hvz] using huz.symm
  · rintro ⟨u, hu, v, hv, rfl⟩
    -- Rebuild membership by choosing `u` from `A x` and `r • v` from `r • B x`.
    rw [add_smul_apply, Set.mem_add]
    refine ⟨u, hu, r • v, ?_, rfl⟩
    rw [Set.mem_smul_set]
    exact ⟨v, hv, rfl⟩

/-- Helper for Text 1.0.17: `(A + r • B) x` is nonempty exactly when both input value sets
are nonempty. -/
-- Proof sketch: convert nonemptiness to a witness in the linear combination, use
-- `mem_add_smul_iff` to extract witnesses in `A x` and `B x`, and reverse the argument
-- by building the element `u + r • v`.
private lemma add_smul_nonempty_iff
    (A B : SetValuedOperator X Y) (r : ℝ) (x : X) :
    ((A + r • B) x).Nonempty ↔ (A x).Nonempty ∧ (B x).Nonempty := by
  constructor
  · rintro ⟨w, hw⟩
    -- Any witness in the linear combination decomposes into witnesses from both source sets.
    rw [mem_add_smul_iff] at hw
    rcases hw with ⟨u, hu, v, hv, _⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    -- Given witnesses in both source sets, their linear combination is a witness upstairs.
    refine ⟨u + r • v, ?_⟩
    rw [mem_add_smul_iff]
    exact ⟨u, hu, v, hv, rfl⟩

/-- Text 1.0.17 (1): the graph of the pointwise linear combination `A + λ B` consists of the
pairs `(x, u + λ • v)` coming from matching graph points of `A` and `B`. -/
-- Proof sketch: use `Set.ext`, unfold `SetValuedOperator.graph`, apply
-- `mem_add_smul_iff`, and rewrite the resulting membership conditions using
-- `SetValuedOperator.mem_graph_iff`.
theorem graph_add_smul (A B : SetValuedOperator X Y) (r : ℝ) :
    (A + r • B).graph =
      { xw | ∃ u v, (xw.1, u) ∈ A.graph ∧ (xw.1, v) ∈ B.graph ∧ xw.2 = u + r • v } := by
  ext xw
  constructor
  · intro hxw
    -- A graph point is exactly a point whose second coordinate lies in the combined value set.
    rw [mem_graph_iff, mem_add_smul_iff] at hxw
    rcases hxw with ⟨u, hu, v, hv, hEq⟩
    exact ⟨u, v, (mem_graph_iff A xw.1 u).2 hu, (mem_graph_iff B xw.1 v).2 hv, hEq⟩
  · intro hxw
    -- Conversely, the witness description gives membership in the value set, hence in the graph.
    rcases hxw with ⟨u, v, hu, hv, hEq⟩
    rw [mem_graph_iff, mem_add_smul_iff]
    exact ⟨u, (mem_graph_iff A xw.1 u).1 hu, v, (mem_graph_iff B xw.1 v).1 hv, hEq⟩

/-- Text 1.0.17 (2): the domain of the pointwise linear combination `A + λ B` is
`A.dom ∩ B.dom`. -/
@[simp] theorem dom_add_smul (A B : SetValuedOperator X Y) (r : ℝ) :
    (A + r • B).dom = A.dom ∩ B.dom := by
  ext x
  rw [Set.mem_inter_iff, mem_dom_iff, mem_dom_iff, mem_dom_iff]
  rw [add_smul_nonempty_iff]

end SetValuedOperator
