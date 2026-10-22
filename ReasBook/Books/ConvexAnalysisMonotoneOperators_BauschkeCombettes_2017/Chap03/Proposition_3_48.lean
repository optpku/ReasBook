/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section Topological

variable {E : Type u} [TopologicalSpace E]

/-- Closedness gives the easy inclusion
`closure (C ∩ interior D) ⊆ C ∩ closure D`. -/
private lemma closure_inter_interior_subset_inter_closure
    {C D : Set E} (hC_closed : IsClosed C) :
    closure (C ∩ interior D) ⊆ C ∩ closure D := by
  -- First place `C ∩ interior D` inside the closed target set.
  refine closure_minimal ?_ (hC_closed.inter isClosed_closure)
  intro z hz
  exact ⟨hz.1, interior_subset_closure hz.2⟩

end Topological

section TopologicalVector

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Once a point of `C ∩ interior D` is fixed, every point of
`C ∩ closure D` belongs to `closure (C ∩ interior D)`. -/
private lemma mem_closure_inter_interior_of_mem_inter_closure
    {C D : Set E} (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    {x y : E} (hx : x ∈ C ∩ interior D) (hy : y ∈ C ∩ closure D) :
    y ∈ closure (C ∩ interior D) := by
  -- The geometric core is that the open segment from `x` to `y` stays in `C ∩ interior D`.
  have hsubset : openSegment ℝ x y ⊆ C ∩ interior D := by
    intro z hz
    refine ⟨?_, ?_⟩
    · exact hC_conv.openSegment_subset hx.1 hy.1 hz
    · exact hD_conv.openSegment_interior_closure_subset_interior hx.2 hy.2 hz
  -- The endpoint `y` lies in the segment, hence in the closure of the open segment.
  have hy_mem : y ∈ closure (openSegment ℝ x y) :=
    segment_subset_closure_openSegment (right_mem_segment ℝ x y)
  -- Monotonicity of closure transfers this to the desired closure.
  exact closure_mono hsubset hy_mem

-- Proof sketch: The inclusion `closure (C ∩ interior D) ⊆ C ∩ closure D` follows from
-- `interior D ⊆ closure D` and closedness of `C`. For the reverse inclusion, fix
-- `x ∈ C ∩ interior D` and `y ∈ C ∩ closure D`; convexity puts the points
-- `α • x + (1 - α) • y` in `C ∩ interior D` for `0 < α ≤ 1`, and these converge to `y`.
/-- Proposition 3.48: if `C` and `D` are convex subsets of a real topological vector space, `C`
is closed, and `C ∩ interior D` is nonempty, then the closure of `C ∩ interior D` is
`C ∩ closure D`. -/
theorem closure_inter_interior_eq_inter_closure_of_nonempty
    {C D : Set E}
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hC_closed : IsClosed C) (h_nonempty : (C ∩ interior D).Nonempty) :
    closure (C ∩ interior D) = C ∩ closure D := by
  refine subset_antisymm ?_ ?_
  · -- The forward inclusion is the closed-set argument from the textbook proof.
    exact closure_inter_interior_subset_inter_closure hC_closed
  · rcases h_nonempty with ⟨x, hx⟩
    -- Fix one point of `C ∩ interior D`; every `y ∈ C ∩ closure D` is reached as a segment endpoint.
    intro y hy
    exact mem_closure_inter_interior_of_mem_inter_closure hC_conv hD_conv hx hy

end TopologicalVector
