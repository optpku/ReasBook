/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

-- The declarations below reuse the earlier Chapter 3 owner `IsEdgeOf` together with mathlib's
-- canonical `extremePoints`, `segment`, and `SimpleGraph.fromRel` APIs.

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A nondegenerate extreme segment is an edge in the sense of `IsEdgeOf`. -/
theorem isEdgeOf_segment_iff {P : Set E} {v w : E} (hvw : v ≠ w) :
    IsEdgeOf P (segment ℝ v w) ↔ IsExtreme ℝ P (segment ℝ v w) := by
  constructor
  · intro h
    exact h.isExtreme
  · intro h
    refine ⟨convex_segment _ _, h, ?_⟩
    rw [direction_affineSpan, vectorSpan_segment]
    simpa using finrank_span_singleton (vsub_ne_zero.2 hvw.symm)

/-- The edge condition on a segment is symmetric in its endpoints. -/
theorem isEdgeOf_segment_symm {P : Set E} {v w : E} :
    IsEdgeOf P (segment ℝ v w) ↔ IsEdgeOf P (segment ℝ w v) := by
  by_cases hvw : v = w
  · subst hvw
    rfl
  · rw [isEdgeOf_segment_iff hvw, isEdgeOf_segment_iff (Ne.symm hvw)]
    simp [segment_symm]

/-- Definition 3.11-extra-2. The skeleton of a polytope `P` is the graph whose nodes are the
vertices of `P` and whose edges join exactly the pairs of vertices that determine an edge of `P`.
-/
def polytope_skeleton (P : Set E) : SimpleGraph (P.extremePoints ℝ) :=
  SimpleGraph.fromRel fun v w ↦ IsEdgeOf P (segment ℝ (v : E) (w : E))

/-- Two nodes of the polytope skeleton are adjacent exactly when they are distinct and the segment
between the corresponding vertices is an edge of `P`. -/
theorem polytope_skeleton_adj_iff {P : Set E} {v w : P.extremePoints ℝ} :
    (polytope_skeleton P).Adj v w ↔
      v ≠ w ∧ IsEdgeOf P (segment ℝ (v : E) (w : E)) := by
  simp [polytope_skeleton, isEdgeOf_segment_symm]
