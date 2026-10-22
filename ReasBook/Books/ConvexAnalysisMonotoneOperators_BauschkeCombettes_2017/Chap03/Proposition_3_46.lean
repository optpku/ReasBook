/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: `convexHull ℝ (closure C)` lies in the closed convex hull of `closure C`, and the
-- closed convex hull is unchanged by taking closure. The standard closed-convex-hull identity then
-- identifies the target with `closure (convexHull ℝ C)`.
/-- Proposition 3.46 (1): the convex hull of the closure of a subset of a real normed space is
contained in the closure of its convex hull. -/
theorem convexHull_closure_subset_closure_convexHull (C : Set E) :
    convexHull ℝ (closure C) ⊆ closure (convexHull ℝ C) := by
  -- Route through the canonical closed convex hull identity.
  calc
    convexHull ℝ (closure C) ⊆ closedConvexHull ℝ (closure C) :=
      convexHull_subset_closedConvexHull
    _ = closedConvexHull ℝ C := closedConvexHull_closure_eq_closedConvexHull
    _ = closure (convexHull ℝ C) := by
      simpa using (closedConvexHull_eq_closure_convexHull : closedConvexHull ℝ C = _)

-- Proof sketch: this is the standard identification of the closed convex hull with the closure of
-- the convex hull, specialized to subsets of a real normed space.
/-- Proposition 3.46 (2): the closure of the convex hull of a subset of a real normed space is its
closed convex hull. -/
theorem closure_convexHull_eq_closedConvexHull (C : Set E) :
    closure (convexHull ℝ C) = closedConvexHull ℝ C := by
  -- This is exactly the standard closed-convex-hull identity in mathlib.
  simpa [eq_comm] using
    (closedConvexHull_eq_closure_convexHull : closedConvexHull ℝ C = closure (convexHull ℝ C))
