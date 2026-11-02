import Mathlib

-- Semantic recall note: no `lean_leansearch` tool was available in this session; Mathlib already
-- provides the exact canonical statement `convexHull_add`, which this item specializes to
-- subsets of `Fin n → ℝ`.

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

/- Exercise 3.10. The convex hull of a Minkowski sum in `ℝ^n` is the Minkowski sum of the
convex hulls. This is exactly mathlib's canonical theorem `convexHull_add`. -/

#check convexHull_add
