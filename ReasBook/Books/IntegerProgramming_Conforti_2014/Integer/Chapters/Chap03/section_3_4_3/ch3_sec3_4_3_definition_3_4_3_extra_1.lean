import Mathlib

/-
Definition 3.4.3-extra-1. This item is a direct recall of mathlib's canonical convex-analysis API:

* `Convex ℝ C` for convex subsets `C ⊆ ℝ^n`;
* `convex_iff_segment_subset` for the equivalent segment formulation of convexity;
* `convexHull ℝ S` together with `subset_convexHull`, `convex_convexHull`, and `convexHull_min`
  for the inclusionwise minimal convex set containing `S`;
* `mem_convexHull_iff_exists_fintype` for the characterization of membership in `convexHull ℝ S`
  by a finite convex combination of points of `S`.
-/

#check Convex
#check convex_iff_segment_subset
#check convexHull
#check subset_convexHull
#check convex_convexHull
#check convexHull_min
#check mem_convexHull_iff_exists_fintype
