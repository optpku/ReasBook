/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/- Definition 3.3: the convex hull of `C` is the intersection of all convex subsets of the ambient
Hilbert space that contain `C`. This is exactly the canonical mathlib theorem
`convexHull_eq_iInter`. -/
recall convexHull_eq_iInter

/-- The closed convex hull of `C` is the intersection of all closed convex subsets of the ambient
Hilbert space that contain `C`. -/
theorem closedConvexHull_eq_iInter_closed_convex_supersets (C : Set 𝓗) :
    closedConvexHull ℝ C = ⋂ (D : Set 𝓗) (_ : C ⊆ D) (_ : Convex ℝ D) (_ : IsClosed D), D := by
  simp [closedConvexHull, Set.iInter_subtype, Set.iInter_and]
