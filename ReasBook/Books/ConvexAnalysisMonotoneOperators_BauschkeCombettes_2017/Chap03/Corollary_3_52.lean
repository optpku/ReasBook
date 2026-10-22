/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_42
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Corollary_3_51

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- Corollary 3.52: two nonempty closed convex disjoint subsets of a real Hilbert space are
strongly separated whenever the second set is bounded. -/
-- Proof sketch: `C - D` is closed because it is the Minkowski sum `C + (-D)` of a closed convex
-- set with a bounded closed convex set, and it is convex because both `C` and `D` are convex.
-- Apply Corollary 3.51 to the closed convex difference set.
theorem areStronglySeparated_of_nonempty_isClosed_convex_disjoint_bounded
    {C D : Set 𝓗} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hCD : Disjoint C D) (hD_bounded : Bornology.IsBounded D) :
    AreStronglySeparated C D := by
  refine
    areStronglySeparated_of_disjoint_of_isClosed_of_convex_sub
      hC_nonempty hD_nonempty hCD ?_ ?_
  · simpa [sub_eq_add_neg] using
      isClosed_minkowski_sum_of_isBounded hC_closed hC_convex
        hD_closed.neg hD_convex.neg hD_bounded.neg
  · simpa using hC_convex.sub hD_convex
