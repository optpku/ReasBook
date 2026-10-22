/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ERealFunction

variable {H : Type u} {I : Type v} [AddCommGroup H] [Module ℝ H]

-- Proof sketch: use `epigraph_iSup` to rewrite the epigraph of the pointwise supremum as the
-- intersection of the epigraphs of the family members, then apply `convex_iInter`.
/-- Proposition 8.16: the pointwise supremum of a family of extended-real-valued functions with
convex epigraphs again has convex epigraph, hence is convex. -/
theorem convex_epigraph_iSup (f : I → H → EReal)
    (hconv : ∀ i, Convex ℝ (epigraph (f i))) :
    Convex ℝ (epigraph (⨆ i, f i)) := by
  -- Rewrite the epigraph of the supremum as the intersection of the individual epigraphs.
  rw [epigraph_iSup]
  -- Intersections of convex sets are convex, so the family hypothesis closes the goal.
  exact convex_iInter hconv

end ERealFunction
