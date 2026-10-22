/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_23

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Corollary 4.24: if `D` is a nonempty closed convex subset of a real inner product space and
`T` is
nonexpansive on `D`, then the fixed point set `Fix T = {x ∈ D | T x = x}` is closed and convex. -/
theorem isClosed_and_convex_fixedPointSet_of_nonexpansiveOn
    {D : Set H} (_hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    {T : H → H} (hT : LipschitzOnWith 1 T D) :
    IsClosed (fixedPointSetOn D T) ∧ Convex ℝ (fixedPointSetOn D T) := by
  exact
    isClosed_and_convex_fixedPointSetOn_of_quasinonexpansive
      hT.quasinonexpansiveOn hD_closed hD_convex

end
