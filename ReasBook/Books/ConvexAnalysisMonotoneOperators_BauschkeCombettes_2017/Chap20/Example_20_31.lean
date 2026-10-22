/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Remark_4_15_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Corollary_20_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Example_20_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise SetValuedOperator

namespace Function

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: `β`-cocoercivity gives monotonicity by Example 20.5 and Lipschitz continuity by
-- Remark 4.15.1. Apply the canonical owner theorem Corollary 20.28 for continuous monotone
-- singleton-valued operators.
/-- Example 20.31: if `T : H → H` is `β`-cocoercive with `β ∈ ℝ_{++}`, then the associated
singleton-valued set-valued operator of `T` is maximally monotone. -/
theorem toSetValuedOperator_isMaximallyMonotone_of_cocoerciveOn_univ
    {β : ℝ} {T : H → H}
    (hT : CocoerciveOn β (Set.univ : Set H) (fun x : (Set.univ : Set H) ↦ T x)) :
    Maximal SetValuedOperator.IsMonotone T.toSetValuedOperator := by
  have hT_mono : T.toSetValuedOperator.IsMonotone := by
    simpa [Function.toSetValuedOperator] using
      SetValuedOperator.ofFunction_isMonotone_of_cocoerciveOn hT
  have hT_lipschitz_univ : LipschitzWith (Real.toNNReal (1 / β)) (fun x : Set.univ ↦ T x) :=
    lipschitzWith_of_cocoercive hT
  have hT_lipschitz : LipschitzWith (Real.toNNReal (1 / β)) T := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simpa using hT_lipschitz_univ.dist_le_mul ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩
  exact toSetValuedOperator_isMaximallyMonotone_of_monotone_continuous T hT_mono
    hT_lipschitz.continuous

end Function
