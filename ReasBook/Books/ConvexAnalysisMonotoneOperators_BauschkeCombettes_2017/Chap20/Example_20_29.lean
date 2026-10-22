/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Example_20_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Corollary_20_28

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Function

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: specialize the domain-level owner from Example 20.7 to `Set.univ`, rewriting it
-- through the canonical whole-space owner `Function.toSetValuedOperator`. A `1`-Lipschitz map is
-- continuous, so Corollary 20.28 upgrades monotonicity to maximal monotonicity.
/-- Example 20.29: if `T : H → H` is nonexpansive and `α ∈ [-1, 1]`, then the affine perturbation
`Id + α T`, viewed as a singleton-valued set-valued operator, is maximally monotone. -/
theorem id_add_smul_toSetValuedOperator_isMaximallyMonotone_of_nonexpansive
    (T : H → H) (hT : LipschitzWith 1 T) {α : ℝ} (hα : α ∈ Set.Icc (-1 : ℝ) 1) :
    Maximal SetValuedOperator.IsMonotone (id + α • T).toSetValuedOperator := by
  let S : Set H := Set.univ
  let T' : S → H := fun x ↦ T x
  have hT' : LipschitzWith 1 T' := by
    simpa [S, T', one_mul] using hT.comp (LipschitzWith.subtype_val S)
  refine toSetValuedOperator_isMaximallyMonotone_of_monotone_continuous _ ?_ ?_
  · simpa [S, T', Function.toSetValuedOperator] using
      SetValuedOperator.ofFunction_id_add_smul_isMonotone_of_nonexpansive T' hT' hα
  · exact continuous_id.add (continuous_const.smul hT.continuous)

end Function
