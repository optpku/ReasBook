/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Example_20_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: apply Proposition 4.11 to the scaled map `x ↦ -α • T x`. Since `|α| ≤ 1`, that
-- scaled map is still nonexpansive, so its residual map is `1 / 2`-cocoercive. But that residual
-- map is exactly `x ↦ x + α • T x`, and Example 20.5 converts cocoercivity of a single-valued map
-- into monotonicity of the associated singleton-valued operator.
/-- Example 20.7: if `T : D → H` is nonexpansive and `α ∈ [-1,1]`, then the singleton-valued
operator associated with `x ↦ x + α • T x` is monotone. -/
theorem ofFunction_id_add_smul_isMonotone_of_nonexpansive
    {D : Set H} (T : D → H) (hT : LipschitzWith 1 T) {α : ℝ}
    (hα : α ∈ Set.Icc (-1 : ℝ) 1) :
    (ofFunction D (fun x : D ↦ (x : H) + α • T x)).IsMonotone := by
  have hα_abs : |α| ≤ 1 := by
    simpa [abs_le] using hα
  have hα_nnnorm : ‖-α‖₊ ≤ (1 : NNReal) := by
    exact_mod_cast (show ‖-α‖ ≤ 1 by simpa using hα_abs)
  have hScaled :
      LipschitzWith 1 (fun x : D ↦ (-α) • T x) := by
    refine ((lipschitzWith_smul (-α)).comp hT).weaken ?_
    simpa using hα_nnnorm
  have hCoco :
      CocoerciveOn (1 / 2 : ℝ) D (residualMap D (fun x : D ↦ (-α) • T x)) := by
    exact (lipschitzWith_one_iff_residualMap_cocoerciveOn_half _).mp hScaled
  have hResidualMap :
      residualMap D (fun x : D ↦ (-α) • T x) = fun x : D ↦ (x : H) + α • T x := by
    funext x
    simp [residualMap]
  rw [← hResidualMap]
  exact ofFunction_isMonotone_of_cocoerciveOn hCoco

end SetValuedOperator
