/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Corollary_20_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Example_20_15

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: use the canonical linear-map bridge
-- `LinearMap.toSetValuedOperator_isMonotone_iff` to turn `A.toLinearMap.IsMonotone` into
-- monotonicity of the singleton-valued operator associated with `A`. Since `A` is continuous as
-- a bounded linear operator, Corollary 20.28 applies directly.
/-- Example 20.34: a monotone bounded linear operator on a real inner product space is maximally
monotone when viewed as its associated singleton-valued set-valued operator. -/
theorem toSetValuedOperator_isMaximallyMonotone_of_isMonotone
    (A : H →L[ℝ] H) (hA : A.toLinearMap.IsMonotone) :
    Maximal SetValuedOperator.IsMonotone A.toSetValuedOperator := by
  simpa using
    Function.toSetValuedOperator_isMaximallyMonotone_of_monotone_continuous
      (A : H → H)
      ((LinearMap.toSetValuedOperator_isMonotone_iff A.toLinearMap).2 hA)
      A.continuous

end ContinuousLinearMap
