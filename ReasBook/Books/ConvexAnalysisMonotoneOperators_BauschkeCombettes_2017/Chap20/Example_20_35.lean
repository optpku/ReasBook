/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Example_20_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Example_20_34

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: the owner-level bridge `isMonotone_of_adjoint_eq_neg` turns the skew-adjoint
-- hypothesis into monotonicity of `A`. Example 20.34 then upgrades that monotonicity to maximal
-- monotonicity for the associated singleton-valued set-valued operator.
/-- Example 20.35: if `A.adjoint = -A`, then `A`, viewed as its associated singleton-valued
set-valued operator, is maximally monotone. -/
theorem toSetValuedOperator_isMaximallyMonotone_of_adjoint_eq_neg
    (A : H →L[ℝ] H) (hA : A.adjoint = -A) :
    Maximal SetValuedOperator.IsMonotone A.toSetValuedOperator := by
  exact toSetValuedOperator_isMaximallyMonotone_of_isMonotone A
    (ContinuousLinearMap.isMonotone_of_adjoint_eq_neg A hA)

end ContinuousLinearMap
