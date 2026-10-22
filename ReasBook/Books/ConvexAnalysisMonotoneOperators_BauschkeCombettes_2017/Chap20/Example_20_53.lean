/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_51

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: expand the Fitzpatrick supremum for the singleton-valued operator induced by `A`.
-- At a graph point `(y, A y)`, the skew-adjoint hypothesis forces `⟪y, A y⟫_ℝ = 0`, so the
-- supremand becomes `⟪y, u - A x⟫_ℝ`. If `u = A x`, every term is `0`; if `u ≠ A x`, choose `y`
-- along `u - A x` to make the supremum equal `⊤`. This is exactly the graph indicator.
/-- Example 20.53: if `A.adjoint = -A`, then the Fitzpatrick function of the singleton-valued
operator induced by `A` is the extended-real indicator of its graph. -/
theorem fitzpatrickFunction_eq_indicator_graph_of_adjoint_eq_neg
    (A : H →L[ℝ] H) (hA : A.adjoint = -A) :
    F[A.toSetValuedOperator] =
      (ι[gra A.toSetValuedOperator]).asEReal := sorry

end ContinuousLinearMap
