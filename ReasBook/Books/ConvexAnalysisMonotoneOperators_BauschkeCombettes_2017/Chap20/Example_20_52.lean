/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_51

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Example 20.52: for the identity singleton-valued operator, the Fitzpatrick function is the
textbook quadratic map `(x, u) ↦ (1 / 4) * ‖x + u‖ ^ 2`. -/
theorem fitzpatrickFunction_id_apply (x u : H) :
    F[id.toSetValuedOperator] (x, u) = ((1 / 4 : ℝ) * ‖x + u‖ ^ 2 : EReal) := sorry
