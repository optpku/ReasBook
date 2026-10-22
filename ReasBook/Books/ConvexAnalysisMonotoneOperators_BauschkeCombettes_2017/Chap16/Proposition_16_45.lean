/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: apply `SetValuedOperator.dom` to the inverse formula from Proposition 16.44,
-- rewrite the domain of the singleton-valued proximity operator pointwise as `Set.univ`, and use
-- Text 1.0.12 to identify the domain of the inverse with the range of the operator sum
-- `(id.toSetValuedOperator + ∂ f)`.
/-- Proposition 16.45: if `f ∈ Γ₀(H)`, then the range of the set-valued operator
`id.toSetValuedOperator + ∂ f`, i.e. `Id + ∂ f`, is all of `H`. -/
theorem range_id_add_subdifferential_eq_univ_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    SetValuedOperator.range ((id : H → H).toSetValuedOperator + ∂ f) = Set.univ := sorry

end SubdifferentialCalculus

end ERealFunction
