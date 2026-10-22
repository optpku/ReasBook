/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_42

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

open scoped SetValuedOperator

/- Example 20.43 (1): the pointwise formula for the partial inverse `A₍V₎` is exactly the
owner theorem `partialInverse_apply` from Definition 20.42. -/
recall partialInverse_apply

/- Example 20.43 (2): the pointwise membership criterion for `A₍V₎` is exactly
`mem_partialInverse_iff`. -/
recall mem_partialInverse_iff

-- Proof sketch: specialize the definition of the partial inverse to `V = ⊤`. Then `⊤ᗮ = ⊥`.
-- The projection onto `⊤` is the identity, and the projection onto `⊥` is zero, so the
-- membership relation reduces to the original membership relation in `A`.
/-- The partial inverse with respect to the whole space is the operator itself. -/
@[simp] theorem partialInverse_top_eq_self (A : SetValuedOperator H H) :
    A₍⊤₎ = A := by
  ext x y; simp [Submodule.starProjection_top, Submodule.starProjection_bot]

-- Proof sketch: specialize the definition of the partial inverse to `V = ⊥`. Then the
-- projection onto `⊥` is zero and the projection onto `⊥ᗮ = ⊤` is the identity, so the
-- defining membership condition becomes exactly the reversed membership relation characterizing
-- `A.inverse`.
/-- The partial inverse with respect to the zero subspace is the inverse operator. -/
@[simp] theorem partialInverse_bot_eq_inverse (A : SetValuedOperator H H) :
    A₍⊥₎ = A⁻¹ := by
  ext x y; simp [Submodule.starProjection_top, Submodule.starProjection_bot]

end SetValuedOperator
