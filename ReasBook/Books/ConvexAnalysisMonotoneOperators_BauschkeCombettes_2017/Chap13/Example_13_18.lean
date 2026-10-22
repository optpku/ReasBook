/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_23

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- The strict Loewner relation on `S(H)`: `A ≺ B` iff `B - A` is strictly monotone in the sense
of Definition 2.23. -/
def StrictlyLoewner (A B : selfAdjoint (H →L[ℝ] H)) : Prop :=
  (((B - A : selfAdjoint (H →L[ℝ] H)) : H →L[ℝ] H).toLinearMap).IsStrictlyMonotone

end ContinuousLinearMap

set_option quotPrecheck false in
notation "S(" H ")" => selfAdjoint (H →L[ℝ] H)

infix:50 " ≺ " => ContinuousLinearMap.StrictlyLoewner

-- Proof sketch: rewrite the ambient order by `ContinuousLinearMap.le_def`, express positivity via
-- `ContinuousLinearMap.isPositive_iff'`, and use that the difference of two self-adjoint operators
-- is self-adjoint to reduce to the quadratic-form inequality.
/-- Example 13.18 (1): on the real vector space of self-adjoint operators, the Loewner partial
order is the ambient operator order, characterized by `⟪A x, x⟫ ≤ ⟪B x, x⟫` for every `x`. -/
theorem loewner_le_iff_forall_inner_le (A B : S(H)) :
    A ≤ B ↔ ∀ x : H, ⟪(A : H →L[ℝ] H) x, x⟫_ℝ ≤ ⟪(B : H →L[ℝ] H) x, x⟫_ℝ := sorry

-- Proof sketch: expand the quadratic form of `B - A` and rearrange the resulting identity.
/-- Example 13.18 (2): the strict Loewner relation on `S(H)` is the Chapter 2 strict-monotonicity
condition for the operator difference `B - A`, equivalently `⟪A x, x⟫ < ⟪B x, x⟫` on every
nonzero vector. -/
theorem strictlyLoewner_iff_forall_inner_lt (A B : S(H)) :
    A ≺ B ↔ ∀ x : H, x ≠ 0 → ⟪(A : H →L[ℝ] H) x, x⟫_ℝ < ⟪(B : H →L[ℝ] H) x, x⟫_ℝ := sorry
