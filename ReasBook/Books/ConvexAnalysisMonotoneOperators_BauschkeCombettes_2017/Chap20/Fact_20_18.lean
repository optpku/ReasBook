/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ContinuousLinearMap

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A product of commuting positive bounded operators is positive. -/
theorem IsPositive.mul_of_commute {A B : E →L[𝕜] E}
    (hA : A.IsPositive) (hB : B.IsPositive) (hcomm : Commute A B) :
    (A * B).IsPositive := sorry

section Real

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: turn the textbook hypotheses into positivity via
-- `ContinuousLinearMap.isPositive_iff'`, apply the owner-level positivity lemma
-- `ContinuousLinearMap.IsPositive.mul_of_commute`, and then forget positivity back to monotonicity.
/-- Fact 20.18: if `A` and `B` are self-adjoint monotone bounded linear operators on a real
Hilbert space and commute, then the product `AB` is monotone. -/
theorem isMonotone_mul_of_isSelfAdjoint_of_commute
    {A B : H →L[ℝ] H}
    (hA_self : IsSelfAdjoint A) (hB_self : IsSelfAdjoint B)
    (hA_mono : A.toLinearMap.IsMonotone) (hB_mono : B.toLinearMap.IsMonotone)
    (hcomm : Commute A B) :
    (A * B).toLinearMap.IsMonotone := by
  have hA_pos : A.IsPositive := (isPositive_iff' A).2 ⟨hA_self, hA_mono⟩
  have hB_pos : B.IsPositive := (isPositive_iff' B).2 ⟨hB_self, hB_mono⟩
  exact (hA_pos.mul_of_commute hB_pos hcomm).toLinearMap.isMonotone

end Real

end ContinuousLinearMap
