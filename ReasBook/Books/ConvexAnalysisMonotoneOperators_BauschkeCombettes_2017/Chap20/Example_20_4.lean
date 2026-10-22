/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

namespace SetValuedOperator

-- Proof sketch: unfold `SetValuedOperator.IsMonotone`; graph membership for `ofFunction D A`
-- forces `u = A ⟨x, hx⟩` and `v = A ⟨y, hy⟩`. Then the real inner product is ordinary
-- multiplication, and the desired inequality is the canonical mathlib consequence
-- `Monovary.sub_mul_sub_nonneg` for the monotone pair `((↑) : D → ℝ)` and `A`.
/-- Example 20.4: the singleton-valued operator attached to an increasing real function on a
subset of `ℝ` is monotone. -/
theorem ofFunction_isMonotone_of_monotone (D : Set ℝ) (A : D → ℝ) (hA : Monotone A) :
    (ofFunction D A).IsMonotone := by
  rw [isMonotone_iff]
  intro x u y v hu hv
  rcases hu with ⟨hx, rfl⟩
  rcases hv with ⟨hy, rfl⟩
  have hMonovary : Monovary ((↑) : D → ℝ) A := (Subtype.mono_coe D).monovary hA
  rw [show ⟪x - y, A ⟨x, hx⟩ - A ⟨y, hy⟩⟫_ℝ =
      (x - y) * (A ⟨x, hx⟩ - A ⟨y, hy⟩) by
    simpa [conj_trivial] using
      (RCLike.inner_apply' (x - y) (A ⟨x, hx⟩ - A ⟨y, hy⟩))]
  exact hMonovary.sub_mul_sub_nonneg ⟨y, hy⟩ ⟨x, hx⟩

end SetValuedOperator
