/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: apply the cocoercivity inequality at `x` and `y`; since the parameter `β` is
-- positive, the term `β * ‖T x - T y‖ ^ 2` is nonnegative, so the right-hand side inner product is
-- also nonnegative.
/-- Example 20.5: every cocoercive map on a subset of a real Hilbert space is monotone, i.e. for
all `x, y ∈ D` one has `0 ≤ ⟪x - y, T x - T y⟫_ℝ`. -/
theorem CocoerciveOn.monotone {β : ℝ} {D : Set H} {T : D → H} (hT : CocoerciveOn β D T)
    (x y : D) : 0 ≤ ⟪(x : H) - y, T x - T y⟫_ℝ := by
  exact le_trans (mul_nonneg hT.pos.le (sq_nonneg ‖T x - T y‖)) (hT.ineq x y)

namespace SetValuedOperator

/-- Example 20.5: a cocoercive single-valued map on a subset of a real Hilbert space defines a
monotone singleton-valued operator. -/
theorem ofFunction_isMonotone_of_cocoerciveOn {β : ℝ} {D : Set H} {T : D → H}
    (hT : CocoerciveOn β D T) :
    (ofFunction D T).IsMonotone := by
  exact ofFunction_isMonotone_iff.2 hT.monotone

end SetValuedOperator
