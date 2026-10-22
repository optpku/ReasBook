/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Remark_4_37
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: apply the firm nonexpansiveness inequality
-- `‖T x - T y‖ ^ 2 ≤ ⟪x - y, T x - T y⟫_ℝ` and use that the squared norm is nonnegative.
/-- A firmly nonexpansive map on a subset of a real Hilbert space is monotone in the standard
inner-product sense. -/
theorem FirmlyNonexpansiveOn.monotone {D : Set H} {T : D → H}
    (hT : FirmlyNonexpansiveOn D T) (x y : D) :
    0 ≤ ⟪(x : H) - y, T x - T y⟫_ℝ := by
  exact le_trans (sq_nonneg ‖T x - T y‖) (hT x y)

-- Proof sketch: Remark 4.37 upgrades `α`-averagedness with `α ≤ 1 / 2` to firm
-- nonexpansiveness, then apply `FirmlyNonexpansiveOn.monotone`.
/-- Example 20.6: if `T : D → H` is `α`-averaged with `α ≤ 1 / 2`, then `T` is monotone, i.e. for
all `x, y ∈ D` one has `0 ≤ ⟪x - y, T x - T y⟫_ℝ`. -/
theorem averagedWith_monotone_of_le_half {D : Set H} {α : ℝ} {T : D → H}
    (hT : AveragedWith α T) (hα : α ≤ (1 / 2 : ℝ)) (x y : D) :
    0 ≤ ⟪(x : H) - y, T x - T y⟫_ℝ := by
  exact FirmlyNonexpansiveOn.monotone
    (firmlyNonexpansiveOn_of_averagedWith_le_half hT hα) x y

namespace SetValuedOperator

-- Proof sketch: first use `FirmlyNonexpansiveOn.monotone` to obtain the pointwise monotonicity
-- inequality, then rewrite through the canonical owner `ofFunction_isMonotone_iff`.
/-- A firmly nonexpansive single-valued map on a subset of a real Hilbert space defines a monotone
singleton-valued operator. -/
theorem ofFunction_isMonotone_of_firmlyNonexpansiveOn {D : Set H} {T : D → H}
    (hT : FirmlyNonexpansiveOn D T) :
    (ofFunction D T).IsMonotone := by
  exact ofFunction_isMonotone_iff.2 (FirmlyNonexpansiveOn.monotone hT)

-- Proof sketch: Remark 4.37 upgrades `α`-averagedness with `α ≤ 1 / 2` to firm
-- nonexpansiveness, then rewrite through `ofFunction_isMonotone_iff`.
/-- Example 20.6: if `T : D → H` is `α`-averaged with `α ≤ 1 / 2`, then the associated
singleton-valued operator is monotone. -/
theorem ofFunction_isMonotone_of_averagedWith_le_half {D : Set H} {α : ℝ} {T : D → H}
    (hT : AveragedWith α T) (hα : α ≤ (1 / 2 : ℝ)) :
    (ofFunction D T).IsMonotone := by
  exact ofFunction_isMonotone_iff.2 (averagedWith_monotone_of_le_half hT hα)

end SetValuedOperator
