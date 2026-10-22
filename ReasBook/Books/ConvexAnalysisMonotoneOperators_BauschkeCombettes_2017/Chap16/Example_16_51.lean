/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

open ERealFunction
open Set
open scoped EuclideanSpace InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "C" => Metric.closedBall (!₂[(-1 : ℝ), 0] : ℝ²) 1
local notation "D" => Metric.closedBall (!₂[(1 : ℝ), 0] : ℝ²) 1

-- Proof sketch: expand membership in the two closed balls as distance inequalities to `(-1,0)`
-- and `(1,0)`. The two inequalities force both coordinates to vanish, and conversely the origin
-- satisfies both.
/-- The two opposite closed unit balls meet exactly at the origin. -/
theorem leftRightClosedUnitBall_inter_eq_singleton_origin :
    C ∩ D = ({0} : Set ℝ²) := sorry

-- Proof sketch: `effectiveDomain_indicator` identifies each indicator domain with its underlying
-- set, so the previous intersection computation gives the common effective domain immediately.
/-- The effective domains of the two closed-ball indicators intersect exactly at the origin. -/
theorem effectiveDomain_closedBallIndicators_inter_eq_singleton_origin :
    effectiveDomain (ι[C]) ∩ effectiveDomain (ι[D]) = ({0} : Set ℝ²) := sorry

-- Proof sketch: at the common boundary point `0`, the pointwise sum `ι[C] + ι[D]` vanishes only
-- at the origin and is `⊤` elsewhere, so its subgradient inequality reduces to the indicator of
-- the singleton `{0}`. The subdifferential of the singleton indicator at `0` is all of `ℝ²`.
/-- The subdifferential of `ι[C] + ι[D]` at the origin is all of `ℝ²`. -/
theorem subdifferential_oppositeClosedBallIndicatorSum_at_origin :
    (∂ (ι[C] + ι[D])) (0 : ℝ²) = (univ : Set ℝ²) := sorry

-- Proof sketch: the canonical bridge `subdifferential_setIndicator_eq_normalCone` identifies each
-- indicator subdifferential with the corresponding normal cone. At the origin, the left and right
-- closed balls have outward normals on the positive and negative horizontal rays, whose pointwise
-- sum is exactly the horizontal axis.
/-- The sum of the two indicator subdifferentials at the origin is the horizontal axis. -/
theorem sum_subdifferential_closedBallIndicators_at_origin :
    (∂ ι[C]) (0 : ℝ²) + (∂ ι[D]) (0 : ℝ²) = {u : ℝ² | u 1 = 0} := sorry

-- Proof sketch: use the two explicit descriptions above: the left-hand side is `univ`,
-- whereas the right-hand side is `{u | u 1 = 0}`, a proper subset of `ℝ²`.
/-- Example 16.51: for the closed unit balls centered at `(-1,0)` and `(1,0)` in `ℝ²`, the
subdifferential of `ι[C] + ι[D]` at the origin is not the sum of the subdifferentials of `ι[C]`
and `ι[D]`. -/
theorem subdifferential_oppositeClosedBallIndicatorSum_at_origin_ne_sum_subdifferentials :
    (∂ (ι[C] + ι[D])) (0 : ℝ²) ≠
      (∂ ι[C]) (0 : ℝ²) + (∂ ι[D]) (0 : ℝ²) := sorry

end

end ERealFunction
