/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Exercise_7_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp
open scoped ENNReal

namespace ERealFunction

noncomputable section

-- Proof sketch: identify the support function of the `ℓ^p` unit ball with the Chapter 7 owner
-- `EuclideanSpace.lpNorm N p.conjExponent` using Hölder's inequality and the extremal vectors
-- from Exercise 7.9, then apply the norm-conjugate formula from Example 13.3 to conclude that
-- the conjugate is the indicator of the conjugate-exponent unit ball, expressed through the
-- owner `Set.lpClosedUnitBall`.
/-- Example 13.32: on `ℝ^N`, for `p ∈ [1,+∞]`, the conjugate of the coordinate `ℓ^p` norm is the
indicator of the conjugate-exponent unit ball `B_{p*}`. -/
theorem conjugate_lpNorm_eq_indicator_lpClosedUnitBall_conjExponent
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (fun x : EuclideanSpace ℝ (Fin N) ↦ (‖x‖_[p] : EReal))∗ =
      (ι[Set.lpClosedUnitBall N p.conjExponent]).asEReal := sorry

end

end ERealFunction
