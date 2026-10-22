/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Exercise_7_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_40
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_32

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ENNReal InnerProductSpace
open Set

namespace ERealFunction

-- Proof sketch: apply the Chapter 13 owner
-- `conjugate_lpNorm_eq_indicator_lpClosedUnitBall_conjExponent` to `q = p.conjExponent`, rewrite
-- `((ι[lpClosedUnitBall N p]).asEReal)∗` as `σ[lpClosedUnitBall N p]` using
-- `conjugate_indicator_eq_supportFunction`, and then use
-- `eq_conjugate_iff_eq_conjugate_of_mem_gammaZero` to swap the conjugation relation back to the
-- Chapter 7 owner `EuclideanSpace.lpNorm`, written pointwise as `‖u‖_[p.conjExponent]`.
/-- Example 13.41: the support function of the coordinate `ℓ^p` unit ball in `ℝ^N` is the
coordinate `ℓ^{p*}` norm, written on the theorem surface with the Chapter 7 notation
`u ↦ ‖u‖_[p*]` and viewed in `EReal`. -/
theorem lpDualNorm_eq_lpNorm_conjExponent
    (N : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    σ[lpClosedUnitBall N p] =
      fun u ↦ (‖u‖_[p.conjExponent] : EReal) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  sorry

end ERealFunction
