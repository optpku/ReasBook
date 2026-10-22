/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

noncomputable section

section NormSubdifferential

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Classical decidability of equality on `H`, used to state the piecewise formula for the norm
subdifferential. -/
local instance instDecidableEqNormSubdifferential : DecidableEq H := Classical.decEq H

-- Proof sketch: specialize Example 16.31 to the packaged absolute-value function, then use
-- Example 16.15 to compute the scalar subdifferential of `ξ ↦ |ξ|`. If `x ≠ 0`, then `‖x‖ > 0`,
-- so the scalar subdifferential is `{1}` and the common-ray condition forces `u` to be the
-- normalized vector `‖x‖⁻¹ • x`. If `x = 0`, then Example 16.15 gives the scalar value
-- `[-1,1]`, which translates to the closed unit ball `Metric.closedBall (0 : H) 1`.
/-- Example 16.32: the subdifferential of the norm is the singleton containing the normalized
vector away from `0`, and the closed unit ball at `0`. -/
theorem subdifferential_norm_eq_singleton_or_closedBall (x : H) :
    (∂ (fun y : H ↦ ‖y‖).toEReal) x =
      if x = 0 then (Metric.closedBall (0 : H) 1 : Set H) else ({‖x‖⁻¹ • x} : Set H) := sorry

end NormSubdifferential

end

end ERealFunction
