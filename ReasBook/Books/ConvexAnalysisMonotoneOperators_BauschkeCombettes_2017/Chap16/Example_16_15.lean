/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Example_16_14

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

noncomputable section

section RealLine

-- Proof sketch: the support function of `[-1,1]` is the supremum of `x ↦ ξ x` over that interval,
-- which equals `|ξ|` by checking the sign of `ξ` and evaluating at the appropriate endpoint.
/-- The support function of the interval `[-1,1] ⊆ ℝ` is the absolute value. -/
theorem supportFunction_Icc_neg_one_one_eq_abs :
    σ[Set.Icc (-1 : ℝ) 1] = (fun ξ : ℝ ↦ |ξ|).toEReal.asEReal := sorry

-- Proof sketch: identify `|·|` with the support function of `[-1,1]` and apply the three
-- subdifferential formulas from Example 16.14 directly to the canonical owner
-- `(∂ (fun η ↦ |η|).toEReal)`. This yields the endpoints `-1` and `1` away from `0`, and the
-- interval `[-1,1]` at `0`.
/-- Example 16.15: since `|·| = σ[[-1,1]]`, the subdifferential of the absolute value on `ℝ` is
`{-1}` on `(-∞,0)`, `[-1,1]` at `0`, and `{1}` on `(0,+∞)`. -/
theorem subdifferential_abs_eq_piecewise (ξ : ℝ) :
    (∂ (fun η : ℝ ↦ |η|).toEReal) ξ =
      if ξ < 0 then {(-1 : ℝ)}
      else if ξ = 0 then Set.Icc (-1 : ℝ) 1
      else {(1 : ℝ)} := sorry

end RealLine

end

end ERealFunction
