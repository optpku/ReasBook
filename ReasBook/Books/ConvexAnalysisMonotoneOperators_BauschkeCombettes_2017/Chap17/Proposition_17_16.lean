/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_14

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

section DirectionalDerivativesAndSubgradients

variable (f : ℝ → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))

-- Proof sketch: apply convexity to the midpoint identity
-- `x = ((x - α) + (x + α)) / 2`, rearrange the resulting inequality of secant quotients, and pass
-- to the infimum definitions of the one-sided directional derivatives.
/-- Proposition 17.16 (1): at an effective-domain point of a convex function on `ℝ`, the left
derivative is bounded above by the right derivative. -/
theorem leftDerivative_le_rightDerivative
    {x : ℝ} (hx : x ∈ effectiveDomain f) :
    f′₋(x) ≤ f′₊(x) := sorry

-- Proof sketch: specialize Proposition 17.14 (1) to `H = ℝ`, test the subgradient inequality on
-- the directions `1` and `-1`, and use clause (1) to identify the subdifferential with the real
-- preimage of the extended-real interval between the one-sided derivatives `f′₋(x)` and `f′₊(x)`.
/-- Proposition 17.16 (2): at an effective-domain point of a convex function on `ℝ`, the
subdifferential is the set of real numbers lying between the left and right derivatives. -/
theorem subdifferential_eq_Icc_oneSidedDerivatives
    {x : ℝ} (hx : x ∈ effectiveDomain f) :
    (∂ f) x =
      ((↑) : ℝ → EReal) ⁻¹' Set.Icc (f′₋(x)) (f′₊(x)) := sorry

-- Proof sketch: apply Proposition 17.2 (3) to the pair `x < y`, then rewrite the directional
-- derivatives along `y - x` and `x - y` by factoring out the positive scalar `y - x`.
/-- Proposition 17.16 (3): along an increasing pair of effective-domain points of a convex
function on `ℝ`, the right derivative at the left point does not exceed the left derivative at the
right point. -/
theorem rightDerivative_le_leftDerivative_of_lt
    {x y : ℝ} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (hxy : x < y) :
    f′₊(x) ≤ f′₋(y) := sorry

-- Proof sketch: if `x ≤ y` are both in the effective domain, apply clause (3) to compare the
-- right derivative at `x` with the left derivative at `y`, then insert clause (1) at `y`.
/-- Proposition 17.16 (4): the right derivative of a convex function on `ℝ` is increasing on its
effective domain. -/
theorem monotoneOn_rightDerivative :
    MonotoneOn (fun x : ℝ ↦ f′₊(x)) (effectiveDomain f) := sorry

-- Proof sketch: if `x ≤ y` are both in the effective domain, combine clause (1) at `x` with
-- clause (3) to compare the left derivative at `x` and the left derivative at `y`.
/-- Proposition 17.16 (5): the left derivative of a convex function on `ℝ` is increasing on its
effective domain. -/
theorem monotoneOn_leftDerivative :
    MonotoneOn (fun x : ℝ ↦ f′₋(x)) (effectiveDomain f) := sorry

end DirectionalDerivativesAndSubgradients

end ERealFunction
