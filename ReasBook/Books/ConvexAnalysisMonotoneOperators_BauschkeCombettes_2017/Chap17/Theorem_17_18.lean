/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section DirectionalDerivativesAndSubgradients

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: Proposition 16.17 gives that `∂ f(x)` is nonempty and weakly compact at a
-- continuity point on the effective domain. Proposition 17.17 identifies the conjugate of
-- `f'(x; ·)` with the indicator of `∂ f(x)`, and Example 13.3 rewrites the conjugate of this
-- indicator as the support function of `∂ f(x)`. Fenchel--Moreau then yields the claimed identity.
/-- Theorem 17.18: for a convex `]-∞,+∞]`-valued function, the directional derivative at a
continuity point on the effective domain is the support function of the subdifferential there. -/
theorem directionalDerivative_eq_supportFunction_subdifferential_of_continuousAtOnEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtOnEffectiveDomain f x) :
    directionalDerivative f x = σ[(∂ f) x] := sorry

-- Proof sketch: apply Theorem 17.18 to rewrite the directional derivative as the support function
-- of `∂ f(x)`. Proposition 16.17 makes `∂ f(x)` weakly compact and nonempty, so the weakly
-- continuous functional `u ↦ ⟪y, u⟫` attains its maximum on `∂ f(x)`.
/-- At a continuity point on the effective domain, each directional derivative is attained by some
subgradient. -/
theorem exists_subgradient_eq_directionalDerivative_of_continuousAtOnEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtOnEffectiveDomain f x) (y : H) :
    ∃ u ∈ (∂ f) x, f′(x; y) = (⟪y, u⟫_ℝ : EReal) := sorry

end DirectionalDerivativesAndSubgradients

end ERealFunction
