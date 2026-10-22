/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section DirectionalDerivativesAndSubgradients

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))

-- Proof sketch: unfold membership in the subdifferential, apply Proposition 17.2 (2) to the
-- direction `y - x`, and use convexity to pass between the affine-minorant inequality and the
-- directional-derivative lower bound.
/-- Proposition 17.14 (1): at an effective-domain point of a convex function, a vector belongs to
the subdifferential exactly when its inner-product functional is pointwise dominated by the
directional derivative. -/
theorem mem_subdifferential_iff_inner_le_directionalDerivative
    {x u : H} (hx : x ∈ effectiveDomain f) :
    u ∈ (∂ f) x ↔ ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ (f′(x; y)) := sorry

-- Proof sketch: `hconv.nonempty` supplies the nonempty effective-domain hypothesis needed for
-- Proposition 16.4 (1), which yields `x ∈ effectiveDomain f` from `SubdifferentiableAt f x`;
-- then apply Proposition 17.2 (6).
/-- Proposition 17.14 (2): if a convex `]-∞,+∞]`-valued function is subdifferentiable at `x`,
then its directional derivative at `x` is proper. -/
theorem SubdifferentiableAt.directionalDerivative_isProper
    {x : H}
    (hxsub : SubdifferentiableAt f x) :
    IsProper (directionalDerivative f x) := sorry

-- Proof sketch: derive the nonempty effective-domain input from `hconv.nonempty`, use
-- Proposition 16.4 (1) to obtain `x ∈ effectiveDomain f`, and invoke Proposition 17.2 (4).
/-- Proposition 17.14 (3): if a convex `]-∞,+∞]`-valued function is subdifferentiable at `x`,
then its directional derivative at `x` is sublinear. -/
theorem SubdifferentiableAt.sublinear_directionalDerivative
    {x : H}
    (hxsub : SubdifferentiableAt f x) :
    Sublinear (directionalDerivative f x) := sorry

end DirectionalDerivativesAndSubgradients

end ERealFunction
