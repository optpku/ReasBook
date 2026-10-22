/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section DirectionalDerivativesAndSubgradients

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f : H → Set.Ioi (⊥ : EReal))

-- Proof sketch: Proposition 16.17 gives that `∂ f(x)` is nonempty at a continuity point on the
-- effective domain. Proposition 16.4 supplies closedness and convexity, and Theorem 3.16.1 then
-- upgrades these properties to the Chebyshev condition needed for the metric projection.
/-- The subdifferential at a continuity point on the effective domain is a Chebyshev set. -/
theorem isChebyshev_subdifferential_of_continuousAtOnEffectiveDomain
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtOnEffectiveDomain f x) :
    IsChebyshev ((∂ f) x) := sorry

/-- The projection of `0` onto the subdifferential at a continuity point on the effective domain,
that is, the minimal-norm subgradient at `x`. -/
def minimalNormSubgradient
    (hconv : ConvexOn f (effectiveDomain f))
    (x : H) (hxcont : ContinuousAtOnEffectiveDomain f x) : H :=
  projectionPoint ((∂ f) x)
    (isChebyshev_subdifferential_of_continuousAtOnEffectiveDomain f hconv hxcont) 0

-- Proof sketch: unfold `minimalNormSubgradient` and apply the defining best-approximation theorem
-- for `projectionPoint` on the Chebyshev set `(∂ f) x`.
/-- The minimal-norm subgradient is the best approximation of `0` from the subdifferential. -/
theorem minimalNormSubgradient_isBestApproximation_zero_of_continuousAtOnEffectiveDomain
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtOnEffectiveDomain f x) :
    IsBestApproximation 0 ((∂ f) x) (minimalNormSubgradient f hconv x hxcont) := sorry

-- Proof sketch: if the minimal-norm subgradient were `0`, then `0 ∈ (∂ f) x`. Fermat's rule
-- identifies zeros of the subdifferential with global minimizers, contradicting `x ∉ Argmin f`.
/-- A nonminimizer has a nonzero minimal-norm subgradient at every continuity point on the
effective domain. -/
theorem minimalNormSubgradient_ne_zero_of_continuousAtOnEffectiveDomain_of_not_mem_argmin
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtOnEffectiveDomain f x)
    (hxnotmin : x ∉ Argmin f.asEReal) :
    minimalNormSubgradient f hconv x hxcont ≠ 0 := sorry

/-- The normalized negative minimal-norm subgradient, i.e. the steepest descent direction
associated with `f` at `x`. -/
def steepestDescentDirection
    (hconv : ConvexOn f (effectiveDomain f))
    (x : H) (hxcont : ContinuousAtOnEffectiveDomain f x) : H :=
  let u := minimalNormSubgradient f hconv x hxcont;
  -(‖u‖)⁻¹ • u

-- Proof sketch: write the steepest descent direction as `-(‖u‖)⁻¹ • u` with
-- `u = minimalNormSubgradient ...`. The previous theorem gives `u ≠ 0`, so
-- `‖(‖u‖)⁻¹ • u‖ = ‖u‖⁻¹ * ‖u‖ = 1`.
/-- For a nonminimizer, the steepest descent direction has norm `1`. -/
theorem norm_steepestDescentDirection_eq_one_of_continuousAtOnEffectiveDomain_of_not_mem_argmin
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtOnEffectiveDomain f x)
    (hxnotmin : x ∉ Argmin f.asEReal) :
    ‖steepestDescentDirection f hconv x hxcont‖ = 1 := sorry

-- Proof sketch: Theorem 17.18 rewrites `f′(x; ·)` as the support function of
-- `(∂ f) x`. The projection characterization of `u := minimalNormSubgradient ...` gives
-- `max ⟪-u, (∂ f) x - u⟫ = 0`, so the normalized vector
-- `z := steepestDescentDirection ...` attains the value `-‖u‖` on the support function. Every
-- `y ∈ closedBall 0 1` satisfies `⟪y, u⟫ ≥ -‖u‖` by Cauchy--Schwarz, hence no smaller directional
-- derivative value is possible; equality forces `y = z`.
/-- Proposition 17.22: if `x` is a continuity point on the effective domain of a convex function
but not a global minimizer, then the steepest descent direction obtained by normalizing the
negative metric projection of `0` onto `(∂ f) x` is the unique minimizer of `f′(x; ·)` on the
closed unit ball. -/
theorem argminOn_closedUnitBall_directionalDerivative_eq_singleton_steepestDescentDirection
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtOnEffectiveDomain f x)
    (hxnotmin : x ∉ Argmin f.asEReal) :
    Argmin[Metric.closedBall 0 1] (f′(x; ·)) =
      {steepestDescentDirection f hconv x hxcont} := sorry

end DirectionalDerivativesAndSubgradients

end

end ERealFunction
