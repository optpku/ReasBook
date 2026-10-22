/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section SubdifferentialContinuity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A point is a continuity point of `f` when the finite-valued restriction of `f` to its
effective domain is continuous there. -/
def ContinuousAtOnEffectiveDomain (f : H → Set.Ioi (⊥ : EReal)) (x : H) : Prop :=
  x ∈ effectiveDomain f ∧
    ContinuousWithinAt (fun y : H ↦ (f y : EReal).toReal) (effectiveDomain f) x

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A continuity point on the effective domain belongs to the effective domain. -/
theorem ContinuousAtOnEffectiveDomain.mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H}
    (hx : ContinuousAtOnEffectiveDomain f x) :
    x ∈ effectiveDomain f :=
  hx.1

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A continuity point on the effective domain is continuous for the finite-valued restriction of
`f` to its effective domain. -/
theorem ContinuousAtOnEffectiveDomain.continuousWithinAt
    {f : H → Set.Ioi (⊥ : EReal)} {x : H}
    (hx : ContinuousAtOnEffectiveDomain f x) :
    ContinuousWithinAt (fun y : H ↦ (f y : EReal).toReal) (effectiveDomain f) x :=
  hx.2

-- Proof sketch: use the supporting-functional argument at a boundary point of the effective domain
-- to produce a nonzero outward normal `u`, then show that every `v ∈ ∂ f x` generates the ray
-- `v + ℝ≥0 • u ⊆ ∂ f x`; hence a nonempty subdifferential cannot be bounded.
/-- Proposition 16.17 (1): clause (i). If the effective domain has nonempty interior and `x` lies
on its boundary, then the subdifferential at `x` is either empty or unbounded. -/
theorem subdifferential_eq_empty_or_unbounded_of_mem_frontier_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f)
    (hinter : (interior (effectiveDomain f)).Nonempty)
    (hfrontier : x ∈ frontier (effectiveDomain f)) :
    (∂ f) x = ∅ ∨ ¬Bornology.IsBounded ((∂ f) x) := sorry

-- Proof sketch: apply the epigraph normal-cone characterization of Proposition 16.16 to a support
-- functional at the boundary point `(x, f x)` of `epi f`, obtaining a subgradient. Then combine
-- local boundedness of nearby subgradients with closedness and convexity of `∂ f x`, and conclude
-- weak compactness from the bounded closed convex criterion.
/-- Proposition 16.17 (2): clause (ii). At a continuity point of the finite-valued restriction of
`f` to its effective domain, the subdifferential is nonempty and weakly compact. -/
theorem subdifferential_nonempty_and_weaklyCompact_of_continuousAtOnEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtOnEffectiveDomain f x) :
    ((∂ f) x).Nonempty ∧ IsCompact (toWeakSpace ℝ H '' ((∂ f) x)) := sorry

-- Proof sketch: continuity on the effective domain gives a neighborhood on which the finite-valued
-- restriction is Lipschitz. For `y` in a smaller ball and `v ∈ ∂ f y`, test the subgradient
-- inequality on short increments `z` to obtain a uniform norm bound on all nearby subgradients.
/-- Proposition 16.17 (3): clause (iii). At a continuity point of the finite-valued restriction of
`f` to its effective domain, there is a positive radius for which the union of the nearby
subdifferentials is bounded. -/
theorem subdifferential_ball_union_bounded_of_continuousAtOnEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtOnEffectiveDomain f x) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Bornology.IsBounded (⋃ y ∈ Metric.ball x ρ, (∂ f) y) := sorry

-- Proof sketch: Corollary 8.39 transports nonemptiness of the continuity set to continuity at
-- every interior-domain point, and clause (ii) then supplies a nonempty subdifferential at each of
-- those points.
/-- Proposition 16.17 (4): clause (iv). If the effective-domain continuity set is nonempty, then
every interior point of the effective domain is a subdifferentiability point. -/
theorem interior_effectiveDomain_subset_subdifferentiabilityDomain_of_exists_continuityPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    (hcont : ∃ x : H, ContinuousAtOnEffectiveDomain f x) :
    interior (effectiveDomain f) ⊆ {x : H | SubdifferentiableAt f x} := sorry

end SubdifferentialContinuity

end ERealFunction
