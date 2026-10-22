/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_43
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Theorem_17_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section DirectionalDerivativesAndSubgradients

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 17.24 identifies the subdifferential at `x` from a source-given
  support-function description of the directional derivative.
- `core/canonical`: the owner abstractions are `directionalDerivative`, `∂`, the support function
  `σ[·]`, and the closed-convex-hull biconjugate owner
  `biconjugate_indicator_eq_indicator_closedConvexHull`.
- `bridge/view`: Theorem 17.18 converts the directional derivative to `σ[(∂ f) x]`; the rest of
  the argument stays on the canonical conjugate/indicator owners, with no extra local wrapper. -/

-- Proof sketch: Theorem 17.18 identifies `directionalDerivative f x` with `σ[(∂ f) x]` at a
-- continuity point on the effective domain. Equality with `σ[C]` then gives equality of the
-- conjugate indicators, and Example 13.43 together with closedness and convexity of `∂ f x`
-- upgrades this to equality of the underlying sets with the closed convex hull of `C`.
/-- Proposition 17.24: if the directional derivative of a convex function at a continuity point on
the effective domain is the support function of `C`, then the subdifferential at that point is the
closed convex hull of `C`. -/
theorem subdifferential_eq_closedConvexHull_of_directionalDerivative_eq_supportFunction
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtOnEffectiveDomain f x) (C : Set H)
    (hσ : directionalDerivative f x = σ[C]) :
    (∂ f) x = closedConvexHull ℝ C := by
  have hx : x ∈ effectiveDomain f := hxcont.mem_effectiveDomain
  have hindicator :
      (ι[(∂ f) x]).asEReal = (ι[closedConvexHull ℝ C]).asEReal := by
    calc
      (ι[(∂ f) x]).asEReal = (directionalDerivative f x)∗ := by
        symm
        exact conjugate_directionalDerivative_eq_setIndicator_subdifferential f hconv hx
      _ = (σ[C])∗ := by simp [hσ]
      _ = (ι[closedConvexHull ℝ C]).asEReal := by
        simpa [conjugate_indicator_eq_supportFunction] using
          biconjugate_indicator_eq_indicator_closedConvexHull C
  ext u
  have hu : ((ι[(∂ f) x]).asEReal) u = ((ι[closedConvexHull ℝ C]).asEReal) u :=
    congrArg (fun g : H → EReal ↦ g u) hindicator
  by_cases hux : u ∈ (∂ f) x <;> by_cases huC : u ∈ closedConvexHull ℝ C <;>
    simp [indicator_apply, hux, huC] at hu ⊢

end DirectionalDerivativesAndSubgradients

end ERealFunction
