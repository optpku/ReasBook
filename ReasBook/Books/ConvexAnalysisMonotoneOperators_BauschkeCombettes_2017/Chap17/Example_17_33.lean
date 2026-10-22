/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Example_16_62
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

namespace ERealFunction

noncomputable section

section DifferentiabilityOfDistanceCompositions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

/-- Classical decidability of membership in `C`, used to state the piecewise subdifferential
formula for compositions with the distance to `C`. -/
local instance instDecidablePredCompInfDistSet :
    DecidablePred (fun x : H ↦ x ∈ C) := Classical.decPred _

/-- Classical decidability of membership in `frontier C`, used to state the boundary branch of the
subdifferential formula for compositions with the distance to `C`. -/
local instance instDecidablePredCompInfDistFrontier :
    DecidablePred (fun x : H ↦ x ∈ frontier C) := Classical.decPred _

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "P" => P[C, hC_cheb]

/- Source/core/bridge triage:
- `source-facing`: Example 17.33 is the piecewise subdifferential formula for
  `x ↦ φ (Metric.infDist x C)`.
- `core/canonical`: the owner surface is `Metric.infDist`, `∂`, `P`, `N[C]`, and
  the one-sided scalar derivative owner `(φ.toEReal)′₊(0)` at the boundary value `0`.
- `bridge/view`: Proposition 17.32 composes subdifferentials with a differentiable convex scalar
  function away from the boundary, while Example 16.62 provides the distance-to-set branch
  formulas.

The refinement therefore keeps the source-facing theorem and rewrites it directly against those
chapter owners instead of parallel lower-level spellings. -/

-- Proof sketch: away from the boundary, apply Proposition 17.32 to
-- `f := fun y ↦ Metric.infDist y C`, using the convexity and continuity of `Metric.infDist` and
-- Example 16.62 for `∂ d_C`. At boundary points, `Metric.infDist x C = 0`, so only the
-- one-sided scalar behavior along `ℝ₊` is available; the correct branch is therefore governed by
-- the canonical right derivative `(φ.toEReal)′₊(0)` rather than the ambient derivative `deriv φ 0`.
-- If `φ` is even, Proposition 11.7(ii) upgrades even convexity to monotonicity on `ℝ₊`, reducing
-- to the previous case; then rewrite the scaled distance subdifferential branch-by-branch to
-- obtain the displayed piecewise formula.
/-- Example 17.33: if `C` is a nonempty closed convex subset of a real Hilbert space and
`φ : ℝ → ℝ` is convex, differentiable on `ℝ₊`, and either increasing on `ℝ₊` or even, then the
subdifferential of `x ↦ φ (d(x, C))` is the scaled projection residual outside `C`, the
intersection `N[C] x ∩ Metric.closedBall (0 : H) (φ′₊(0))` on `frontier C`, and `{0}` on the
interior of `C`, encoded here by the corresponding piecewise formula; the boundary radius is the
canonical right derivative of `φ.toEReal` at `0`, rendered below as `((φ.toEReal)′₊(0)).toReal`.
-/
theorem
    subdifferential_comp_distanceToSet_eq_piecewise_of_nonempty_isClosed_convex
    (φ : ℝ → ℝ) (hφconv : _root_.ConvexOn ℝ Set.univ φ)
    (hφdiff : DifferentiableOn ℝ φ (Set.Ici (0 : ℝ)))
    (hφ_mono_or_even : MonotoneOn φ (Set.Ici (0 : ℝ)) ∨ Function.Even φ)
    (x : H) :
    (∂ (fun y : H ↦ φ (Metric.infDist y C)).toEReal) x =
      if hxC : x ∈ C then
        if hxbdry : x ∈ frontier C then
          N[C] x ∩ Metric.closedBall (0 : H) (((φ.toEReal)′₊(0)).toReal)
        else
          ({0} : Set H)
      else
        ({(deriv φ (Metric.infDist x C) / Metric.infDist x C) • (x - P x)} : Set H) :=
      sorry

end DifferentiabilityOfDistanceCompositions

end

end ERealFunction
