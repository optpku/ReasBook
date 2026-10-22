/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Corollary_12_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 16.57 is the bounded-subdifferential criterion for Lipschitz
  continuity.
- `core/canonical`: the owner abstraction is the set-valued operator `∂ f.toEReal` together with
  its range `SetValuedOperator.range (∂ f.toEReal)`.
- `bridge/view`: the entrywise norm bound is derived from the range containment
  `SetValuedOperator.range (∂ f.toEReal) ⊆ Metric.closedBall (0 : H) β`, so the public statement
  should use that canonical owner directly.
-/
-- Proof sketch: apply Theorem 16.56 to the coerced function `f.toEReal`, whose effective domain
-- is all of `H` because `f` is real-valued and continuous. For any `x y`, the theorem yields a
-- point of the open segment and a subgradient `u` with `f y - f x = ⟪y - x, u⟫`. The range
-- hypothesis places `u` in `Metric.closedBall (0 : H) β`, hence `‖u‖ ≤ β`, and Cauchy--Schwarz
-- gives `|f y - f x| ≤ β * ‖y - x‖`. Applying the same argument with `x` and `y` exchanged
-- yields the `LipschitzWith β` estimate.
/-- Corollary 16.57: a continuous convex real-valued function on a real Hilbert space is
`β`-Lipschitz whenever the range of the subdifferential of its canonical `]-∞,+∞]`-valued
coercion is contained in `B(0;β)`. -/
theorem lipschitzWith_of_continuous_convexOn_univ_of_range_subdifferential_subset_closedBall
    (f : H → ℝ) (β : NNReal) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hsubgrad : SetValuedOperator.range (∂ f.toEReal) ⊆ Metric.closedBall (0 : H) β) :
    LipschitzWith β f := sorry

end SubdifferentialCalculus

end ERealFunction
