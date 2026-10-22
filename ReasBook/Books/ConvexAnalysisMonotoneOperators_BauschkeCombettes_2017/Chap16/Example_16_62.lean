/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Example_12_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

namespace ERealFunction

noncomputable section

section SubdifferentialCalculus

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

/-- Classical decidability of membership in `C`, used to state the piecewise distance
subdifferential formula. -/
local instance instDecidablePredDistanceToSetSet :
    DecidablePred (fun x : H ↦ x ∈ C) := Classical.decPred _

/-- Classical decidability of membership in `frontier C`, used to state the boundary branch of the
distance subdifferential formula. -/
local instance instDecidablePredDistanceToSetFrontier :
    DecidablePred (fun x : H ↦ x ∈ frontier C) := Classical.decPred _

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "P" => P[C, hC_cheb]

/- Source/core/bridge triage:
- `source-facing`: Example 16.62 is the piecewise subdifferential formula for the
  distance-to-set function.
- `core/canonical`: the owner declarations are `Metric.infDist`, `P[C, hC]`, `N[C]`, and `∂`.
- `bridge/view`: the boundary and exterior branch lemmas are derived views of this piecewise owner.

The refinement therefore keeps the piecewise formula as the main source-facing statement and
derives the reusable branch lemmas from it instead of maintaining parallel standalone copies. -/

-- Proof sketch: write `d_C = ι_C □ ‖·‖` using the projection formula for the distance to a closed
-- convex set, then apply the exact subdifferential formula for infimal convolution at the
-- projection point to `(fun y ↦ Metric.infDist y C).toEReal`. Use the indicator subdifferential
-- formula `∂ ι_C = N_C`, the norm subdifferential formula, and the projection/normal-cone
-- characterization to simplify the three cases `x ∉ C`, `x ∈ frontier C`, and `x ∈ interior C`.
/-- Example 16.62: for a nonempty closed convex subset `C` of a real Hilbert space, the
subdifferential of the distance-to-set function is the singleton containing the normalized
projection residual outside `C`, the intersection `N[C] x ∩ Metric.closedBall (0 : H) 1` on the
boundary, and `{0}` off the boundary inside `C` (equivalently, on `interior C`). -/
theorem subdifferential_distanceToSet_eq_piecewise_of_nonempty_isClosed_convex
    (x : H) :
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x =
      if hxC : x ∈ C then
        if hxbdry : x ∈ frontier C then
          N[C] x ∩ Metric.closedBall (0 : H) 1
        else
          ({0} : Set H)
      else
        ({(Metric.infDist x C)⁻¹ • (x - P x)} : Set H) := sorry

/-- Exterior branch of Example 16.62: away from `C`, the distance-to-set subdifferential is the
singleton containing the normalized projection residual. -/
theorem subdifferential_distanceToSet_eq_singleton_normalizedResidual_of_not_mem
    {x : H} (hx : x ∉ C) :
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x =
      ({(Metric.infDist x C)⁻¹ • (x - P x)} : Set H) := by
  simpa [hx] using
    subdifferential_distanceToSet_eq_piecewise_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex x

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}

/-- Boundary branch of Example 16.62: at a frontier point of a nonempty closed convex set, the
subdifferential of the distance-to-set function is `N[C] x ∩ Metric.closedBall (0 : H) 1`. -/
theorem subdifferential_distanceToSet_eq_normalCone_inter_closedBall_of_mem_frontier
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {x : H} (hx : x ∈ frontier C) :
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x =
      N[C] x ∩ Metric.closedBall (0 : H) 1 := by
  have hxC : x ∈ C := hC_closed.frontier_subset hx
  have hC_nonempty : C.Nonempty := ⟨x, hxC⟩
  simpa [hxC, hx] using
    subdifferential_distanceToSet_eq_piecewise_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex x

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {C : Set H}

/-- Interior branch of Example 16.62: on `interior C`, the distance-to-set subdifferential is the
singleton `{0}`. -/
theorem subdifferential_distanceToSet_eq_singleton_zero_of_mem_interior
    {x : H} (hx : x ∈ interior C) :
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x = ({0} : Set H) := sorry

end

end SubdifferentialCalculus

end

end ERealFunction
