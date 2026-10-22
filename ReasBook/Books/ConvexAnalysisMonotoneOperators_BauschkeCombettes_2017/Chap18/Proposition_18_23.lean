/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_54
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Example_16_62
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap18.Proposition_18_22

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open ERealFunction
open scoped Gradient InnerProductSpace Pointwise
open scoped Set

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: if `x ∈ interior C`, then some open ball around `x` lies in `C`, so
-- `Metric.infDist · C` vanishes on a neighborhood of `x`. The distance function is therefore
-- locally constant at `x`, hence Fréchet differentiable there with gradient `0`.
/-- Proposition 18.23 (1): clause (i). At an interior point of `C`, the distance function to `C`
is Fréchet differentiable with gradient `0`. -/
theorem distanceToSet_hasGradientAt_zero_of_mem_interior
    {C : Set H} {x : H} (hx : x ∈ interior C) :
    HasGradientAt (fun y ↦ Metric.infDist y C) (0 : H) x := sorry

section

variable {C : Set H}
variable (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

-- Proof sketch: Proposition 18.22 gives the Gâteaux derivative `0` at `x` from
-- `x ∉ spts C`. The source proof then combines Theorem 7.4, Example 16.62, and Proposition 17.41
-- to show that this Gâteaux differentiability cannot upgrade to Fréchet differentiability at a
-- boundary point.
/-- Proposition 18.23 (2): clause (ii)(a). At a boundary point of a closed convex set
that is not a support point, the distance function fails to be Fréchet differentiable. -/
theorem distanceToSet_not_differentiableAt_of_mem_frontier_and_not_mem_supportPoints
    {x : H} (hx : x ∈ frontier C) (hx_support : x ∉ spts C) :
    ¬ DifferentiableAt ℝ (fun y ↦ Metric.infDist y C) x := sorry

-- Proof sketch: Proposition 18.22 identifies non-support points of `C` with points where the
-- distance function has Gâteaux derivative `0`; apply it to the boundary point `x`.
/-- Proposition 18.23 (3): clause (ii)(a). At a boundary point of a closed convex set
that is not a support point, the distance function has Gâteaux derivative `0`. -/
theorem distanceToSet_hasGateauxDerivativeAt_zero_of_mem_frontier_and_not_mem_supportPoints
    {x : H} (hx : x ∈ frontier C) (hx_support : x ∉ spts C) :
    HasGateauxDerivativeAt (fun y ↦ Metric.infDist y C) (toDual ℝ H (0 : H)) x := sorry

-- Proof sketch: Example 16.62 identifies the subdifferential of `d_C` at a boundary support
-- point with `N[C] x ∩ Metric.closedBall 0 1`. Because `x ∈ spts C`, this set contains both `0`
-- and a nonzero normalized support direction, so Proposition 17.31 rules out Gâteaux
-- differentiability.
/-- Proposition 18.23 (4): clause (ii)(b). At a boundary support point of a closed convex
set, the distance function is not Gâteaux differentiable. -/
theorem distanceToSet_not_gateauxDifferentiableAt_of_mem_frontier_and_mem_supportPoints
    {x : H} (hx : x ∈ frontier C) (hx_support : x ∈ spts C) :
    ¬ GateauxDifferentiableAt (fun y ↦ Metric.infDist y C) x := sorry

/- Proposition 18.23 (5): clause (ii)(b) is exactly the boundary branch of Example 16.62. -/
recall subdifferential_distanceToSet_eq_normalCone_inter_closedBall_of_mem_frontier

end

section

variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "P" => P[C, hC_cheb]

-- Proof sketch: Example 16.62 gives the singleton subdifferential formula away from `C`,
-- Proposition 17.31 converts that singleton subdifferential into a Gâteaux derivative, and the
-- source argument upgrades this to the Fréchet derivative with gradient equal to the normalized
-- projection residual.
/-- Proposition 18.23 (6): clause (iii). Outside a nonempty closed convex set, the distance
function is Fréchet differentiable with gradient given by the normalized residual
`(Metric.infDist x C)⁻¹ • (x - P_C x)`. -/
theorem distanceToSet_hasGradientAt_normalized_residual_of_not_mem
    {x : H} (hx : x ∉ C) :
    HasGradientAt (fun y ↦ Metric.infDist y C) ((Metric.infDist x C)⁻¹ • (x - P x)) x := sorry

end

end
