/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_35
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_67
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_70

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise
open WithLp

universe u v

namespace ERealFunction

section SubdifferentialOfComposition

open SetValuedOperator

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: apply Corollary 16.48 to the canonical constrained objective
-- `g + ι[gra F]`, using the `sri` regularity hypothesis to identify its product-space
-- subdifferential with `∂ g + N[gra F]`. The normal-cone term rewrites via the coderivative, and
-- Proposition 16.70 gives the reverse inclusion for the same active graph point `(xbar, ybar)`.
/-- Theorem 16.71: if `g ∈ Γ₀(H × K)`, `F : H → 2^K` has closed convex graph, `(xbar, ybar)` is
an active graph point for the canonical infimal projection
`marginalFunction (g + ι[gra F])`, and `((0 : H), (0 : K)) ∈ sri (gra F - dom g)`, then the
subdifferential of that infimal projection
at `xbar` is exactly `⋃ (u, v) ∈ (∂ g) (xbar, ybar), u + D*F(xbar, ybar)(v)`. -/
theorem subdifferential_eq_iUnion_add_coderivative_of_setValuedInfimalProjection
    (g : H × K → Set.Ioi (⊥ : EReal)) (F : SetValuedOperator H K) (xbar : H) (ybar : K)
    (hg : g ∈ Γ₀(H × K)) (hgraph_closed : IsClosed (gra F)) (hgraph_convex : Convex ℝ (gra F))
    (hybar : ybar ∈ F xbar)
    (hactive : marginalFunction (g + ι[gra F]) xbar = (g (xbar, ybar) : EReal))
    (hregular : ((0 : H), (0 : K)) ∈ sri (gra F - effectiveDomain g)) :
    (∂ marginalFunction (g + ι[gra F])) xbar =
      ⋃ p ∈ (∂ g) (xbar, ybar), ({p.1} : Set H) + (((D* F) xbar) ybar p.2) := sorry

end SubdifferentialOfComposition

end ERealFunction
