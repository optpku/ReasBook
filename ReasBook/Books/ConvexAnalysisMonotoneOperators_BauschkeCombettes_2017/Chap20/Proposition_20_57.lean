/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_51
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator
open ERealFunction

universe u v

namespace SetValuedOperator

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.57 is the textbook product formula for the Fitzpatrick function
  and the induced first-coordinate domain projection identity.
- `core/canonical`: the owner abstractions are the chapter's `SetValuedOperator.prod` and the
  Fitzpatrick owner `F[_]` from Definition 20.51.
- `bridge/view`: this file only records how those two owners interact on the Chapter 9 raw-product
  `ℓ²` Hilbert structure and on `dom`; it does not introduce any new product wrapper. -/

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2 prod_normedSpace_l2
  prod_innerProductSpace_l2

-- Proof sketch: expand the Fitzpatrick supremum of `A × B` over graph points, rewrite graph
-- membership componentwise through `mem_prod_iff`, and split the inner product on
-- `H × K` equipped with the Chapter 9 `ℓ²` product structure into the sum of its `H`- and
-- `K`-components. The supremum over the product graph then separates into the sum of the two
-- Fitzpatrick suprema.
/-- Proposition 20.57 (1): the Fitzpatrick function of the componentwise product operator
`(x, y) ↦ A x × B y` is the sum of the Fitzpatrick functions of `A` and `B` on the Chapter 9
raw-pair `ℓ²` Hilbert product `H × K`. -/
theorem fitzpatrickFunction_prod_apply
    (A : SetValuedOperator H H) (B : SetValuedOperator K K)
    (x u : H) (y v : K) :
    F[(A × B)] ((x, y), (u, v)) = F[A] (x, u) + F[B] (y, v) := sorry

-- Proof sketch: use the product formula from part (1). When `gra A` and `gra B` are nonempty,
-- the Fitzpatrick functions of `A`, `B`, and the componentwise product operator never take the
-- value `⊥`, so membership in `ERealFunction.dom` is controlled exactly by finiteness above. Then
-- the sum formula shows that a product point lies in the first-coordinate projection of
-- `dom F_{A×B}` exactly when its two components lie in the corresponding first-coordinate
-- projections for `F_A` and `F_B`.
/-- Proposition 20.57 (2): if `gra A` and `gra B` are nonempty, then the first-coordinate
projection of `dom F_{A × B}` is the product of the first-coordinate projections of `dom F_A`
and `dom F_B`. -/
theorem fst_image_dom_fitzpatrickFunction_prod
    (A : SetValuedOperator H H) (B : SetValuedOperator K K)
    (hA_graph : A.graph.Nonempty) (hB_graph : B.graph.Nonempty) :
    Prod.fst '' ERealFunction.dom (F[(A × B)]) =
      (Prod.fst '' ERealFunction.dom (F[A])) ×ˢ
        (Prod.fst '' ERealFunction.dom (F[B])) :=
  sorry

end SetValuedOperator
