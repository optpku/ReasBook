/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u v

namespace SetValuedOperator

noncomputable section

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.23 is the maximal-monotonicity theorem for the componentwise
  product operator on the Hilbert product `H × K`, written in ordinary pair coordinates.
- `core/canonical`: the owner abstractions are the chapter's product operator `A × B` from
  `Definition_20_1` and maximal monotonicity `Maximal IsMonotone`.
- `bridge/view`: Chapter 9 only supplies the local `ℓ²` Hilbert-space structure on the raw pair
  type `H × K`; it is not a second public owner. -/

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: use `Maximal.mem_iff` for `A` and `B`. Membership in the product operator is
-- componentwise by `mem_prod_iff`, and the Chapter 9 `ℓ²` inner product on `H × K` splits into
-- the sum of the two coordinate pairings. The product Minty criterion therefore separates into the
-- two component Minty criteria, yielding maximal monotonicity of `A × B`.
/-- Proposition 20.23: if `A` and `B` are maximally monotone, then the componentwise product
operator `(x, y) ↦ A x × B y` is maximally monotone on the Chapter 9 `ℓ²` Hilbert product
structure on the raw pair type `H × K`. -/
theorem Maximal.prod
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    Maximal IsMonotone (A × B) := sorry

end

end SetValuedOperator
