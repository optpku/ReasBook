/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open ERealFunction

universe u

namespace SetValuedOperator

noncomputable section

section BivariateFenchelEquality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Theorem 20.46 studies the operator defined by the contact set
  `F∗ (u, x) = ⟪x, u⟫`.
- `core/canonical`: the owner abstraction is the pairing-contact operator attached to a bivariate
  function on `H × H`.
- `bridge/view`: the source operator is that owner applied to the transpose-conjugate `(F∗)ᵀ`. -/

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- The set-valued operator whose graph is the pairing-contact set
`{(x, u) | F (x, u) = ⟪x, u⟫}`. -/
def pairingEqualityOperator {α : Type*} [CoeTC α EReal] (F : H × H → α) :
    SetValuedOperator H H :=
  fun x ↦ {u | (F (x, u) : EReal) = ((⟪x, u⟫_ℝ : ℝ) : EReal)}

-- Proof sketch: unfold `pairingEqualityOperator` and `SetValuedOperator.graph`; graph membership
-- is exactly the defining pairing-contact equality.
/-- A pair `(x, u)` lies in the graph of `pairingEqualityOperator F` exactly when it satisfies the
pairing equality `F (x, u) = ⟪x, u⟫`. -/
theorem mem_graph_pairingEqualityOperator_iff
    {α : Type*} [CoeTC α EReal] (F : H × H → α) (x u : H) :
    (x, u) ∈ (pairingEqualityOperator F).graph ↔
      (F (x, u) : EReal) = ((⟪x, u⟫_ℝ : ℝ) : EReal) := sorry

-- Proof sketch: if `(x, u)` and `(y, v)` satisfy the defining equality for `A`, convexity of
-- the Fenchel conjugate `(F∗)` from the canonical owner `conjugate_mem_gamma`, combined with the
-- lower bound `F* ≥ ⟪·, ·⟫`, yields
-- `0 ≤ ⟪x - y, u - v⟫`.
/-- Theorem 20.46 (1): if `F*(u, x) ≥ ⟪x, u⟫` for all `x, u`, then the pairing-contact operator
of the transpose-conjugate `(F∗)ᵀ` is monotone; equivalently, the equality locus
`F*(u, x) = ⟪x, u⟫` defines a monotone operator. -/
theorem pairingEqualityOperator_conjugateTranspose_isMonotone
    (F : H × H → EReal)
    (hFstar_ge : ∀ x u : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ F∗ (u, x)) :
    (pairingEqualityOperator ((F∗)ᵀ)).IsMonotone := sorry

section HilbertSpace

variable [CompleteSpace H]

-- Proof sketch: apply the maximal-monotonicity graph criterion. For a pair monotonically related
-- to every point of the graph, combine the quadratic kernel from Lemma 20.45 with the lower
-- bounds `F ≥ ⟪·, ·⟫` and `F* ≥ ⟪·, ·⟫` to force equality in the Fenchel relation and recover
-- graph membership.
/-- Theorem 20.46 (2): on a real Hilbert space, if moreover `F(x, u) ≥ ⟪x, u⟫` for all `x, u`,
then the same operator is maximally monotone. -/
theorem pairingEqualityOperator_conjugateTranspose_isMaximallyMonotone
    (F : H × H → EReal) (hF_conv : IsConvex F)
    (hFstar_proper : IsProper F∗)
    (hFstar_ge : ∀ x u : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ F∗ (u, x))
    (hF_ge : ∀ x u : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ F (x, u)) :
    Maximal IsMonotone (pairingEqualityOperator ((F∗)ᵀ)) := sorry

end HilbertSpace

end BivariateFenchelEquality

end

end SetValuedOperator
