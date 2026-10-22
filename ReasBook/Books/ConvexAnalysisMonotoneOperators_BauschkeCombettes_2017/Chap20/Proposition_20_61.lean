/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_56
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Theorem_20_46

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open ERealFunction
open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: Proposition 20.56 (2) identifies `F_A` with the conjugate of the canonical
-- inverse-graph indicator owner `(ι[gra A⁻¹]).asEReal` plus the pairing on `H × H`; applying
-- Fenchel conjugation once more gives the biconjugate of that sum.
/-- Proposition 20.61 (1): clause (i). The Fenchel conjugate of the Fitzpatrick function is the
Fenchel biconjugate of the inverse-graph indicator plus the pairing on `H × H`. -/
theorem conjugate_fitzpatrickFunction_eq_biconjugate_inverseGraphIndicator_add_pairing
    (A : SetValuedOperator H H) :
    (F[A])∗ =
      (((ι[gra A⁻¹]).asEReal + fun p : H × H ↦ ((⟪p.1, p.2⟫_ℝ : ℝ) : EReal)))∗∗ := sorry

-- Proof sketch: combine clause (1) with the lower-semicontinuous-convex-envelope domain inclusion
-- from Proposition 9.8 (iv), applied to the inverse-graph indicator plus pairing.
/-- Proposition 20.61 (2): clause (ii), first inclusion. The convex hull of `gra A⁻¹` lies in the
effective domain of `F_A^*`. -/
theorem convexHull_inverseGraph_subset_dom_conjugate_fitzpatrickFunction
    (A : SetValuedOperator H H) :
    convexHull ℝ (gra A⁻¹) ⊆ ERealFunction.dom ((F[A])∗) := sorry

-- Proof sketch: use clause (1) and the complementary domain inclusion from Proposition 9.8 (iv)
-- for the lower-semicontinuous convex envelope, together with the Hilbert-space biconjugation
-- bridge from Proposition 13.45 / 13.46 for the inverse-graph indicator plus pairing.
/-- Proposition 20.61 (3): clause (ii), second inclusion. The effective domain of `F_A^*` is
contained in the closure of the convex hull of `gra A⁻¹`. -/
theorem dom_conjugate_fitzpatrickFunction_subset_closure_convexHull_inverseGraph
    [CompleteSpace H] (A : SetValuedOperator H H) :
    ERealFunction.dom ((F[A])∗) ⊆ closure (convexHull ℝ (gra A⁻¹)) := sorry

section

variable {H : Type u} [TopologicalSpace H] [AddCommMonoid H] [Module ℝ H]

-- Proof sketch: every point of `gra A⁻¹` has first coordinate in `range A` and second coordinate
-- in `dom A`; pass to convex hulls and then take closures in the product space.
/-- Proposition 20.61 (4): clause (ii), third inclusion. The closed convex hull of `gra A⁻¹`
lies in the product of the closed convex hulls of `range A` and `dom A`. -/
theorem closure_convexHull_inverseGraph_subset_closure_convexHull_range_prod_closure_convexHull_dom
    (A : SetValuedOperator H H) :
    closure (convexHull ℝ (gra A⁻¹)) ⊆
      closure (convexHull ℝ A.range) ×ˢ closure (convexHull ℝ A.dom) := sorry

end

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: extend `A` to a maximally monotone operator and compare Fitzpatrick functions via
-- the order-reversal property of Fenchel conjugation; Proposition 20.58 then yields the lower
-- bound by the pairing.
/-- Proposition 20.61 (5): clause (iii). For a monotone operator, the Fenchel conjugate of the
Fitzpatrick function dominates the pairing after swapping the two variables. -/
theorem inner_le_conjugate_fitzpatrickFunction_swap
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (x u : H) :
    ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ (F[A])∗ (u, x) := sorry

-- Proof sketch: combine clause (5) with Proposition 20.56 (6). At graph points, Proposition
-- 20.56 (6) gives equality with the pairing; conversely, equality in the conjugate contact set
-- forces membership in the graph by maximal monotonicity.
/-- Proposition 20.61 (6), atomic contact-set form: a point belongs to the graph of a maximally
monotone operator exactly when the Fenchel conjugate of its Fitzpatrick function attains the
pairing after swapping the two variables. -/
theorem Maximal.mem_graph_iff_conjugate_fitzpatrickFunction_eq_inner
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x u : H) :
    (x, u) ∈ A.graph ↔ (F[A])∗ (u, x) = ((⟪x, u⟫_ℝ : ℝ) : EReal) := sorry

/-- Proposition 20.61 (6): clause (iv). A maximally monotone operator is the pairing-contact
operator of the transposed Fenchel conjugate of its Fitzpatrick function. -/
theorem Maximal.eq_pairingEqualityOperator_conjugateTranspose_fitzpatrickFunction
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    A = pairingEqualityOperator (((F[A])∗)ᵀ) := by
  ext x u
  simpa [transpose_apply] using
    (Maximal.mem_graph_iff_conjugate_fitzpatrickFunction_eq_inner hA x u)

/-- Proposition 20.61 (6), graph-form companion: the graph of a maximally monotone operator is
exactly the pairing-contact set of the Fenchel conjugate of its Fitzpatrick function after
swapping the variables. -/
theorem Maximal.graph_eq_setOf_conjugate_fitzpatrickFunction_eq_inner
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    A.graph =
      {p | (F[A])∗ (p.2, p.1) = ((⟪p.1, p.2⟫_ℝ : ℝ) : EReal)} := by
  ext p
  exact Maximal.mem_graph_iff_conjugate_fitzpatrickFunction_eq_inner hA p.1 p.2

end

end SetValuedOperator
