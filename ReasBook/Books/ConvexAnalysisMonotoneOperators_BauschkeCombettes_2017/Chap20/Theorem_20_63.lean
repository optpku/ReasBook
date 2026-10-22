/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Corollary_14_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_20
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_56
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Theorem_20_46

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open ERealFunction

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

/-- The proximal-average autoconjugate candidate
`G = pav(F_A, F_A^{*T})` attached to a monotone operator with nonempty graph. -/
noncomputable def fitzpatrickProximalAverage
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (hA_graph : A.graph.Nonempty) :
    H × H → Set.Ioi (⊥ : EReal) :=
  let FA :=
    properIoi (F[A]) (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone A hA_graph hA_mono)
  let hFA := properIoi_fitzpatrickFunction_mem_gammaZero A hA_graph hA_mono
  properIoi
    (pav(FA, FA∗ᵀ[hFA]))
    (isProper_proximalAverage
      FA
      (FA∗ᵀ[hFA])
      hFA
      (gammaZeroConjugateTranspose_mem_gammaZero hFA))

/-- The set-valued operator `B` whose graph is the pairing-contact set of
`fitzpatrickProximalAverage A hA_mono hA_graph`. -/
abbrev fitzpatrickProximalAverageExtension
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (hA_graph : A.graph.Nonempty) :
    SetValuedOperator H H :=
  pairingEqualityOperator (fitzpatrickProximalAverage A hA_mono hA_graph)

-- Proof sketch: this is the canonical graph-membership lemma
-- `mem_graph_pairingEqualityOperator_iff` specialized to the proximal-average owner.
/-- A pair `(x, u)` lies in the graph of `fitzpatrickProximalAverageExtension A hA_mono hA_graph`
exactly when the proximal average `pav(F_A, F_A^{*T})` equals the pairing `⟪x, u⟫` at `(x, u)`. -/
@[simp] theorem mem_graph_fitzpatrickProximalAverageExtension_iff
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (hA_graph : A.graph.Nonempty) (x u : H) :
    (x, u) ∈ (fitzpatrickProximalAverageExtension A hA_mono hA_graph).graph ↔
      (fitzpatrickProximalAverage A hA_mono hA_graph (x, u) : EReal) =
        ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  simpa [fitzpatrickProximalAverageExtension] using
    (mem_graph_pairingEqualityOperator_iff
      (fitzpatrickProximalAverage A hA_mono hA_graph) x u)

-- Proof sketch: let `F_A` be `properIoi (F[A]) ...` and let
-- `G := pav(F_A, F_A^{*T})`, encoded by `fitzpatrickProximalAverage A hA_mono hA_graph`.
-- Proposition 20.56(3) puts `F_A` in `Γ₀(H × H)`, Proposition 16.66 identifies the proximity
-- operator of `F_A^{*T}`, and Corollary 14.8 shows that `G ∈ Γ₀(H × H)` with
-- `G^* = G^T`, hence `G` is autoconjugate. Corollary 20.47 then yields maximal monotonicity of
-- the pairing-equality operator. For graph inclusion, Proposition 20.56(9), Corollary 14.8(4),
-- Proposition 16.66, and Proposition 16.65 show that every `(x, u) ∈ gra A` is a fixed contact
-- point of `G`, so `(x, u)` lies in the graph of the extension operator.
section HilbertSpace

variable [CompleteSpace H]

attribute [local instance] ERealFunction.prod_completeSpace_l2

/-- Theorem 20.63: if `A` is monotone and `gra A` is nonempty, set
`G = pav(F_A, F_A^{*T})` and define `B` by
`gra B = {(x, u) | G(x, u) = ⟪x, u⟫}`. Then
`fitzpatrickProximalAverageExtension A hA_mono hA_graph` is a maximally monotone extension of
`A`. -/
theorem fitzpatrickProximalAverageExtension_isMaximallyMonotone_and_extends
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (hA_graph : A.graph.Nonempty) :
    Maximal IsMonotone (fitzpatrickProximalAverageExtension A hA_mono hA_graph) ∧
      A ≤ fitzpatrickProximalAverageExtension A hA_mono hA_graph :=
  sorry

/-- Theorem 20.63, graph-form companion: every graph point of `A` lies in the graph of the
proximal-average extension. This is the graph-containment reformulation of the canonical extension
claim `A ≤ fitzpatrickProximalAverageExtension A hA_mono hA_graph`. -/
theorem graph_subset_fitzpatrickProximalAverageExtension
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (hA_graph : A.graph.Nonempty) :
    A.graph ⊆ (fitzpatrickProximalAverageExtension A hA_mono hA_graph).graph := by
  intro p hp
  exact
    (fitzpatrickProximalAverageExtension_isMaximallyMonotone_and_extends A hA_mono hA_graph).2 p.1
      (by simpa using hp)

end HilbertSpace

end

end SetValuedOperator
