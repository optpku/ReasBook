/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ProximityOperator
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_51

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator
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

/-- A graph-nonempty Fitzpatrick function never attains `-∞`. -/
-- Proof sketch: choose a graph point `(y, v) ∈ gra A`; the corresponding Fitzpatrick supremand at
-- `(x, u)` is a finite real number, so the supremum defining `F_A(x, u)` is strictly above `⊥`.
theorem fitzpatrickFunction_ne_bot_of_graph_nonempty
    (A : SetValuedOperator H H) (hA_graph : (gra A).Nonempty) (p : H × H) :
    ⊥ < F[A] p := sorry

-- Proof sketch: if `(x, u) ∈ gra A`, then the infimum formula from Definition 20.51 reduces to
-- `⟪x, u⟫ - 0` because monotonicity gives the infimum term `0` and the graph point `(x, u)` shows
-- that this lower bound is attained.
/-- Proposition 20.56 (1): clause (i). On the graph of a monotone operator, the Fitzpatrick
function agrees with the pairing. -/
theorem fitzpatrickFunction_eq_inner_of_mem_graph
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) {x u : H} (hxu : (x, u) ∈ gra A) :
    F[A] (x, u) = ((⟪x, u⟫_ℝ : ℝ) : EReal) := sorry

-- Proof sketch: `fitzpatrickFunction_ne_bot_of_graph_nonempty` excludes the value `⊥`
-- everywhere, while clause (1) gives a graph point where `F_A` equals the finite pairing
-- `⟪x, u⟫`.
/-- If `gra A` is nonempty and `A` is monotone, then the Fitzpatrick function is proper. -/
theorem fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
    (A : SetValuedOperator H H) (hA_graph : (gra A).Nonempty) (hA_mono : A.IsMonotone) :
    IsProper F[A] := sorry

-- Proof sketch: unfold the definitions of `gra A⁻¹`, the graph indicator, and Fenchel
-- conjugation on `H × H`; the resulting supremum is exactly the defining supremum of `F_A`.
/-- Proposition 20.56 (2): clause (ii). The Fitzpatrick function is the Fenchel conjugate of the
sum of the indicator of `gra A⁻¹` and the pairing function `(x, u) ↦ ⟪x, u⟫`. -/
theorem fitzpatrickFunction_eq_conjugate_inverseGraphIndicator_add_pairing
    (A : SetValuedOperator H H) :
    F[A] =
      ((ι[gra A⁻¹]).asEReal + fun p : H × H ↦ ((⟪p.1, p.2⟫_ℝ : ℝ) : EReal))∗ := sorry

-- Proof sketch: the previous conjugate formula identifies `F_A` as a Fenchel conjugate, so
-- conjugation theory gives convexity and lower semicontinuity; the properness theorem above
-- packages the same owner through the canonical Chapter 9 bridge `properIoi`.
/-- Proposition 20.56 (3): clause (ii). If `gra A` is nonempty and `A` is monotone, then the
Fitzpatrick function belongs to `Γ₀(H × H)`. -/
theorem properIoi_fitzpatrickFunction_mem_gammaZero
    (A : SetValuedOperator H H) (hA_graph : (gra A).Nonempty) (hA_mono : A.IsMonotone) :
    properIoi (F[A])
      (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone A hA_graph hA_mono) ∈
        Γ₀(H × H) := sorry

-- Proof sketch: rewrite `F_A(x, u)` by the infimum formula. The inequality `F_A(x, u) ≤ ⟪x, u⟫`
-- is equivalent to nonnegativity of `⟪x - y, u - v⟫` for every `(y, v) ∈ gra A`, which is
-- exactly monotonicity of `gra A ∪ {(x, u)}`.
/-- Proposition 20.56 (4): clause (iii). The Fitzpatrick value at `(x, u)` lies below the pairing
if and only if adjoining `(x, u)` to `gra A` preserves monotonicity. -/
theorem fitzpatrickFunction_le_inner_iff_insert_graph_isMonotone
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (x u : H) :
    F[A] (x, u) ≤ ((⟪x, u⟫_ℝ : ℝ) : EReal) ↔
      SetRel.IsMonotone (Set.insert (x, u) (gra A)) := sorry

-- Proof sketch: replace every graph value `F_A(y, v)` in the defining supremum by the pairing
-- `⟪y, v⟫` using clause (1), then compare that supremum with the unrestricted supremum defining
-- the transpose-conjugate owner `((F[A])∗)ᵀ`.
/-- Proposition 20.56 (5): clause (iv). The Fitzpatrick function is dominated by its
transpose-conjugate owner `((F_A)^*)^T`. -/
theorem fitzpatrickFunction_le_conjugate_transpose
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) :
    F[A] ≤ ((F[A])∗)ᵀ := sorry

/-- Pointwise form of Proposition 20.56 (5). -/
theorem fitzpatrickFunction_le_conjugate_swap
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (x u : H) :
    F[A] (x, u) ≤ (F[A])∗ (u, x) := by
  simpa [transpose_apply] using
    show F[A] (x, u) ≤ (((F[A])∗)ᵀ) (x, u) from
      fitzpatrickFunction_le_conjugate_transpose A hA_mono (x, u)

-- Proof sketch: clause (3) places `F_A` in `Γ₀(H × H)`, so biconjugation bounds its conjugate by
-- the graph-indicator-plus-pairing function; evaluating the transpose-conjugate owner at a graph
-- point and combining clauses (1) and (5) forces equality.
/-- Proposition 20.56 (6): clause (v). At every graph point `(x, u)`, the transpose-conjugate
value `((F_A)^*)^T (x, u)` equals the pairing `⟪x, u⟫`. -/
theorem conjugateTranspose_fitzpatrickFunction_eq_inner_of_mem_graph
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone)
    {x u : H} (hxu : (x, u) ∈ gra A) :
    ((F[A])∗)ᵀ (x, u) = ((⟪x, u⟫_ℝ : ℝ) : EReal) := sorry

/-- Pointwise swapped-coordinate form of Proposition 20.56 (6). -/
theorem conjugate_fitzpatrickFunction_eq_inner_of_mem_graph
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone)
    {x u : H} (hxu : (x, u) ∈ gra A) :
    (F[A])∗ (u, x) = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  simpa [transpose_apply] using
    conjugateTranspose_fitzpatrickFunction_eq_inner_of_mem_graph A hA_mono hxu

-- Proof sketch: rewrite both Fitzpatrick functions from Definition 20.51; swapping the graph
-- coordinates turns `gra A` into `gra A⁻¹`, so the inverse-operator Fitzpatrick owner is the
-- transpose `F[A]ᵀ`.
/-- Proposition 20.56 (7): clause (vi). The Fitzpatrick function of the inverse operator is the
transpose of the Fitzpatrick function. -/
theorem fitzpatrickFunction_inverse_eq_transpose
    (A : SetValuedOperator H H) :
    F[A⁻¹] = (F[A])ᵀ := sorry

/-- Pointwise swapped-coordinate form of Proposition 20.56 (7). -/
theorem fitzpatrickFunction_eq_inverse_swap
    (A : SetValuedOperator H H) (x u : H) :
    F[A] (x, u) = F[A⁻¹] (u, x) := by
  simpa [transpose_apply] using
    (congrFun (fitzpatrickFunction_inverse_eq_transpose A) (u, x)).symm

-- Proof sketch: expand the Fitzpatrick supremum of `γ A`; graph points of `γ A` are exactly the
-- pairs `(y, γ • v)` with `(y, v) ∈ gra A`, and pulling the positive scalar `γ` out of the
-- supremand yields the displayed scaling identity.
/-- Proposition 20.56 (8): clause (vii). Positive scaling of the operator scales the Fitzpatrick
function by the same factor after rescaling the second variable. -/
theorem fitzpatrickFunction_smul_apply
    (A : SetValuedOperator H H) (x u : H) (γ : Set.Ioi (0 : ℝ)) :
    F[((γ : ℝ) • A)] (x, u) =
      (((γ : ℝ) : EReal) * F[A] (x, (γ : ℝ)⁻¹ • u)) := sorry

section Proximity

variable [CompleteSpace H]

attribute [local instance] ERealFunction.prod_completeSpace_l2

-- Proof sketch: clauses (1) and (6) give equality in Fenchel--Young at `((x, u), (u, x))` for
-- the canonical `Γ₀(H × H)` representative `properIoi (F[A]) ...`, so `(u, x)` lies in its
-- subdifferential at `(x, u)`. Unfolding the proximal-point condition for the unit Moreau
-- parameter then gives `(x, u) = Prox_{F_A}(x + u, x + u)`.
/-- Proposition 20.56 (9): clause (viii). Every graph point of a monotone operator is a fixed
contact point of the proximity operator of its Fitzpatrick function. -/
theorem eq_prox_properIoi_fitzpatrickFunction_of_mem_graph
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone)
    {x u : H} (hxu : (x, u) ∈ gra A) :
    (x, u) =
      Prox[
        properIoi (F[A])
          (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone A ⟨(x, u), hxu⟩ hA_mono),
        properIoi_fitzpatrickFunction_mem_gammaZero A ⟨(x, u), hxu⟩ hA_mono] (x + u, x + u) :=
  sorry

end Proximity

end

end SetValuedOperator
