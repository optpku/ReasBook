/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_47
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_35
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_67
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_59

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u v

namespace ERealFunction

noncomputable section

section SubdifferentialOfComposition

open SetValuedOperator

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: rewrite the target through the canonical marginal owner with
-- Proposition 16.59, so it suffices to show `(w, 0) ∈ ∂ (g + ι[gra F]) (xbar, y)`. The
-- witness `w ∈ {p.1} + D*F(xbar, y)(p.2)` provides `v ∈ D*F(xbar, y)(p.2)` with `w = p.1 + v`,
-- hence `(v, -p.2) ∈ N[gra F] (xbar, y)`. Example 16.13 turns this normal vector into a
-- subgradient of `ι[gra F]`, and adding its inequality to the subgradient inequality for
-- `p ∈ (∂ g) (xbar, y)` yields the desired product-space subgradient.
/-- Proposition 16.70: at an active graph point for the marginal representation
`marginalFunction (pointwiseAdd g (ι[gra F]))`, every active subgradient of `g` at `(xbar, y)`
together with the coderivative contribution `D*F(xbar, y)(v)` yields a subgradient of that
infimal projection at `xbar`. -/
theorem subgradient_coderivative_sum_subset_subdifferential_of_setValuedInfimalProjection
    (g : H × K → Set.Ioi (⊥ : EReal)) (F : SetValuedOperator H K) {xbar : H} :
    {w : H |
      ∃ y ∈ F xbar,
        marginalFunction (pointwiseAdd g (ι[gra F])) xbar = (g (xbar, y) : EReal) ∧
          ∃ p ∈ (∂ g) (xbar, y),
            w ∈ ({p.1} : Set H) + (((D* F) xbar) y p.2)} ⊆
      (∂ marginalFunction (pointwiseAdd g (ι[gra F]))) xbar := by
  let G : H × K → Set.Ioi (⊥ : EReal) := pointwiseAdd g (ι[gra F])
  intro w hw
  rcases hw with ⟨y, hy, hactive, ⟨u₀, v₀⟩, hp, hw⟩
  rcases Set.mem_add.mp hw with ⟨u, hu, v, hv, huv⟩
  have hu : u = u₀ := Set.mem_singleton_iff.mp hu
  subst u
  have hmarginal_eq :
      marginalFunction G xbar = (G (xbar, y) : EReal) := by
    apply le_antisymm
    · exact marginalFunction_le G xbar y
    · simpa [G, pointwiseAdd_apply, hy] using hactive.ge
  have hxy_graph : (xbar, y) ∈ gra F := by simpa using hy
  have hnormal :
      ∀ z ∈ gra F, ⟪z - (xbar, y), (v, -v₀)⟫_ℝ ≤ 0 := by
    have hnormal0 : (v, -v₀) ∈ Set.normalCone (gra F) (xbar, y) :=
      (mem_coderivative_iff F xbar y v₀ v).mp hv
    rw [Set.normalCone_of_mem hxy_graph] at hnormal0
    have hnormal_iff :
        innerSupremumOn (gra F - ({(xbar, y)} : Set (H × K))) (v, -v₀) ≤ 0 ↔
          ∀ z ∈ gra F, ⟪z - (xbar, y), (v, -v₀)⟫_ℝ ≤ 0 := by
      exact
        (innerSupremumOn_sub_singleton_le_zero_iff :
          innerSupremumOn (gra F - ({(xbar, y)} : Set (H × K))) (v, -v₀) ≤ 0 ↔
            ∀ z ∈ gra F, ⟪z - (xbar, y), (v, -v₀)⟫_ℝ ≤ 0)
    exact
      hnormal_iff.1 hnormal0
  rw [mem_subdifferential_iff] at hp
  have hq :
      ∀ z : H × K,
        (⟪z - (xbar, y), (v, -v₀)⟫_ℝ : EReal) + (ι[gra F] (xbar, y) : EReal) ≤
          (ι[gra F] z : EReal) := by
    intro z
    by_cases hz_graph : z ∈ gra F
    · have hz0 : ⟪z - (xbar, y), (v, -v₀)⟫_ℝ ≤ 0 := hnormal z hz_graph
      simpa [ERealFunction.indicator, hxy_graph, hz_graph] using hz0
    · simp [ERealFunction.indicator, hxy_graph, hz_graph]
  have hw_prod :
      (w, (0 : K)) ∈ (∂ G) (xbar, y) := by
    rw [mem_subdifferential_iff]
    intro z
    rcases z with ⟨x', y'⟩
    have hp' := hp (x', y')
    have hq' := hq (x', y')
    by_cases hz : y' ∈ F x'
    · have hq'' :
          (⟪(x', y') - (xbar, y), (v, -v₀)⟫_ℝ : EReal) ≤ 0 := by
        have hz_graph : (x', y') ∈ gra F := by
          simpa [SetValuedOperator.mem_graph] using hz
        simpa [ERealFunction.indicator, hxy_graph, hz_graph] using hq'
      have hsum := add_le_add hp' hq''
      have hinner :
          ⟪(x', y') - (xbar, y), (u₀, v₀)⟫_ℝ + ⟪(x', y') - (xbar, y), (v, -v₀)⟫_ℝ =
            ⟪x' - xbar, w⟫_ℝ := by
        change
          (⟪x' - xbar, u₀⟫_ℝ + ⟪y' - y, v₀⟫_ℝ) +
              (⟪x' - xbar, v⟫_ℝ + ⟪y' - y, -v₀⟫_ℝ) =
            ⟪x' - xbar, w⟫_ℝ
        simp only [inner_neg_right]
        abel_nf
        rw [← inner_add_right, huv]
      have hpair_zero :
          ⟪(x', y') - (xbar, y), (w, (0 : K))⟫_ℝ = ⟪x' - xbar, w⟫_ℝ := by
        change ⟪x' - xbar, w⟫_ℝ + ⟪y' - y, (0 : K)⟫_ℝ = ⟪x' - xbar, w⟫_ℝ
        simp
      have hinnerE :
          (⟪x' - xbar, w⟫_ℝ : EReal) =
            ((⟪(x', y') - (xbar, y), (u₀, v₀)⟫_ℝ +
                ⟪(x', y') - (xbar, y), (v, -v₀)⟫_ℝ : ℝ) : EReal) := by
        exact_mod_cast hinner.symm
      calc
        (⟪(x', y') - (xbar, y), (w, (0 : K))⟫_ℝ : EReal) +
            (G (xbar, y) : EReal)
            =
            (((⟪(x', y') - (xbar, y), (u₀, v₀)⟫_ℝ : ℝ) : EReal) +
                (g (xbar, y) : EReal)) +
              (⟪(x', y') - (xbar, y), (v, -v₀)⟫_ℝ : EReal) := by
              rw [show (⟪(x', y') - (xbar, y), (w, (0 : K))⟫_ℝ : EReal) =
                  (⟪x' - xbar, w⟫_ℝ : EReal) by exact_mod_cast hpair_zero]
              rw [show (G (xbar, y) : EReal) = (g (xbar, y) : EReal) by
                  simp [G, pointwiseAdd_apply, hy]]
              rw [hinnerE]
              rw [EReal.coe_add]
              rw [add_assoc]
              rw [add_comm (⟪(x', y') - (xbar, y), (v, -v₀)⟫_ℝ : EReal) (g (xbar, y) : EReal)]
              rw [← add_assoc]
        _ ≤ (g (x', y') : EReal) + 0 := hsum
        _ = (G (x', y') : EReal) := by
          simp [G, pointwiseAdd_apply, hz]
    · have hz_graph : (x', y') ∉ gra F := by
        simpa using hz
      change
        (⟪(x', y') - (xbar, y), (w, (0 : K))⟫_ℝ : EReal) +
            (G (xbar, y) : EReal) ≤
          (G (x', y') : EReal)
      have hxy_indicator : (ι[gra F] (xbar, y) : EReal) = 0 := by
        simp [ERealFunction.indicator, hxy_graph]
      have hz_indicator : (ι[gra F] (x', y') : EReal) = ⊤ := by
        simp [ERealFunction.indicator, hz_graph]
      have htop_le :
          (⟪(x', y') - (xbar, y), (w, (0 : K))⟫_ℝ : EReal) + (g (xbar, y) : EReal) ≤
            (g (x', y') : EReal) + ⊤ := by
        have hg_ne_bot : (g (x', y') : EReal) ≠ ⊥ := ne_of_gt (g (x', y')).property
        calc
          (⟪(x', y') - (xbar, y), (w, (0 : K))⟫_ℝ : EReal) + (g (xbar, y) : EReal) ≤
              (⊤ : EReal) := le_top
          _ = (g (x', y') : EReal) + ⊤ := by
            symm
            exact EReal.add_top_of_ne_bot hg_ne_bot
      rw [show (G (xbar, y) : EReal) = (g (xbar, y) : EReal) + (ι[gra F] (xbar, y) : EReal) by
            simp [G, pointwiseAdd_apply]]
      rw [show (G (x', y') : EReal) = (g (x', y') : EReal) + (ι[gra F] (x', y') : EReal) by
            simp [G, pointwiseAdd_apply]]
      rw [hxy_indicator, hz_indicator]
      simpa [G, pointwiseAdd_apply, hxy_indicator, hz_indicator, add_assoc] using htop_le
  have hw_marginal :
      w ∈ (∂ marginalFunction G) xbar := by
    exact
      (mem_subdifferential_marginalFunction_iff_mem_subdifferential_zeroSecond_of_value_eq
        G xbar y hmarginal_eq w).2 hw_prod
  simpa [G] using hw_marginal

end SubdifferentialOfComposition

end

end ERealFunction
