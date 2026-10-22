/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_44
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_67

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u v

namespace SetValuedOperator

noncomputable section

section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

omit [InnerProductSpace ℝ H] [InnerProductSpace ℝ K] in
private lemma mem_univ_prod_sub_singleton_iff {C : Set K} {x : H} {y : K} {p : H × K} :
    p ∈ (univ ×ˢ C) - ({(x, y)} : Set (H × K)) ↔ p.2 + y ∈ C := by
  constructor
  · rintro ⟨q, hq, r, hr, hpr⟩
    have hrxy : r = (x, y) := by
      simpa using hr
    rcases hq with ⟨-, hq₂⟩
    subst hrxy
    rcases q with ⟨q₁, q₂⟩
    rcases p with ⟨p₁, p₂⟩
    cases hpr
    simpa using hq₂
  · intro hp
    refine ⟨(p.1 + x, p.2 + y), ?_, (x, y), by simp, ?_⟩
    · exact ⟨by simp, hp⟩
    · ext <;> simp

-- Proof sketch: for the constant operator `F z = C`, the graph is `Set.univ ×ˢ C`. If `y ∈ C`,
-- its normal cone at `(x, y)` is detected by the translated cylinder `(Set.univ ×ˢ C) - {(x, y)}`;
-- testing that polar-cone condition on the horizontal vectors `(±u, 0)` forces the coderivative
-- output coordinate to vanish, and the remaining vertical condition is exactly `-v ∈ N[C] y`. If
-- `y ∉ C`, both the coderivative graph and `-N[C] y × {0}` are empty.
/-- Example 16.68: for the constant set-valued operator `F z = C`, the graph of `D*F(x, y)` is
`-N[C] y × {0}`. -/
theorem graph_coderivative_constant_eq_neg_normalCone_prod_singleton_zero
    {C : Set K} {x : H} {y : K} :
    ((D* (fun _ : H ↦ C)) x y).graph = (-N[C] y) ×ˢ ({0} : Set H) := by
  have hgraph : graph (fun _ : H ↦ C) = univ ×ˢ C := by
    ext p
    simp [graph]
  by_cases hy : y ∈ C
  · ext vu
    have hnormal_eq :
        N[univ ×ˢ C] (x, y) =
          ((univ ×ˢ C) - ({(x, y)} : Set (H × K)))ᵒ⊖ :=
      Set.normalCone_eq_polarCone_translate_of_mem (by simpa using hy)
    constructor
    · intro hvu
      rw [mem_graph, mem_coderivative_iff] at hvu
      rw [hgraph] at hvu
      have hnormal : (vu.2, -vu.1) ∈ N[univ ×ˢ C] (x, y) := hvu
      rw [hnormal_eq, Set.mem_polarCone_iff_forall_inner_nonpos] at hnormal
      have hu_mem : (vu.2, (0 : K)) ∈ (univ ×ˢ C) - ({(x, y)} : Set (H × K)) := by
        refine ⟨(x + vu.2, y), ?_, (x, y), by simp, ?_⟩
        · exact ⟨by simp, hy⟩
        · ext <;> simp
      have hu_nonpos : ⟪(vu.2, (0 : K)), (vu.2, -vu.1)⟫_ℝ ≤ 0 := hnormal _ hu_mem
      have hu_sq_nonpos : ‖vu.2‖ ^ 2 ≤ 0 := by
        change ⟪vu.2, vu.2⟫_ℝ + ⟪(0 : K), -vu.1⟫_ℝ ≤ 0 at hu_nonpos
        simpa [real_inner_self_eq_norm_sq] using hu_nonpos
      have hu_sq_nonneg : 0 ≤ ‖vu.2‖ ^ 2 := sq_nonneg ‖vu.2‖
      have hu_zero : vu.2 = 0 := by
        exact norm_eq_zero.mp <| sq_eq_zero_iff.mp <| le_antisymm hu_sq_nonpos hu_sq_nonneg
      have hv_mem : -vu.1 ∈ N[C] y := by
        rw [Set.normalCone_eq_polarCone_translate_of_mem hy]
        rw [Set.mem_polarCone_iff_forall_inner_nonpos]
        intro w hw
        rcases Set.mem_sub.mp hw with ⟨a, ha, b, hb, hab⟩
        have hby : b = y := by
          simpa using hb
        subst b
        have hw_mem : ((0 : H), w) ∈ (univ ×ˢ C) - ({(x, y)} : Set (H × K)) := by
          refine ⟨(x, a), ⟨by simp, ha⟩, (x, y), by simp, ?_⟩
          ext <;> simp [hab]
        have hnormal_w : ⟪w, -vu.1⟫_ℝ ≤ 0 := by
          have hnormal_pair : ⟪((0 : H), w), (vu.2, -vu.1)⟫_ℝ ≤ 0 := hnormal ((0 : H), w) hw_mem
          change ⟪(0 : H), vu.2⟫_ℝ + ⟪w, -vu.1⟫_ℝ ≤ 0 at hnormal_pair
          simpa [hu_zero] using hnormal_pair
        exact hnormal_w
      exact ⟨by simpa [Set.mem_neg] using hv_mem, hu_zero⟩
    · rintro ⟨hv, hzero⟩
      rw [mem_graph, mem_coderivative_iff]
      have hu_zero : vu.2 = 0 := by
        simpa using hzero
      have hv' : -vu.1 ∈ N[C] y := by
        simpa [Set.mem_neg] using hv
      rw [hgraph]
      rw [hnormal_eq, Set.mem_polarCone_iff_forall_inner_nonpos]
      rw [Set.normalCone_eq_polarCone_translate_of_mem hy] at hv'
      rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hv'
      intro p hp
      have hp₂ : p.2 + y ∈ C :=
        mem_univ_prod_sub_singleton_iff.1 hp
      have hpv : ⟪p.2, -vu.1⟫_ℝ ≤ 0 := by
        apply hv'
        exact ⟨p.2 + y, hp₂, y, by simp, by simp⟩
      rcases p with ⟨p₁, p₂⟩
      change ⟪p₁, vu.2⟫_ℝ + ⟪p₂, -vu.1⟫_ℝ ≤ 0
      simpa [hu_zero] using hpv
  · have hgraph_not_mem : (x, y) ∉ graph (fun _ : H ↦ C) := by
      rw [hgraph, Set.mem_prod]
      simp [hy]
    have hnormal_empty : N[graph (fun _ : H ↦ C)] (x, y) = ∅ :=
      Set.normalCone_of_not_mem hgraph_not_mem
    ext vu
    rw [mem_graph, mem_coderivative_iff, hnormal_empty]
    simp [Set.normalCone_of_not_mem hy]

end

end

end SetValuedOperator
