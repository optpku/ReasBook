/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_29

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
private theorem exists_strict_upperLevel_of_isMinimizingSequence
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ) :
    ∃ ξ : ℝ, sInf (Set.range f) < (ξ : EReal) := by
  let ξ : ℝ := (f (xₙ 0)).toReal + 1
  refine ⟨ξ, ?_⟩
  have hx0_lt_ξ : f (xₙ 0) < (ξ : EReal) := by
    by_cases hx0_bot : f (xₙ 0) = ⊥
    · simpa [ξ, hx0_bot] using EReal.bot_lt_coe ((f (xₙ 0)).toReal + 1)
    · rw [← EReal.coe_toReal (ne_of_lt (hxₙ.lt_top 0)) hx0_bot]
      exact_mod_cast show (f (xₙ 0)).toReal < (f (xₙ 0)).toReal + 1 by linarith
  exact lt_of_le_of_lt (sInf_le (Set.mem_range_self (xₙ 0))) hx0_lt_ξ

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
private theorem lowerLevelSet_subset_effectiveDomain_asEReal
    {f : H → Set.Ioi (⊥ : EReal)} {ξ : ℝ} :
    lowerLevelSet f.asEReal ξ ⊆ effectiveDomain f := by
  intro x hx
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt ((mem_lowerLevelSet_iff f.asEReal ξ x).1 hx) (EReal.coe_lt_top ξ)

private theorem exists_nonempty_lowerLevelSet_above_sInf_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    ∃ ξ : ℝ, sInf (Set.range f.asEReal) < (ξ : EReal) ∧
      (lowerLevelSet f.asEReal ξ).Nonempty := by
  obtain ⟨x, hxdom⟩ := (isProper_of_mem_gammaZero hf).2
  let ξ : ℝ := (f x : EReal).toReal + 1
  have hx_lt_ξ : (f x : EReal) < (ξ : EReal) := by
    rw [← EReal.coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hxdom)) (ne_of_gt (f x).2)]
    exact_mod_cast show (f x : EReal).toReal < (f x : EReal).toReal + 1 by linarith
  refine ⟨ξ, lt_of_le_of_lt (sInf_le (Set.mem_range_self x)) hx_lt_ξ, x, ?_⟩
  exact (mem_lowerLevelSet_iff f.asEReal ξ x).2 hx_lt_ξ.le

private theorem exists_nonempty_bounded_convex_lowerLevelSet_above_sInf_of_mem_gammaZero_of_coercive
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hf_coe : Coercive f.asEReal) :
    ∃ ξ : ℝ, sInf (Set.range f.asEReal) < (ξ : EReal) ∧
      (lowerLevelSet f.asEReal ξ).Nonempty ∧
      Bornology.IsBounded (lowerLevelSet f.asEReal ξ) ∧
      Convex ℝ (lowerLevelSet f.asEReal ξ) := by
  obtain ⟨ξ, hξ, hlevel_nonempty⟩ := exists_nonempty_lowerLevelSet_above_sInf_of_mem_gammaZero hf
  refine ⟨ξ, hξ, hlevel_nonempty, ?_, convex_lowerLevelSet_asEReal_of_mem_gammaZero hf ξ⟩
  exact (coercive_iff_bounded_lowerLevelSet f.asEReal).1 hf_coe ξ

private theorem convexCombination_le_max {a b : EReal} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    (α : EReal) * a + ((1 - α : ℝ) : EReal) * b ≤ max a b := by
  have hα_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα0.le
  have hβ_nonneg : 0 ≤ (((1 - α : ℝ) : EReal)) := by
    exact_mod_cast (sub_pos.2 hα1).le
  have hsum : (α : EReal) + ((1 - α : ℝ) : EReal) = 1 := by
    rw [← EReal.coe_add]
    norm_num
  calc
    (α : EReal) * a + ((1 - α : ℝ) : EReal) * b
        ≤ (α : EReal) * max a b + ((1 - α : ℝ) : EReal) * max a b := by
          gcongr
          · exact le_max_left a b
          · exact le_max_right a b
    _ = max a b := by
          rw [← EReal.right_distrib_of_nonneg hα_nonneg hβ_nonneg, hsum, one_mul]

private theorem strictlyQuasiconvex_add_indicator_of_strictlyConvexOn
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hC_convex : Convex ℝ C) (hstrict : StrictlyConvexOn f C) :
    StrictlyQuasiconvex (f.asEReal + (ι[C]).asEReal) := by
  let g : H → EReal := f.asEReal + (ι[C]).asEReal
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x
      by_cases hx : x ∈ C
      · simpa [g, hx] using (ne_of_gt (f x).2)
      · have hbot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
        simp [hx, hbot]
    · rcases hstrict.nonempty with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [mem_dom_iff]
      simpa [g, hx] using mem_effectiveDomain_iff.mp (hstrict.subset_effectiveDomain hx)
  · intro x y hx hy hxy α hα0 hα1
    rw [mem_dom_iff_ne_top] at hx hy
    have hxC : x ∈ C := by
      by_contra hxC
      have hbot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
      exact hx (by simp [hxC, hbot])
    have hyC : y ∈ C := by
      by_contra hyC
      have hbot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
      exact hy (by simp [hyC, hbot])
    have hcomboC :
        α • x + (1 - α) • y ∈ C := by
      exact hC_convex hxC hyC hα0.le (by linarith) (by ring)
    have hstrict_lt :
        (f (α • x + (1 - α) • y) : EReal) < max (f x : EReal) (f y : EReal) := by
      calc
        (f (α • x + (1 - α) • y) : EReal)
            < (α : EReal) * (f x : EReal) + ((1 - α : ℝ) : EReal) * (f y : EReal) :=
              hstrict.ineq hxC hyC hxy hα0 hα1
        _ ≤ max (f x : EReal) (f y : EReal) :=
              convexCombination_le_max hα0 hα1
    simpa [g, hxC, hyC, hcomboC] using hstrict_lt

private theorem uniformlyQuasiconvex_add_indicator_of_uniformlyConvexOn
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hC_convex : Convex ℝ C) (huniform : UniformlyConvexOn f C φ) :
    UniformlyQuasiconvex (f.asEReal + (ι[C]).asEReal) φ := by
  let g : H → EReal := f.asEReal + (ι[C]).asEReal
  refine ⟨?_, huniform.monotone, huniform.modulus_eq_zero_iff, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x
      by_cases hx : x ∈ C
      · simpa [g, hx] using (ne_of_gt (f x).2)
      · have hbot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
        simp [hx, hbot]
    · rcases huniform.nonempty with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [mem_dom_iff]
      simpa [g, hx] using mem_effectiveDomain_iff.mp (huniform.subset_effectiveDomain hx)
  · intro x y hx hy α hα0 hα1
    rw [mem_dom_iff_ne_top] at hx hy
    have hxC : x ∈ C := by
      by_contra hxC
      have hbot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
      exact hx (by simp [hxC, hbot])
    have hyC : y ∈ C := by
      by_contra hyC
      have hbot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
      exact hy (by simp [hyC, hbot])
    have hcomboC :
        α • x + (1 - α) • y ∈ C := by
      exact hC_convex hxC hyC hα0.le (by linarith) (by ring)
    have huniform_le :
        (f (α • x + (1 - α) • y) : EReal) +
            ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤
          max (f x : EReal) (f y : EReal) := by
      calc
        (f (α • x + (1 - α) • y) : EReal) +
            ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊
            ≤ (α : EReal) * (f x : EReal) + ((1 - α : ℝ) : EReal) * (f y : EReal) :=
              huniform.ineq hxC hyC hα0 hα1
        _ ≤ max (f x : EReal) (f y : EReal) :=
              convexCombination_le_max hα0 hα1
    simpa [g, hxC, hyC, hcomboC] using huniform_le

section CompleteSpace

variable [CompleteSpace H]

-- Proof sketch: Proposition 11.20 makes every minimizing sequence of a coercive function
-- bounded. Equivalently, Proposition 11.12 makes every real lower level set bounded, so
-- Proposition 11.29 (1) yields a weak sequential cluster point. No `Γ₀(H)` structure is used.
/-- Corollary 11.30 (1): clause (i). Every minimizing sequence of a coercive `]-∞,+∞]`-valued
function has a weak sequential cluster point. -/
theorem exists_weakSequentialClusterPoint_of_coercive
    {f : H → Set.Ioi (⊥ : EReal)} (hf_coe : Coercive f.asEReal) {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence f.asEReal xₙ) :
    ∃ x : H,
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x) := by
  obtain ⟨ξ, hξ⟩ := exists_strict_upperLevel_of_isMinimizingSequence hxₙ
  have hlevel_bounded : Bornology.IsBounded (lowerLevelSet f.asEReal ξ) :=
    (coercive_iff_bounded_lowerLevelSet f.asEReal).1 hf_coe ξ
  exact
    IsMinimizingSequence.exists_weakSequentialClusterPoint_of_bounded_lowerLevelSet
      hxₙ hξ hlevel_bounded

end CompleteSpace

-- Proof sketch: unpack `hf : f ∈ Γ₀(H)` into lower semicontinuity and convexity on
-- `effectiveDomain f`; the latter yields quasiconvexity on `Set.univ`, so Proposition 11.29 (2)
-- identifies every weak sequential cluster point of the minimizing sequence with a global
-- minimizer. Unlike part (1), this is the non-complete clause of Proposition 11.29.
/-- Corollary 11.30 (2): clause (i). Every weak sequential cluster point of a minimizing sequence
of a member of `Γ₀(H)` is a global minimizer. -/
theorem mem_argmin_of_weakSequentialClusterPoint_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence f.asEReal xₙ) {x : H}
    (hx : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x)) :
    x ∈ Argmin f.asEReal := by
  have hf_quasi : QuasiconvexOn ℝ Set.univ f.asEReal := by
    rw [quasiconvexOn_univ_iff_convex_lowerLevelSet ℝ]
    intro ξ
    exact convex_lowerLevelSet_asEReal_of_mem_gammaZero hf ξ
  exact
    IsSequentialClusterPt.mem_argmin_of_isMinimizingSequence_of_quasiconvexOn_univ hx
      hf_quasi hf.1 hxₙ

section CompleteSpace

variable [CompleteSpace H]

-- Proof sketch: coercivity and `hf : f ∈ Γ₀(H)` give existence of a minimizer, while strict
-- convexity implies uniqueness by Corollary 11.9.
/-- Corollary 11.30 (3): clause (ii). If `f` is strictly convex, then `f` has a unique global
minimizer. -/
theorem existsUnique_mem_argmin_of_mem_gammaZero_of_coercive_of_strictlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hf_coe : Coercive f.asEReal) (hstrict : StrictlyConvex f) :
    ∃! x : H, x ∈ Argmin f.asEReal := by
  obtain ⟨ξ, hξ, hlevel_nonempty, hlevel_bounded, hlevel_convex⟩ :=
    exists_nonempty_bounded_convex_lowerLevelSet_above_sInf_of_mem_gammaZero_of_coercive
      hf hf_coe
  have hstrict_level :
      StrictlyConvexOn f (lowerLevelSet f.asEReal ξ) :=
    hstrict.strictlyConvexOn hlevel_nonempty lowerLevelSet_subset_effectiveDomain_asEReal
  exact
    existsUnique_mem_argmin_of_strictlyQuasiconvex_indicator_lowerLevelSet
      hf.1 hξ hlevel_bounded
      (strictlyQuasiconvex_add_indicator_of_strictlyConvexOn hlevel_convex hstrict_level)

-- Proof sketch: by Corollary 11.30 (1), the minimizing sequence has a weak sequential cluster
-- point; Corollary 11.30 (2) makes every such point a minimizer. Strict convexity makes the
-- minimizer unique, so Proposition 11.29 (4) yields weak convergence of the whole minimizing
-- sequence to that minimizer.
/-- Corollary 11.30 (4): clause (ii). If `f` is strictly convex, then every minimizing sequence
converges weakly to a global minimizer of `f`. -/
theorem exists_mem_argmin_and_tendsto_toWeakSpace_of_mem_gammaZero_of_coercive_of_strictlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hf_coe : Coercive f.asEReal) (hstrict : StrictlyConvex f) {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence f.asEReal xₙ) :
    ∃ x ∈ Argmin f.asEReal,
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)) := by
  obtain ⟨ξ, hξ, hlevel_nonempty, hlevel_bounded, hlevel_convex⟩ :=
    exists_nonempty_bounded_convex_lowerLevelSet_above_sInf_of_mem_gammaZero_of_coercive
      hf hf_coe
  have hstrict_level :
      StrictlyConvexOn f (lowerLevelSet f.asEReal ξ) :=
    hstrict.strictlyConvexOn hlevel_nonempty lowerLevelSet_subset_effectiveDomain_asEReal
  exact
    hxₙ.exists_mem_argmin_and_tendsto_toWeakSpace_of_strictlyQuasiconvex_indicator_lowerLevelSet
      hf.1 hξ hlevel_bounded
      (strictlyQuasiconvex_add_indicator_of_strictlyConvexOn hlevel_convex hstrict_level)

-- Proof sketch: coercivity again yields existence of a minimizer. Apply the hypothesis on
-- nonempty bounded subsets to a bounded lower level set containing the minimizing set; the
-- resulting local uniform convexity gives uniqueness through Proposition 11.29 (5).
/-- Corollary 11.30 (5): clause (iii). If `f` is uniformly convex on every nonempty bounded subset
of `effectiveDomain f`, then `f` has a unique global minimizer. -/
theorem existsUnique_mem_argmin_of_gammaZero_coercive_uniformlyConvexOnBoundedSubsets
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hf_coe : Coercive f.asEReal)
    (hbounded_uniform :
      ∀ ⦃C : Set H⦄, C.Nonempty → Bornology.IsBounded C → C ⊆ effectiveDomain f →
        ∃ φ : NNReal → EReal, UniformlyConvexOn f C φ) :
    ∃! x : H, x ∈ Argmin f.asEReal := by
  obtain ⟨ξ, hξ, hlevel_nonempty, hlevel_bounded, hlevel_convex⟩ :=
    exists_nonempty_bounded_convex_lowerLevelSet_above_sInf_of_mem_gammaZero_of_coercive
      hf hf_coe
  obtain ⟨φ, huniform_level⟩ :=
    hbounded_uniform hlevel_nonempty hlevel_bounded lowerLevelSet_subset_effectiveDomain_asEReal
  exact
    existsUnique_mem_argmin_of_uniformlyQuasiconvex_indicator_lowerLevelSet
      hf.1 hξ hlevel_bounded
      (uniformlyQuasiconvex_add_indicator_of_uniformlyConvexOn hlevel_convex huniform_level)

-- Proof sketch: coercivity bounds the minimizing sequence, so its range is contained in a
-- nonempty bounded subset of `effectiveDomain f` on which `f` is uniformly convex by hypothesis.
-- Proposition 11.29 (6) then gives strong convergence to a minimizer, and Corollary 11.30 (5)
-- supplies uniqueness.
/-- Corollary 11.30 (6): clause (iii). If `f` is uniformly convex on every nonempty bounded subset
of `effectiveDomain f`, then every minimizing sequence converges strongly to a global minimizer
of `f`. -/
theorem exists_mem_argmin_and_tendsto_of_gammaZero_coercive_uniformlyConvexOnBoundedSubsets
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hf_coe : Coercive f.asEReal)
    (hbounded_uniform :
      ∀ ⦃C : Set H⦄, C.Nonempty → Bornology.IsBounded C → C ⊆ effectiveDomain f →
        ∃ φ : NNReal → EReal, UniformlyConvexOn f C φ)
    {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f.asEReal xₙ) :
    ∃ x ∈ Argmin f.asEReal, Tendsto xₙ atTop (𝓝 x) := by
  obtain ⟨ξ, hξ, hlevel_nonempty, hlevel_bounded, hlevel_convex⟩ :=
    exists_nonempty_bounded_convex_lowerLevelSet_above_sInf_of_mem_gammaZero_of_coercive
      hf hf_coe
  obtain ⟨φ, huniform_level⟩ :=
    hbounded_uniform hlevel_nonempty hlevel_bounded lowerLevelSet_subset_effectiveDomain_asEReal
  exact
    hxₙ.exists_mem_argmin_and_tendsto_of_uniformlyQuasiconvex_indicator_lowerLevelSet
      hf.1 hξ hlevel_bounded
      (uniformlyQuasiconvex_add_indicator_of_uniformlyConvexOn hlevel_convex huniform_level)

end CompleteSpace

end ERealFunction
