/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_3_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.RealProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_6.Prereqs
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_6.Specialization

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped EntropyEpigraph Gradient HessianLocalNorm

attribute [local instance 10000] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance 10000] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance 10000] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance 10000] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance 10000] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance 10000] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instCompleteSpaceRealProdProd

/-
Theorem 5.4.7.6 lies in the Chapter 5 entropy-epigraph / cone-composition barrier domain.

The derivative/compatibility layer now lives in theorem-local support files so this target file can
stay source-facing: it defines the textbook barrier owner, rewrites the raw specialization back to
that owner, and proves the two affine-slice descriptions from the book.
-/

/-- The logarithmic barrier `ψ_E` for the entropy-epigraph cone, presented as the source-facing
specialization of the chapter's canonical cone-composition barrier owner. -/
abbrev entropyEpigraphConeBarrier : ((ℝ × ℝ) × ℝ) → ℝ :=
  coneCompositionBarrier
    powerConeBarrier
    (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0)
    ξ
    1

-- Proof sketch: evaluate the source-facing owner through the canonical `coneCompositionBarrier`
-- specialization and the upstream pointwise formulas for its three factors.
/-- Evaluating `entropyEpigraphConeBarrier` at `((x₁, x₂), z)` gives the textbook formula
`-\log (z - x^(1) \log (x^(1) / x^(2))) - \log x^(1) - \log x^(2)`. -/
theorem entropyEpigraphConeBarrier_apply (x₁ x₂ z : ℝ) :
    entropyEpigraphConeBarrier ((x₁, x₂), z) =
      -Real.log (z - x₁ * Real.log (x₁ / x₂)) - Real.log x₁ - Real.log x₂ := by
  rw [entropyEpigraphConeBarrier, coneCompositionBarrier_apply,
    entropyEpigraphQ2_sublevelLogBarrier_apply, powerConeBarrier_apply,
    entropyEpigraphRelativeEntropy_apply]
  norm_num
  have harg : -(x₁ * Real.log (x₁ / x₂)) + z = z - x₁ * Real.log (x₁ / x₂) := by
    ring
  rw [harg]
  ring

/-- Helper for Theorem 5.4.7.6: any point feasible for the closed-orthant cone-composition model
already satisfies the graph-point condition `(ξ x, z) ∈ Q₂`. -/
private theorem entropyEpigraphGraphPointMemOfClosedFeasible
    {p : (ℝ × ℝ) × ℝ}
    (hp :
      p ∈ coneCompositionFeasibleSet powerConeQ1 (ConvexCone.positive ℝ ℝ) ξ Q₂) :
    p.1 ∈ powerConeQ1 ∧ (ξ p.1, p.2) ∈ Q₂ := by
  rcases (mem_coneCompositionFeasibleSet_iff powerConeQ1 (ConvexCone.positive ℝ ℝ) ξ Q₂).1 hp with
    ⟨y, hyQ1, hyK, hyQ2⟩
  refine ⟨hyQ1, ?_⟩
  have hgraph :
      (y, p.2) + (1 : ℝ) • (ξ p.1 - y, (0 : ℝ)) ∈ Q₂ :=
    entropyEpigraphQ2_positive_recession hyK hyQ2 1 (by norm_num)
  simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hgraph

/-- Helper for Theorem 5.4.7.6: the source-facing entropy epigraph sits inside the
closed-orthant cone-composition feasible set. -/
private theorem entropyEpigraphCone_subset_closedFeasible :
    entropyEpigraphCone ⊆
      coneCompositionFeasibleSet powerConeQ1 (ConvexCone.positive ℝ ℝ) ξ Q₂ := by
  intro p hp
  rcases p with ⟨⟨x₁, x₂⟩, z⟩
  rw [entropyEpigraphCone_eq_coneCompositionFeasibleSet] at hp
  rw [mem_coneCompositionFeasibleSet_iff] at hp ⊢
  rcases hp with ⟨y, hyPos, hyK, hyQ2⟩
  have hpos : x₁ > 0 ∧ x₂ > 0 := by
    simpa [Set.mem_prod] using hyPos
  refine ⟨y, ?_, hyK, hyQ2⟩
  simpa using (mem_powerConeQ1_iff x₁ x₂).2 ⟨le_of_lt hpos.1, le_of_lt hpos.2⟩

/-- Helper for Theorem 5.4.7.6: every interior point of the closed-orthant feasible model already
lies in the source-facing entropy epigraph. -/
private theorem mem_entropyEpigraphCone_of_mem_interior_closedFeasible
    {p : (ℝ × ℝ) × ℝ}
    (hp :
      p ∈ interior
        (coneCompositionFeasibleSet powerConeQ1 (ConvexCone.positive ℝ ℝ) ξ Q₂)) :
    p ∈ entropyEpigraphCone := by
  rcases p with ⟨⟨x₁, x₂⟩, z⟩
  have hsubset :
      coneCompositionFeasibleSet powerConeQ1 (ConvexCone.positive ℝ ℝ) ξ Q₂ ⊆
        (Prod.fst : ((ℝ × ℝ) × ℝ) → ℝ × ℝ) ⁻¹' powerConeQ1 := by
    intro q hq
    exact (entropyEpigraphGraphPointMemOfClosedFeasible hq).1
  have hp_preimage :
      ((x₁, x₂), z) ∈ interior ((Prod.fst : ((ℝ × ℝ) × ℝ) → ℝ × ℝ) ⁻¹' powerConeQ1) :=
    interior_mono hsubset hp
  have hp_intQ1 : (x₁, x₂) ∈ interior powerConeQ1 := by
    change
      ((x₁, x₂), z) ∈
        (Prod.fst : ((ℝ × ℝ) × ℝ) → ℝ × ℝ) ⁻¹' interior powerConeQ1
    rw [←
      isOpenMap_fst.preimage_interior_eq_interior_preimage
        continuous_fst
        powerConeQ1] at hp_preimage
    exact hp_preimage
  have hgraph : (ξ (x₁, x₂), z) ∈ Q₂ := by
    exact (entropyEpigraphGraphPointMemOfClosedFeasible (interior_subset hp)).2
  rw [entropyEpigraphCone_eq_coneCompositionFeasibleSet, mem_coneCompositionFeasibleSet_iff]
  refine ⟨ξ (x₁, x₂), ?_, ?_, hgraph⟩
  · simpa [Set.mem_prod] using (mem_interior_powerConeQ1_iff x₁ x₂).1 hp_intQ1
  · simp [ConvexCone.mem_positive]

/-- Helper for Theorem 5.4.7.6: a short owner alias for the closed-orthant cone-composition
feasible set used by the raw specialization theorem. -/
private abbrev entropyEpigraphClosedFeasible : Set ((ℝ × ℝ) × ℝ) :=
  coneCompositionFeasibleSet powerConeQ1 (ConvexCone.positive ℝ ℝ) ξ Q₂

open Nesterov.Chap05.Theorem_5_4_7_6.Specialization

/-- Helper for Theorem 5.4.7.6: the generic cone-composition barrier theorem specialized to the
raw entropy-epigraph data, with the chapter `RealProdL2` geometry fixed locally. -/
private theorem entropyEpigraphConeBarrier_rawSelfConcordance :
    @IsSelfConcordantBarrierOnWith
      ((ℝ × ℝ) × ℝ)
      Chap05RealProdL2.instNormedAddCommGroupRealProdProd
      Chap05RealProdL2.instInnerProductSpaceRealProdProd
      Chap05RealProdL2.instCompleteSpaceRealProdProd
      (interior entropyEpigraphClosedFeasible)
      ((1 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal))
      entropyEpigraphConeBarrier := by
  -- Route correction: reuse the ambient-pinned raw specialization from the support file instead
  -- of re-specializing the generic cone-composition theorem in this source-facing file.
  simpa [entropyEpigraphClosedFeasible, entropyEpigraphConeBarrier] using
    coneCompositionBarrier_entropyEpigraphQ2Raw_isSelfConcordantBarrierOnWith

/-- Helper for Theorem 5.4.7.6: the raw closed-feasible owner has the same interior as the
source-facing entropy-epigraph cone. -/
private theorem entropyEpigraphConeInterior_eq_interiorClosedFeasible :
    interior entropyEpigraphClosedFeasible = interior entropyEpigraphCone := by
  apply Set.Subset.antisymm
  · intro p hp
    -- Any point of the raw interior already lies in the source-facing cone, and openness upgrades
    -- this membership to the source-facing interior.
    exact mem_interior_iff_mem_nhds.mpr <|
      Filter.mem_of_superset
        (isOpen_interior.mem_nhds hp)
        (fun q hq ↦ mem_entropyEpigraphCone_of_mem_interior_closedFeasible hq)
  · -- The source-facing cone sits in the closed-feasible owner, so its interior does too.
    exact interior_mono entropyEpigraphCone_subset_closedFeasible

-- Proof sketch: rewrite the raw specialization's owner back to `entropyEpigraphCone`, then
-- collapse the parameter arithmetic from `1 + 1^3 * 2` to `3`.
/-- Helper for Theorem 5.4.7.6: the raw support-file specialization rewrites to the source-facing
entropy-epigraph barrier theorem with parameter `3`. -/
private theorem entropyEpigraphConeBarrier_specializedSelfConcordance :
    IsSelfConcordantBarrierOnWith (interior entropyEpigraphCone) (3 : NNReal)
      entropyEpigraphConeBarrier := by
  have hparam : ((1 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal)) = 3 := by
    norm_num
  have hraw :
      IsSelfConcordantBarrierOnWith
        (interior entropyEpigraphCone)
        ((1 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal))
        entropyEpigraphConeBarrier := by
    -- Rewrite the raw specialization back to the textbook owner before collapsing the parameter.
    simpa [entropyEpigraphConeInterior_eq_interiorClosedFeasible] using
      entropyEpigraphConeBarrier_rawSelfConcordance
  -- Collapse the raw parameter arithmetic after the owner rewrite is in place.
  exact hparam ▸ hraw

/-- Clause (2) of Theorem 5.4.7.6: the function
`ψ_E((x^(1), x^(2)), z) = -\log (z - x^(1) \log (x^(1) / x^(2))) - \log x^(1) - \log x^(2)` is
a `3`-self-concordant barrier for the entropy-epigraph cone `\mathcal Q`. -/
theorem entropyEpigraphConeBarrier_is_three_self_concordant_barrier :
    IsSelfConcordantBarrierOnWith (interior entropyEpigraphCone) (3 : NNReal)
      entropyEpigraphConeBarrier := by
  -- Reuse the owner-stable specialization helper so the public theorem only performs the
  -- final rewrite.
  simpa using entropyEpigraphConeBarrier_specializedSelfConcordance

-- Proof sketch: unfold `entropyEpigraphCone` at the point `((1, x₂), z)`, rewrite the defining
-- inequality using `1 * (Real.log 1 - Real.log x₂) = -Real.log x₂`, and compare with the
-- canonical epigraph owner for `x ↦ -Real.log x`.
/-- Clause (3) of Theorem 5.4.7.6: on the affine slice `x^(1) = 1`, the entropy-epigraph cone is
exactly
the chapter constrained epigraph of `x^(2) ↦ -\log x^(2)` on `(0, ∞)`. -/
theorem entropyEpigraphCone_unitSlice_eq_logEpigraph :
    {yz : ℝ × ℝ | ((1, yz.1), yz.2) ∈ entropyEpigraphCone} =
      constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ)) := by
  ext yz
  rcases yz with ⟨x₂, z⟩
  -- Change the set-equality goal to pointwise membership and then compare the two explicit
  -- logarithmic inequalities.
  change ((1, x₂), z) ∈ entropyEpigraphCone ↔
    (x₂, z) ∈ constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ))
  rw [mem_entropyEpigraphCone_iff, mem_constrainedEpigraph_negLog_iff]
  constructor
  · rintro ⟨_, hx₂, hz⟩
    have hz' : -Real.log x₂ ≤ z := by
      simpa [Real.log_one] using hz
    exact ⟨hx₂, hz'⟩
  · rintro ⟨hx₂, hz⟩
    refine ⟨zero_lt_one, hx₂, ?_⟩
    simpa [Real.log_one] using hz

-- Proof sketch: rewrite clause `(3)` through the scalar equivalence
-- `z ≥ -log x₂ ↔ exp (-z) ≤ x₂` valid for `x₂ > 0`.
/-- Clause (4) of Theorem 5.4.7.6: on the affine slice `x^(1) = 1`, the entropy-epigraph cone is
equivalently described by the inequality `x^(2) ≥ e^{-z}`. -/
theorem entropyEpigraphCone_unitSlice_eq_expEpigraph :
    {yz : ℝ × ℝ | ((1, yz.1), yz.2) ∈ entropyEpigraphCone} =
      {yz : ℝ × ℝ | yz.1 ≥ Real.exp (-yz.2)} := by
  ext yz
  rcases yz with ⟨x₂, z⟩
  -- Start from clause `(3)` and convert the logarithmic inequality to the exponential form.
  change ((1, x₂), z) ∈ entropyEpigraphCone ↔ x₂ ≥ Real.exp (-z)
  have hlogSlice :
      ((1, x₂), z) ∈ entropyEpigraphCone ↔
        (x₂, z) ∈
          constrainedEpigraph
            (Set.Ioi (0 : ℝ))
            (fun x : ℝ ↦ (-Real.log x : WithTop ℝ)) := by
    simpa [Set.mem_setOf_eq] using
      congrArg (fun S : Set (ℝ × ℝ) ↦ (x₂, z) ∈ S) entropyEpigraphCone_unitSlice_eq_logEpigraph
  rw [mem_constrainedEpigraph_negLog_iff] at hlogSlice
  rw [hlogSlice]
  constructor
  · rintro ⟨hx₂, hz⟩
    have hlog : -z ≤ Real.log x₂ := by
      linarith
    exact (Real.le_log_iff_exp_le hx₂).1 hlog
  · intro hx₂
    have hx₂_pos : 0 < x₂ := lt_of_lt_of_le (Real.exp_pos (-z)) hx₂
    have hlog : -z ≤ Real.log x₂ := (Real.le_log_iff_exp_le hx₂_pos).2 hx₂
    have hz : -Real.log x₂ ≤ z := by
      linarith
    exact ⟨hx₂_pos, hz⟩

/-- Theorem 5.4.7.6: `ξ` is `1`-compatible with the orthant barrier `F`, the corresponding
specialized cone-composition barrier is `3`-self-concordant on `entropyEpigraphCone`, and the
unit slice `x^(1) = 1` is described equivalently by the logarithmic and exponential epigraph
inequalities from the source text. -/
theorem entropyEpigraphConeBarrier_and_unitSlice_descriptions :
    IsBetaCompatibleWith powerConeQ1 (ConvexCone.positive ℝ ℝ) powerConeBarrier (1 : NNReal) ξ ∧
    IsSelfConcordantBarrierOnWith (interior entropyEpigraphCone) (3 : NNReal)
      entropyEpigraphConeBarrier ∧
    {yz : ℝ × ℝ | ((1, yz.1), yz.2) ∈ entropyEpigraphCone} =
        constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ)) ∧
    {yz : ℝ × ℝ | ((1, yz.1), yz.2) ∈ entropyEpigraphCone} =
        {yz : ℝ × ℝ | yz.1 ≥ Real.exp (-yz.2)} := by
  -- Package the already-proved source clauses into the item's public textbook entry.
  refine ⟨?_, ?_⟩
  · simpa using entropyEpigraphRelativeEntropy_isOneCompatibleWith_powerConeBarrier
  · refine ⟨entropyEpigraphConeBarrier_is_three_self_concordant_barrier, ?_⟩
    exact
      ⟨entropyEpigraphCone_unitSlice_eq_logEpigraph,
        entropyEpigraphCone_unitSlice_eq_expEpigraph⟩
