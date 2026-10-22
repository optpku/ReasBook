/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.RealProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

/- Theorem 5.4.8.4 lies in the Chapter 5 self-concordant-barrier / epigraph domain for
`x ↦ x log x`.

Sampled owner declarations:
* `entropyEpigraphCone`, `entropyEpigraphConeBarrier`, and
  `entropyEpigraphConeBarrier_is_three_self_concordant_barrier` from `Theorem_5_4_7_6`, the
  upstream Chapter 5 owner/view for the entropy-epigraph cone and its canonical `3`-barrier;
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` from `Theorem_5_3_3`, the chapter
  owner theorem for affine pullbacks of self-concordant barriers;
* `Q₃` and `mem_Q₃_iff` from `Definition_5_4_8_9`, the source-facing owner/view for the textbook
  epigraph;
* `separableLogBarrierF3` and `separableLogBarrierF3_apply` from `Definition_5_4_8_10`, the
  source-facing owner/view for `F₃`.

Best owner abstraction:
* source-facing: the textbook epigraph `Q₃` and barrier `F₃`;
* core/canonical: `entropyEpigraphConeBarrier_is_three_self_concordant_barrier` together with
  `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`;
* bridge/view: the affine slice `((x, 1), t)` identifying `Q₃` and `F₃` with the upstream cone
  and barrier owners.

Primitive data:
* the canonical source-facing owners `Q₃` and `F₃`;
* the upstream cone/barrier owners from `Theorem_5_4_7_6`.

Derived API:
* the slice-domain bridge `((x, 1), t) ∈ interior entropyEpigraphCone ↔ (x, t) ∈ interior Q₃`;
* the direct slice identity `F₃ (x, t) = entropyEpigraphConeBarrier ((x, 1), t)`;
* the source-facing `3`-self-concordant-barrier theorem for `F₃`, obtained as an affine pullback.

This file therefore keeps `Q₃` and `F₃` source-facing, but removes the impression of a second
independent owner-level barrier theorem by presenting them through the `x₂ = 1` affine slice of
the upstream entropy-epigraph cone barrier. -/

local notation "F₃" => separableLogBarrierF3

/-- Helper for Theorem 5.4.8.4: strict positivity of both coordinates and strict slack place a
point in the interior of `entropyEpigraphCone`. -/
private theorem strict_mem_interior_entropyEpigraphCone
    {x₁ x₂ z : ℝ}
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hz : z > x₁ * (Real.log x₁ - Real.log x₂)) :
    ((x₁, x₂), z) ∈ interior entropyEpigraphCone := by
  let φ : ((ℝ × ℝ) × ℝ) → ℝ := fun y ↦ y.1.1 * (Real.log y.1.1 - Real.log y.1.2) - y.2
  -- Keep the positive-orthant constraints open in a neighborhood of the point.
  have hx₁mem :
      (fun y : ((ℝ × ℝ) × ℝ) ↦ y.1.1) ⁻¹' Set.Ioi (0 : ℝ) ∈
        nhds ((x₁, x₂), z) :=
    continuousAt_fst.fst.preimage_mem_nhds (isOpen_Ioi.mem_nhds hx₁)
  have hx₂mem :
      (fun y : ((ℝ × ℝ) × ℝ) ↦ y.1.2) ⁻¹' Set.Ioi (0 : ℝ) ∈
        nhds ((x₁, x₂), z) :=
    continuousAt_fst.snd.preimage_mem_nhds (isOpen_Ioi.mem_nhds hx₂)
  -- The strict slack inequality is also open because the logarithmic expression is continuous
  -- on the positive orthant.
  have hφ_cont : ContinuousAt φ ((x₁, x₂), z) := by
    have hlog₁ :
        ContinuousAt
          (fun y : ((ℝ × ℝ) × ℝ) ↦ Real.log y.1.1)
          ((x₁, x₂), z) := by
      have hx₁coord :
          ContinuousAt (fun y : ((ℝ × ℝ) × ℝ) ↦ y.1.1) ((x₁, x₂), z) :=
        continuousAt_fst.fst
      simpa [Function.comp] using (Real.continuousAt_log hx₁.ne').comp hx₁coord
    have hlog₂ :
        ContinuousAt
          (fun y : ((ℝ × ℝ) × ℝ) ↦ Real.log y.1.2)
          ((x₁, x₂), z) := by
      have hx₂coord :
          ContinuousAt (fun y : ((ℝ × ℝ) × ℝ) ↦ y.1.2) ((x₁, x₂), z) :=
        continuousAt_fst.snd
      simpa [Function.comp] using (Real.continuousAt_log hx₂.ne').comp hx₂coord
    have hmul :
        ContinuousAt
          (fun y : ((ℝ × ℝ) × ℝ) ↦
            y.1.1 * (Real.log y.1.1 - Real.log y.1.2))
          ((x₁, x₂), z) :=
      continuousAt_fst.fst.mul (hlog₁.sub hlog₂)
    simpa [φ] using hmul.sub continuousAt_snd
  have hφ_neg : φ ((x₁, x₂), z) < 0 := by
    simpa [φ] using sub_neg.mpr hz
  have hgap :
      φ ⁻¹' Set.Iio (0 : ℝ) ∈ nhds ((x₁, x₂), z) :=
    hφ_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds hφ_neg)
  have hnhds : entropyEpigraphCone ∈ nhds ((x₁, x₂), z) := by
    refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem hx₁mem hx₂mem) hgap) ?_
    rintro y ⟨⟨hy₁, hy₂⟩, hyφ⟩
    rw [mem_entropyEpigraphCone_iff]
    refine ⟨hy₁, hy₂, ?_⟩
    have hylt : y.1.1 * (Real.log y.1.1 - Real.log y.1.2) - y.2 < 0 := by
      simpa [φ] using hyφ
    linarith
  exact mem_interior_iff_mem_nhds.mpr hnhds

/-- Helper for Theorem 5.4.8.4: interior points of `Q₃` are exactly the strictly feasible
points `x > 0` and `t > x log x`. -/
private theorem mem_interior_Q₃_iff {x t : ℝ} :
    (x, t) ∈ interior Q₃ ↔ 0 < x ∧ t > x * Real.log x := by
  constructor
  · intro h
    have hQ : (x, t) ∈ Q₃ := interior_subset h
    rw [mem_Q₃_iff] at hQ
    -- Projecting the interior to the first coordinate strictifies `x ≥ 0` to `x > 0`.
    have hx_strict : 0 < x := by
      have hsubset :
          Q₃ ⊆ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Ici (0 : ℝ) := by
        intro q hq
        rw [mem_Q₃_iff] at hq
        exact hq.1
      have hx_preimage :
          (x, t) ∈ interior ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Ici (0 : ℝ)) :=
        interior_mono hsubset h
      have hx_mem :
          (x, t) ∈ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' interior (Set.Ici (0 : ℝ)) := by
        rw [←
          isOpenMap_fst.preimage_interior_eq_interior_preimage
            continuous_fst
            (Set.Ici (0 : ℝ))] at hx_preimage
        exact hx_preimage
      have hx_int : x ∈ interior (Set.Ici (0 : ℝ)) := by
        simpa using hx_mem
      simpa [interior_Ici] using hx_int
    -- Move only in the vertical direction to rule out boundary slack.
    have ht_strict : t > x * Real.log x := by
      by_contra hnot
      have hle : t ≤ x * Real.log x := le_of_not_gt hnot
      have heq : t = x * Real.log x := le_antisymm hle hQ.2
      let γ : ℝ → ℝ × ℝ := fun s ↦ (x, s)
      have hγ : Continuous γ := by
        fun_prop
      have hpre : γ ⁻¹' interior Q₃ ∈ nhds t := by
        exact hγ.continuousAt.preimage_mem_nhds
          (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using h))
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
      have hdown : t - ε / 2 ∈ Metric.ball t ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hneg : t - ε / 2 - t < 0 := by
          linarith
        rw [abs_of_neg hneg]
        linarith
      have hmem : γ (t - ε / 2) ∈ interior Q₃ := hεsub hdown
      have hQdown : γ (t - ε / 2) ∈ Q₃ := interior_subset hmem
      rw [mem_Q₃_iff] at hQdown
      have hbound : x * Real.log x ≤ t - ε / 2 := by
        simpa [γ] using hQdown.2
      rw [heq] at hbound
      linarith
    exact ⟨hx_strict, ht_strict⟩
  · rintro ⟨hx, ht⟩
    let φ : ℝ × ℝ → ℝ := fun q ↦ q.1 * Real.log q.1 - q.2
    -- Open neighborhoods for `x > 0` and for the strict gap together force membership in `Q₃`.
    have hx_mem :
        Prod.fst ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds (x, t) :=
      continuousAt_fst.preimage_mem_nhds (isOpen_Ioi.mem_nhds hx)
    have hφ_cont : ContinuousAt φ (x, t) := by
      have hmulLog :
          ContinuousAt (fun q : ℝ × ℝ ↦ q.1 * Real.log q.1) (x, t) := by
        simpa using (Real.continuous_mul_log.comp continuous_fst).continuousAt
      simpa [φ] using hmulLog.sub continuousAt_snd
    have hφ_neg : φ (x, t) < 0 := by
      simpa [φ] using sub_neg.mpr ht
    have hgap : φ ⁻¹' Set.Iio (0 : ℝ) ∈ nhds (x, t) :=
      hφ_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds hφ_neg)
    have hnhds : Q₃ ∈ nhds (x, t) := by
      refine Filter.mem_of_superset (Filter.inter_mem hx_mem hgap) ?_
      rintro y ⟨hyx, hyφ⟩
      rw [mem_Q₃_iff]
      refine ⟨le_of_lt hyx, ?_⟩
      have hylt : y.1 * Real.log y.1 - y.2 < 0 := by
        simpa [φ] using hyφ
      linarith
    exact mem_interior_iff_mem_nhds.mpr hnhds

-- Proof sketch: `interior entropyEpigraphCone` is the strict version of the entropy-epigraph
-- cone inequalities. On the slice `x₂ = 1`, this becomes `x > 0` and `t > x log x`, which is
-- exactly `interior Q₃`.
/-- On the affine slice `((x, 1), t)`, membership in `interior entropyEpigraphCone` is exactly
membership in `interior Q₃`. -/
theorem mem_interior_entropyEpigraphCone_secondUnitSlice_iff (x t : ℝ) :
    ((x, 1), t) ∈ interior entropyEpigraphCone ↔ (x, t) ∈ interior Q₃ := by
  constructor
  · intro h
    have hcone : ((x, 1), t) ∈ entropyEpigraphCone := interior_subset h
    rw [mem_entropyEpigraphCone_iff] at hcone
    -- The slice `x₂ = 1` turns the entropy slack into the epigraph slack `t ≥ x log x`.
    have ht_strict : t > x * Real.log x := by
      by_contra hnot
      have hle : t ≤ x * Real.log x := le_of_not_gt hnot
      have hge : t ≥ x * Real.log x := by
        simpa [Real.log_one] using hcone.2.2
      have heq : t = x * Real.log x := le_antisymm hle hge
      let γ : ℝ → ((ℝ × ℝ) × ℝ) := fun s ↦ ((x, 1), s)
      have hγ : Continuous γ := by
        fun_prop
      have hpre : γ ⁻¹' interior entropyEpigraphCone ∈ nhds t := by
        exact hγ.continuousAt.preimage_mem_nhds
          (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using h))
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
      have hdown : t - ε / 2 ∈ Metric.ball t ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hneg : t - ε / 2 - t < 0 := by
          linarith
        rw [abs_of_neg hneg]
        linarith
      have hmem : γ (t - ε / 2) ∈ interior entropyEpigraphCone := hεsub hdown
      have hdownCone : γ (t - ε / 2) ∈ entropyEpigraphCone := interior_subset hmem
      rw [mem_entropyEpigraphCone_iff] at hdownCone
      have hbound : x * Real.log x ≤ t - ε / 2 := by
        simpa [γ, Real.log_one] using hdownCone.2.2
      rw [heq] at hbound
      linarith
    -- Reuse the source-facing interior characterization once the slice inequalities are strict.
    exact mem_interior_Q₃_iff.mpr ⟨hcone.1, ht_strict⟩
  · intro h
    have hQ : 0 < x ∧ t > x * Real.log x := mem_interior_Q₃_iff.mp h
    -- Rebuild the entropy-cone interior from the strict slice inequalities.
    exact strict_mem_interior_entropyEpigraphCone hQ.1 zero_lt_one (by
      simpa [Real.log_one] using hQ.2)

-- Proof sketch: the interior of the canonical closed epigraph from Definition 5.4.8.9 is
-- obtained by replacing the boundary inequalities `x ≥ 0` and `t ≥ x log x` with the strict
-- inequalities `x > 0` and `t > x log x`.
/-- A pair `(x, t)` lies in the interior of the canonical epigraph for Definition 5.4.8.9
exactly when `x > 0` and `t > x log x`. -/
theorem mem_interior_constrainedEpigraph_xlogx_iff {x t : ℝ} :
    (x, t) ∈ interior Q₃ ↔
      0 < x ∧ t > x * Real.log x := by
  -- Reuse the source-facing interior characterization helper.
  simpa using mem_interior_Q₃_iff (x := x) (t := t)

-- Proof sketch: identify the interior of the canonical closed epigraph from
-- Definition 5.4.8.9 with the affine slice `x₂ = 1` of the canonical entropy-epigraph cone
-- from Theorem 5.4.7.6. The upstream barrier theorem pulls back along the affine map
-- `p ↦ ((p.1, 1), p.2)`, and the slice-domain bridge together with the defining slice formula
-- for `F₃` identify the result with the source-facing owners `Q₃` and `F₃`.
/-- Theorem 5.4.8.4: the function `F₃(x, t) = -\log x - \log (t - x \log x)` is a
`3`-self-concordant barrier for the epigraph
`Q₃ = {(x, t) ∈ \mathbb{R}^2 \mid x ≥ 0,\ t ≥ x \log x}` of `x \log x`, with the convention
`0 \log 0 = 0`. -/
theorem separableLogBarrierF3_is_three_selfConcordantBarrier :
    IsSelfConcordantBarrierOnWith (interior Q₃) (3 : NNReal) F₃ := by
  let g : (ℝ × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : (ℝ × ℝ) →L[ℝ] ℝ)).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)).toContinuousAffineMap +ᵥ
      ContinuousAffineMap.const ℝ (ℝ × ℝ) (((0 : ℝ), (1 : ℝ)), (0 : ℝ))
  have hg_apply (p : ℝ × ℝ) : g p = ((p.1, 1), p.2) := by
    simp [g]
  let hslice :
      IsSelfConcordantBarrierOnWith
        (g ⁻¹' interior entropyEpigraphCone)
        (3 : NNReal)
        (entropyEpigraphConeBarrier ∘ g) :=
    entropyEpigraphConeBarrier_is_three_self_concordant_barrier.comp_continuousAffineMap
      g
  have hdom : g ⁻¹' interior entropyEpigraphCone = interior Q₃ := by
    ext p
    change g p ∈ interior entropyEpigraphCone ↔ p ∈ interior Q₃
    rw [hg_apply]
    simpa using mem_interior_entropyEpigraphCone_secondUnitSlice_iff p.1 p.2
  have hfun : entropyEpigraphConeBarrier ∘ g = F₃ := by
    funext p
    change entropyEpigraphConeBarrier (g p) = F₃ p
    rw [hg_apply]
    change separableLogBarrierF3 p = separableLogBarrierF3 p
    rfl
  simpa [hdom, hfun] using hslice
