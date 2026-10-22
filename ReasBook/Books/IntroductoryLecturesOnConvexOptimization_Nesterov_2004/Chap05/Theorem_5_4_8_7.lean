/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.RealProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_3_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_16

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

open scoped PowerConePlus

variable (p : ℝ)

local notation "Q₆" => Q₆ p
local notation "F₆" => separableLogBarrierF6 p

/-- Helper for Theorem 5.4.8.7: the affine unit-slice map `q ↦ (q, 1)` identifying `Q₆ p`
with the one-sided power cone slice `z = 1`. -/
private def powerConePlusUnitSliceAffine : (ℝ × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
  ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod
      (0 : (ℝ × ℝ) →L[ℝ] ℝ)).toContinuousAffineMap +ᵥ
    ContinuousAffineMap.const ℝ (ℝ × ℝ) (((0 : ℝ), (0 : ℝ)), (1 : ℝ))

/-- Helper for Theorem 5.4.8.7: evaluating the affine slice map recovers the unit slice
`((x, t), 1)`. -/
@[simp] private theorem powerConePlusUnitSliceAffine_apply (q : ℝ × ℝ) :
    powerConePlusUnitSliceAffine q = (q, 1) := by
  simp [powerConePlusUnitSliceAffine]

/-- Helper for Theorem 5.4.8.7: a pair `(x, t)` lies in `interior (Q₆ p)` exactly when
`x > 0` and `t > x^{-p}`. -/
theorem mem_interior_qSix_iff {x t : ℝ} :
    (x, t) ∈ interior Q₆ ↔
      0 < x ∧ t > 1 / Real.rpow x p := by
  constructor
  · intro h
    have hQ : (x, t) ∈ Q₆ := interior_subset h
    rw [mem_Q₆_iff] at hQ
    rcases hQ with ⟨hx, ht_le⟩
    have ht_strict : 1 / Real.rpow x p < t := by
      by_contra hnot
      have hle : t ≤ 1 / Real.rpow x p := le_of_not_gt hnot
      have heq : t = 1 / Real.rpow x p := le_antisymm hle ht_le
      let γ : ℝ → ℝ × ℝ := fun s ↦ (x, s)
      have hγ : Continuous γ := by
        fun_prop
      have hpre : γ ⁻¹' interior Q₆ ∈ nhds t := by
        exact hγ.continuousAt.preimage_mem_nhds
          (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using h))
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
      have hdown : t - ε / 2 ∈ Metric.ball t ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hneg : t - ε / 2 - t < 0 := by
          linarith
        rw [abs_of_neg hneg]
        linarith
      have hmem : γ (t - ε / 2) ∈ interior Q₆ := hεsub hdown
      have hQdown : γ (t - ε / 2) ∈ Q₆ := interior_subset hmem
      rw [mem_Q₆_iff] at hQdown
      have hbound : 1 / Real.rpow x p ≤ t - ε / 2 := by
        simpa [γ] using hQdown.2
      rw [heq] at hbound
      linarith
    exact ⟨hx, ht_strict⟩
  · rintro ⟨hx, ht⟩
    let φ : ℝ × ℝ → ℝ := fun q ↦ 1 / Real.rpow q.1 p - q.2
    have hx_mem :
        Prod.fst ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds (x, t) :=
      continuousAt_fst.preimage_mem_nhds (isOpen_Ioi.mem_nhds hx)
    have hφ_cont : ContinuousAt φ (x, t) := by
      have hrpow : ContinuousAt (fun q : ℝ × ℝ ↦ Real.rpow q.1 p) (x, t) := by
        simpa using continuousAt_fst.rpow_const (Or.inl hx.ne')
      have hinv :
          ContinuousAt (fun q : ℝ × ℝ ↦ 1 / Real.rpow q.1 p) (x, t) := by
        exact ContinuousAt.div continuousAt_const hrpow (Real.rpow_pos_of_pos hx p).ne'
      simpa [φ] using hinv.sub continuousAt_snd
    have hφ_neg : φ (x, t) < 0 := by
      simpa [φ] using sub_neg.mpr ht
    have hgap :
        φ ⁻¹' Set.Iio (0 : ℝ) ∈ nhds (x, t) :=
      hφ_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds hφ_neg)
    have hnhds : Q₆ ∈ nhds (x, t) := by
      refine Filter.mem_of_superset (Filter.inter_mem hx_mem hgap) ?_
      rintro y ⟨hyx, hygap⟩
      rw [mem_Q₆_iff]
      refine ⟨hyx, ?_⟩
      have hylt : 1 / Real.rpow y.1 p - y.2 < 0 := by
        simpa [φ] using hygap
      linarith
    exact mem_interior_iff_mem_nhds.mpr hnhds

/-- Helper for Theorem 5.4.8.7: on the positive unit slice, the strict one-sided power-cone
slack `1 < x^(p/(p+1)) t^(1-p/(p+1))` is equivalent to `x^{-p} < t`. -/
lemma power_cone_plus_unit_slice_lt_iff {x t : ℝ}
    (hp : 0 < p) (hx : 0 < x) (ht : 0 < t) :
    1 < powerConeGeometricMean (p / (p + 1)) (x, t) ↔
      1 / Real.rpow x p < t := by
  have hp1 : 0 < p + 1 := by
    linarith
  have hβ_pos : 0 < 1 / (p + 1) := one_div_pos.mpr hp1
  have hxp_pos : 0 < Real.rpow x p := Real.rpow_pos_of_pos hx p
  have hα :
      p / (p + 1) = p * (1 / (p + 1)) := by
    rw [div_eq_mul_one_div]
  have hβ :
      1 - p * (1 / (p + 1)) = 1 / (p + 1) := by
    field_simp [hp1.ne']
    ring
  have hgeom :
      powerConeGeometricMean (p / (p + 1)) (x, t) =
        Real.rpow (Real.rpow x p * t) (1 / (p + 1)) := by
    rw [powerConeGeometricMean_apply, hα, hβ]
    have hxpow :
        Real.rpow (Real.rpow x p) (1 / (p + 1)) =
          Real.rpow x (p * (1 / (p + 1))) := by
      exact (Real.rpow_mul hx.le p (1 / (p + 1))).symm
    have hmulrpow :
        Real.rpow (Real.rpow x p * t) (1 / (p + 1)) =
          Real.rpow (Real.rpow x p) (1 / (p + 1)) * Real.rpow t (1 / (p + 1)) := by
      exact Real.mul_rpow (Real.rpow_nonneg hx.le p) ht.le
    calc
      Real.rpow x (p * (1 / (p + 1))) * Real.rpow t (1 / (p + 1))
          = Real.rpow (Real.rpow x p) (1 / (p + 1)) * Real.rpow t (1 / (p + 1)) := by
              rw [← hxpow]
      _ = Real.rpow (Real.rpow x p * t) (1 / (p + 1)) := by
            rw [hmulrpow]
  rw [hgeom]
  constructor
  · intro h
    have hpow :
        (1 : ℝ) ^ (1 / (p + 1)) <
          (Real.rpow x p * t) ^ (1 / (p + 1)) := by
      simpa using h
    have hmul : 1 < Real.rpow x p * t := by
      simpa using
        (Real.rpow_lt_rpow_iff (show 0 ≤ (1 : ℝ) by norm_num)
          (mul_nonneg (Real.rpow_nonneg hx.le p) ht.le) hβ_pos).1 hpow
    have hxp_ne : Real.rpow x p ≠ 0 := hxp_pos.ne'
    field_simp [hxp_ne]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  · intro h
    have hmul : 1 < Real.rpow x p * t := by
      have hxp_ne : Real.rpow x p ≠ 0 := hxp_pos.ne'
      field_simp [hxp_ne] at h
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hpow :
        (1 : ℝ) ^ (1 / (p + 1)) <
          (Real.rpow x p * t) ^ (1 / (p + 1)) := by
      exact Real.rpow_lt_rpow (by norm_num) hmul hβ_pos
    simpa using hpow

/-- Helper for Theorem 5.4.8.7: on the affine slice `((x, t), 1)`, membership in
`interior (K_[p / (p + 1)]⁺)` is exactly membership in `interior (Q₆ p)`. -/
theorem mem_interior_power_cone_plus_unitSlice_qSix_iff {x t : ℝ} (hp : 0 < p) :
    ((x, t), 1) ∈ interior (K_[(p / (p + 1))]⁺) ↔ (x, t) ∈ interior Q₆ := by
  have hp1 : 0 < p + 1 := by
    linarith
  have hα₀ : 0 < p / (p + 1) := div_pos hp hp1
  have hα₁ : p / (p + 1) < 1 := by
    have hp1_ne : p + 1 ≠ 0 := by
      linarith
    field_simp [hp1_ne]
    linarith
  rw [mem_interior_power_cone_plus_iff hα₀ hα₁, mem_interior_qSix_iff (p := p)]
  constructor
  · rintro ⟨hx, ht, hslack⟩
    refine ⟨hx, ?_⟩
    exact (power_cone_plus_unit_slice_lt_iff (p := p) hp hx ht).1 hslack
  · rintro ⟨hx, hbound⟩
    have ht : 0 < t := by
      have hxp_pos : 0 < Real.rpow x p := Real.rpow_pos_of_pos hx p
      have hinv_pos : 0 < 1 / Real.rpow x p := one_div_pos.mpr hxp_pos
      linarith
    refine ⟨hx, ht, ?_⟩
    exact (power_cone_plus_unit_slice_lt_iff (p := p) hp hx ht).2 hbound

/-- Helper for Theorem 5.4.8.7: restricting the Chapter 5 one-sided power-cone barrier to the
unit slice `((x, t), 1)` reproduces the source-facing barrier `F₆`. -/
theorem separableLogBarrierF6_eq_powerConePlusBarrier_unitSlice
    (p x t : ℝ) :
    separableLogBarrierF6 p (x, t) =
      power_cone_plus_barrier (p / (p + 1)) ((x, t), 1) := by
  -- Evaluate both barrier owners on the fixed unit slice and normalize the order of summands.
  rw [separableLogBarrierF6_apply, power_cone_plus_barrier_apply]
  ring_nf

-- Proof sketch: identify `Q₆` with the affine unit slice `((x, t), 1)` of the one-sided power
-- cone with exponent `α = p / (p + 1)`, then pull back the imported barrier theorem from
-- `Theorem_5_4_7_4` along that affine slice.
/-- Theorem 5.4.8.7: for `p > 0`, the function
`F₆(x, t) = -\log x - \log t - \log (x^α t^(1 - α) - 1)` with `α = p / (p + 1)` is a
`3`-self-concordant barrier for `Q₆ = {(x, t) ∈ \mathbb{R}^2 \mid x > 0,\ t ≥ x^{-p}}`. -/
theorem separableLogBarrierF6_is_three_selfConcordantBarrier
    (hp : 0 < p) :
    IsSelfConcordantBarrierOnWith (interior Q₆) (3 : NNReal) F₆ := by
  let α : ℝ := p / (p + 1)
  have hα₀ : 0 < α := by
    have hp1 : 0 < p + 1 := by
      linarith
    dsimp [α]
    exact div_pos hp hp1
  have hα₁ : α < 1 := by
    have hp1 : 0 < p + 1 := by
      linarith
    have hp1_ne : p + 1 ≠ 0 := by
      linarith
    dsimp [α]
    field_simp [hp1_ne]
    linarith
  -- Route correction: use named slice-transport lemmas instead of the earlier anonymous affine
  -- map and broad final `simp`, so the pullback proof matches the stable sibling pattern.
  have hbase :
      IsSelfConcordantBarrierOnWith
        (interior (K_[α]⁺))
        (3 : NNReal)
        (power_cone_plus_barrier α) :=
    power_cone_plus_barrier_is_three_self_concordant_barrier hα₀ hα₁
  have hslice :
      IsSelfConcordantBarrierOnWith
        (powerConePlusUnitSliceAffine ⁻¹' interior (K_[α]⁺))
        (3 : NNReal)
        (power_cone_plus_barrier α ∘ powerConePlusUnitSliceAffine) :=
    hbase.comp_continuousAffineMap powerConePlusUnitSliceAffine
  have hdom : powerConePlusUnitSliceAffine ⁻¹' interior (K_[α]⁺) = interior Q₆ := by
    -- Rewrite the pulled-back domain through the unit-slice interior equivalence.
    ext q
    change powerConePlusUnitSliceAffine q ∈ interior (K_[α]⁺) ↔ q ∈ interior Q₆
    rw [powerConePlusUnitSliceAffine_apply]
    simpa [α] using mem_interior_power_cone_plus_unitSlice_qSix_iff (p := p) hp
  have hfun : power_cone_plus_barrier α ∘ powerConePlusUnitSliceAffine = F₆ := by
    -- Evaluate both sides on the unit slice and use the named barrier identity.
    funext q
    rw [Function.comp_apply, powerConePlusUnitSliceAffine_apply]
    simpa [α] using
      (separableLogBarrierF6_eq_powerConePlusBarrier_unitSlice p q.1 q.2).symm
  simpa [hdom, hfun] using hslice
