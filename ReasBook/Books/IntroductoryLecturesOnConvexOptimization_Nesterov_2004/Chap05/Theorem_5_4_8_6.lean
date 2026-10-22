/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_3_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.RealProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_4

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

/- Theorem 5.4.8.6 lies in the Chapter 5 self-concordant-barrier / power-cone-slice domain.

Sampled owner declarations:
* `Q₅` and `mem_Q₅_iff` from `Definition_5_4_8_13`, the source-facing owner/view for `Q₅`;
* `separableLogBarrierF5` and `separableLogBarrierF5_apply` from `Definition_5_4_8_14`, the
  source-facing owner/view for `F₅`;
* `power_cone_plus`, `power_cone_plus_barrier`, and
  `power_cone_plus_barrier_is_three_self_concordant_barrier` from `Theorem_5_4_7_4`, the
  upstream owner theorem on the one-sided power cone;
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` from `Theorem_5_3_3`, the canonical
  affine-pullback theorem for barrier owners.

Best owner abstraction:
* source-facing: the textbook set `Q₅` and barrier `F₅`;
* core/canonical: `K_[p]⁺`, `power_cone_plus_barrier p`, and
  `IsSelfConcordantBarrierOnWith`;
* bridge/view: the affine slice `((t, 1), x)` identifying `Q₅` and `F₅` with those upstream
  power-cone owners.

Primitive data:
* the source-facing owner `Q₅ p`;
* the canonical slice owner `F₅ = power_cone_plus_barrier p ∘ ((t, 1), x)`.

Derived API:
* the interior-membership theorem for `Q₅`;
* the interior slice-domain bridge to `K_[p]⁺`;
* the resulting source-facing barrier theorem.

Source/core/bridge triage:
* source-facing: Theorem 5.4.8.6 itself;
* core/canonical: the one-sided power-cone barrier theorem from `Theorem_5_4_7_4`;
* bridge/view: the interior unit-slice theorem below.

The previous proof sketch used the wrong slice `((1, t), x)`, which corresponds to
`x ≤ t^(1 - p)` rather than `x ≤ t^p`. The correct source-faithful bridge is the affine slice
`((t, 1), x)`. -/

local notation "Q₅" => Q₅ p

local notation "F₅" => separableLogBarrierF5 p

-- Proof sketch: use that for `p > 0` the map `t ↦ t^p` is continuous on `(0, ∞)`, so the
-- interior of the canonical closed constrained sublevel set `Q₅` is obtained by replacing the
-- boundary conditions `t ≥ 0` and `x ≤ t^p` with the strict inequalities `t > 0` and `x < t^p`.
/-- Helper for Theorem 5.4.8.6: a pair `(x, t)` lies in the interior of the canonical
constrained sublevel set for Definition 5.4.8.13 exactly when `t > 0` and `x < t^p`. -/
theorem mem_interior_constrainedSublevelSet_sub_rpow_iff
    {x t : ℝ} (hp0 : 0 < p) :
    (x, t) ∈ interior Q₅ ↔ 0 < t ∧ x < Real.rpow t p := by
  constructor
  · intro h
    have hQ : (x, t) ∈ Q₅ := interior_subset h
    rw [mem_Q₅_iff] at hQ
    rcases hQ with ⟨ht, hx_le⟩
    -- Strictify the `t ≥ 0` boundary by perturbing the second coordinate downward.
    have ht_strict : 0 < t := by
      by_contra ht_nonpos
      have ht_zero : t = 0 := le_antisymm (le_of_not_gt ht_nonpos) ht
      let γ : ℝ → ℝ × ℝ := fun s ↦ (x, s)
      have hγ : Continuous γ := by
        fun_prop
      have hpre : γ ⁻¹' interior Q₅ ∈ nhds t := by
        exact hγ.continuousAt.preimage_mem_nhds
          (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using h))
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
      have hneg : -ε / 2 ∈ Metric.ball t ε := by
        have hhalf_neg : -ε / 2 < 0 := by
          linarith
        have habs : |(-ε / 2 : ℝ) - 0| = ε / 2 := by
          rw [sub_zero, abs_of_neg hhalf_neg]
          ring
        rw [ht_zero, Metric.mem_ball, Real.dist_eq, habs]
        linarith
      have hmem : γ (-ε / 2) ∈ interior Q₅ := hεsub hneg
      have hQneg : γ (-ε / 2) ∈ Q₅ := interior_subset hmem
      rw [mem_Q₅_iff] at hQneg
      linarith
    -- Strictify the gap constraint by perturbing the first coordinate upward.
    have hx_strict : x < Real.rpow t p := by
      by_contra hx_not
      have hx_eq : x = Real.rpow t p := le_antisymm hx_le (not_lt.mp hx_not)
      let γ : ℝ → ℝ × ℝ := fun s ↦ (s, t)
      have hγ : Continuous γ := by
        fun_prop
      have hpre : γ ⁻¹' interior Q₅ ∈ nhds x := by
        exact hγ.continuousAt.preimage_mem_nhds
          (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using h))
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
      have hup : x + ε / 2 ∈ Metric.ball x ε := by
        have hhalf_nonneg : 0 ≤ x + ε / 2 - x := by
          linarith
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hhalf_nonneg]
        linarith
      have hmem : γ (x + ε / 2) ∈ interior Q₅ := hεsub hup
      have hQup : γ (x + ε / 2) ∈ Q₅ := interior_subset hmem
      rw [mem_Q₅_iff] at hQup
      have hboundary : x + ε / 2 ≤ Real.rpow t p := hQup.2
      linarith
    exact ⟨ht_strict, hx_strict⟩
  · rintro ⟨ht, hx⟩
    let φ : ℝ × ℝ → ℝ := fun q ↦ q.1 - Real.rpow q.2 p
    -- Build an open neighborhood from the two strict inequalities `t > 0` and `x - t^p < 0`.
    have ht_mem :
        Prod.snd ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds (x, t) :=
      continuousAt_snd.preimage_mem_nhds (isOpen_Ioi.mem_nhds ht)
    have hφ_cont : ContinuousAt φ (x, t) := by
      have hrpow :
          ContinuousAt (fun q : ℝ × ℝ ↦ Real.rpow q.2 p) (x, t) := by
        simpa using continuousAt_snd.rpow_const (Or.inr hp0.le)
      simpa [φ] using continuousAt_fst.sub hrpow
    have hφ_neg : φ (x, t) < 0 := by
      simpa [φ] using sub_neg.mpr hx
    have hgap :
        φ ⁻¹' Set.Iio (0 : ℝ) ∈ nhds (x, t) :=
      hφ_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds hφ_neg)
    have hnhds : Q₅ ∈ nhds (x, t) := by
      refine Filter.mem_of_superset (Filter.inter_mem ht_mem hgap) ?_
      rintro y ⟨hy_t, hy_gap⟩
      rw [mem_Q₅_iff]
      refine ⟨le_of_lt hy_t, ?_⟩
      have hy_lt : y.1 < Real.rpow y.2 p := by
        simpa [φ] using hy_gap
      linarith
    exact mem_interior_iff_mem_nhds.mpr hnhds

/-- Helper for Theorem 5.4.8.6: on the endpoint slice `p = 1`, interior membership in `Q₅`
is equivalent to the two affine slack inequalities `t > 0` and `t - x > 0`. -/
lemma mem_interior_qFive_one_iff {q : ℝ × ℝ} :
    q ∈ interior (_root_.Q₅ (1 : ℝ)) ↔ 0 < q.2 ∧ 0 < q.2 - q.1 := by
  rcases q with ⟨x, t⟩
  rw [mem_interior_constrainedSublevelSet_sub_rpow_iff (p := (1 : ℝ)) zero_lt_one]
  constructor
  · rintro ⟨ht, hx⟩
    constructor
    · exact ht
    · have hx' : x < t := by
        simpa using hx
      linarith
  · rintro ⟨ht, hgap⟩
    constructor
    · exact ht
    · have hx' : x < t := by
        linarith
      simpa using hx'

/-- Helper for Theorem 5.4.8.6: the scalar barrier `x ↦ -log x` pulled back along the second
coordinate projection gives a `1`-self-concordant barrier on the slack domain `t > 0`. -/
lemma snd_negLog_isSelfConcordantBarrierOn :
    IsSelfConcordantBarrierOnWith
      ((fun q : ℝ × ℝ ↦ q.2) ⁻¹' Set.Ioi (0 : ℝ))
      1
      (fun q : ℝ × ℝ ↦ -Real.log q.2) := by
  let sndMap : (ℝ × ℝ) →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  -- Pull back the scalar nonnegative-ray barrier along the projection `q ↦ t`.
  simpa [sndMap, Function.comp] using
    (negLog_isSelfConcordantBarrierOnWith_nonnegativeRay.comp_continuousAffineMap sndMap)

/-- Helper for Theorem 5.4.8.6: the scalar barrier `x ↦ -log x` pulled back along the affine
gap map `q ↦ q.2 - q.1` gives a `1`-self-concordant barrier on the slack domain `t - x > 0`. -/
lemma gap_negLog_isSelfConcordantBarrierOn :
    IsSelfConcordantBarrierOnWith
      ((fun q : ℝ × ℝ ↦ q.2 - q.1) ⁻¹' Set.Ioi (0 : ℝ))
      1
      (fun q : ℝ × ℝ ↦ -Real.log (q.2 - q.1)) := by
  let gapMap : (ℝ × ℝ) →ᴬ[ℝ] ℝ :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ) - (ContinuousLinearMap.fst ℝ ℝ ℝ)).toContinuousAffineMap
  -- Pull back the same scalar owner along the affine slack `q ↦ t - x`.
  simpa [gapMap, Function.comp] using
    (negLog_isSelfConcordantBarrierOnWith_nonnegativeRay.comp_continuousAffineMap gapMap)

/-- Helper for Theorem 5.4.8.6: at the endpoint `p = 1`, the source-facing barrier
`F₅(x, t) = -log t - log (t - x)` is the sharp `2`-self-concordant barrier obtained by summing
the two affine `-log` slack barriers. -/
theorem separableLogBarrierF5_one_is_two_selfConcordantBarrier :
    IsSelfConcordantBarrierOnWith
      (interior (_root_.Q₅ (1 : ℝ)))
      (2 : NNReal)
      (separableLogBarrierF5 (1 : ℝ)) := by
  have hsnd := snd_negLog_isSelfConcordantBarrierOn
  have hgap := gap_negLog_isSelfConcordantBarrierOn
  have hν : (1 : NNReal) + 1 = 2 := by
    norm_num
  have hdom :
      ((fun q : ℝ × ℝ ↦ q.2) ⁻¹' Set.Ioi (0 : ℝ)) ∩
          ((fun q : ℝ × ℝ ↦ q.2 - q.1) ⁻¹' Set.Ioi (0 : ℝ)) =
        interior (_root_.Q₅ (1 : ℝ)) := by
    ext q
    rw [mem_interior_qFive_one_iff]
    simp [Set.mem_preimage]
  have hfun :
      (fun q : ℝ × ℝ ↦ -Real.log q.2) + (fun q : ℝ × ℝ ↦ -Real.log (q.2 - q.1)) =
        separableLogBarrierF5 (1 : ℝ) := by
    funext q
    rcases q with ⟨x, t⟩
    -- Rewrite the summed slack barrier to the source-facing endpoint formula.
    rw [Pi.add_apply, separableLogBarrierF5_apply]
    simp [Real.rpow_one, sub_eq_add_neg]
  simpa [hν, hdom, hfun] using hsnd.add hgap

-- Proof sketch: the slice point `((t, 1), x)` belongs to `interior (K_[p]⁺)` exactly when the
-- first coordinate stays positive and the power-cone slack
-- `x₁^p x₂^(1 - p) - z` stays positive. On the unit slice `x₂ = 1`, that strict slack is
-- `t^p - x`, which is the same strict condition that describes `interior Q₅`.
/-- On the affine slice `((t, 1), x)`, membership in `interior (K_[p]⁺)` is exactly membership
in `interior Q₅`. -/
theorem mem_interior_power_cone_plus_unitSlice_iff {x t : ℝ} (hp0 : 0 < p) :
    ((t, 1), x) ∈ interior (K_[p]⁺) ↔ (x, t) ∈ interior Q₅ := by
  rw [mem_interior_constrainedSublevelSet_sub_rpow_iff p hp0]
  constructor
  · intro h
    have hK : ((t, 1), x) ∈ K_[p]⁺ := interior_subset h
    rw [mem_power_cone_plus_iff, powerConeGeometricMean_apply] at hK
    rcases hK with ⟨ht, -, hx_raw⟩
    have hx : x ≤ Real.rpow t p := by
      simpa using hx_raw
    have ht_strict : 0 < t := by
      by_contra ht_nonpos
      have ht_zero : t = 0 := le_antisymm (le_of_not_gt ht_nonpos) ht
      let γ : ℝ → ((ℝ × ℝ) × ℝ) := fun s ↦ ((s, 1), x)
      have hγ : Continuous γ := by
        fun_prop
      have hpre :
          γ ⁻¹' interior (K_[p]⁺) ∈ nhds t := by
        exact hγ.continuousAt.preimage_mem_nhds
          (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using h))
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
      have hneg : -ε / 2 ∈ Metric.ball t ε := by
        have hhalf_neg : -ε / 2 < 0 := by
          linarith
        have habs : |(-ε / 2 : ℝ) - 0| = ε / 2 := by
          rw [sub_zero, abs_of_neg hhalf_neg]
          ring
        rw [ht_zero, Metric.mem_ball, Real.dist_eq, habs]
        linarith
      have hmem : γ (-ε / 2) ∈ interior (K_[p]⁺) := hεsub hneg
      have hcone : γ (-ε / 2) ∈ K_[p]⁺ := interior_subset hmem
      simp [γ, mem_power_cone_plus_iff, powerConeGeometricMean_apply] at hcone
      linarith
    have hx_strict : x < Real.rpow t p := by
      by_contra hx_not
      have hx_eq : x = Real.rpow t p := le_antisymm hx (not_lt.mp hx_not)
      let γ : ℝ → ((ℝ × ℝ) × ℝ) := fun z ↦ ((t, 1), z)
      have hγ : Continuous γ := by
        fun_prop
      have hpre :
          γ ⁻¹' interior (K_[p]⁺) ∈ nhds x := by
        exact hγ.continuousAt.preimage_mem_nhds
          (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using h))
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
      have hup : x + ε / 2 ∈ Metric.ball x ε := by
        have hhalf_nonneg : 0 ≤ x + ε / 2 - x := by
          linarith
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hhalf_nonneg]
        linarith
      have hmem : γ (x + ε / 2) ∈ interior (K_[p]⁺) := hεsub hup
      have hcone : γ (x + ε / 2) ∈ K_[p]⁺ := interior_subset hmem
      simp [γ, mem_power_cone_plus_iff, powerConeGeometricMean_apply, hx_eq] at hcone
      linarith
    exact ⟨ht_strict, hx_strict⟩
  · rintro ⟨ht, hx⟩
    let q : ((ℝ × ℝ) × ℝ) := ((t, 1), x)
    let φ : ((ℝ × ℝ) × ℝ) → ℝ := fun y ↦ powerConeGeometricMean p y.1 - y.2
    have hφ_pos : 0 < φ q := by
      simpa [q, φ, powerConeGeometricMean_apply] using sub_pos.mpr hx
    have hφ_cont : ContinuousAt φ q := by
      have hfst :
          ContinuousAt (fun y : ((ℝ × ℝ) × ℝ) ↦ Real.rpow y.1.1 p) q :=
        by simpa using continuousAt_fst.fst.rpow_const (Or.inl ht.ne')
      have hsnd :
          ContinuousAt (fun y : ((ℝ × ℝ) × ℝ) ↦ Real.rpow y.1.2 (1 - p)) q :=
        by simpa using continuousAt_fst.snd.rpow_const (Or.inl one_ne_zero)
      have hmul :
          ContinuousAt
            (fun y : ((ℝ × ℝ) × ℝ) ↦ Real.rpow y.1.1 p * Real.rpow y.1.2 (1 - p))
            q :=
        hfst.mul hsnd
      simpa [φ, powerConeGeometricMean_apply] using hmul.sub continuousAt_snd
    have hfirst :
        (fun y : ((ℝ × ℝ) × ℝ) ↦ y.1.1) ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds q :=
      continuousAt_fst.fst.preimage_mem_nhds (isOpen_Ioi.mem_nhds ht)
    have hsecond :
        (fun y : ((ℝ × ℝ) × ℝ) ↦ y.1.2) ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds q :=
      continuousAt_fst.snd.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by norm_num : 0 < (1 : ℝ)))
    have hslack : φ ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds q :=
      hφ_cont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hφ_pos)
    have hnhds : K_[p]⁺ ∈ nhds q := by
      refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem hfirst hsecond) hslack) ?_
      rintro y ⟨⟨hy1, hy2⟩, hy3⟩
      rw [mem_power_cone_plus_iff, powerConeGeometricMean_apply]
      refine ⟨le_of_lt hy1, le_of_lt hy2, ?_⟩
      have hy3' : 0 < powerConeGeometricMean p y.1 - y.2 := by
        simpa [φ] using hy3
      have hylt : y.2 < powerConeGeometricMean p y.1 := by
        linarith
      exact le_of_lt hylt
    exact mem_interior_iff_mem_nhds.mpr hnhds

-- Proof sketch: for `0 < p < 1`, identify `Q₅` with the affine slice
-- `{{((x₁, x₂), z) | x₂ = 1}} ∩ K_[p]⁺` via `((t, 1), x)`, and rewrite
-- `separableLogBarrierF5 p` as the restriction of the canonical cone-composition barrier from
-- `Theorem_5_4_7_4`. Then apply preservation of self-concordant barriers under affine
-- restriction. For the endpoint `p = 1`, the set becomes the linear epigraph `{(x, t) | t ≥ 0,
-- x ≤ t}` and the same logarithmic formula is the standard two-slack barrier with parameter `3`.
/-- Theorem 5.4.8.6: for `0 < p ≤ 1`, the function
`F₅(x, t) = -\log t - \log (t^p - x)` is a `3`-self-concordant barrier for the hypograph-type
constraint set `Q₅ = {(x, t) ∈ \mathbb{R}^2 \mid t ≥ 0,\ t^p ≥ x}`. -/
theorem separableLogBarrierF5_is_three_selfConcordantBarrier
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    IsSelfConcordantBarrierOnWith (interior Q₅) (3 : NNReal) F₅ := by
  rcases lt_or_eq_of_le hp1 with hp1_lt | rfl
  · let g : (ℝ × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
      (((ContinuousLinearMap.snd ℝ ℝ ℝ).prod
          (0 : (ℝ × ℝ) →L[ℝ] ℝ)).prod
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).toContinuousAffineMap +ᵥ
        ContinuousAffineMap.const ℝ (ℝ × ℝ) (((0 : ℝ), (1 : ℝ)), (0 : ℝ))
    have hg_apply (q : ℝ × ℝ) : g q = ((q.2, 1), q.1) := by
      simp [g]
    let hbase :
        IsSelfConcordantBarrierOnWith
          (interior (K_[p]⁺))
          (3 : NNReal)
          (power_cone_plus_barrier p) :=
      power_cone_plus_barrier_is_three_self_concordant_barrier hp0 hp1_lt
    let hslice :
        IsSelfConcordantBarrierOnWith
          (g ⁻¹' interior (K_[p]⁺))
          (3 : NNReal)
          (power_cone_plus_barrier p ∘ g) :=
      hbase.comp_continuousAffineMap g
    have hdom : g ⁻¹' interior (K_[p]⁺) = interior Q₅ := by
      ext q
      change g q ∈ interior (K_[p]⁺) ↔ q ∈ interior Q₅
      rw [hg_apply]
      simpa using mem_interior_power_cone_plus_unitSlice_iff p hp0
    have hfun : power_cone_plus_barrier p ∘ g = F₅ := by
      funext q
      change power_cone_plus_barrier p (g q) = separableLogBarrierF5 p q
      rw [hg_apply]
      rfl
    simpa [hdom, hfun] using hslice
  · let h2 := separableLogBarrierF5_one_is_two_selfConcordantBarrier
    -- The endpoint barrier is sharp with parameter `2`; enlarge it to the stated `3`.
    refine
      { toIsStandardSelfConcordantOn := h2.toIsStandardSelfConcordantOn
        barrier_parameter_bound := ?_ }
    intro q hq u
    exact le_trans (h2.barrier_parameter_bound hq u) (by norm_num)
