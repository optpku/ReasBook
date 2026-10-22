/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part13

section Chap05
section Section24

open scoped ConvexAnalysis
open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Helper for Corollary 5.24.2: the eventual subdifferential inclusion from Theorem 5.24.8 can
be upgraded to a uniform closed-ball neighborhood around any interior-domain point. -/
lemma helperForCorollary_5_24_2_local_subdifferential_subset
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x : Fin n → ℝ}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ⦃z : Fin n → ℝ⦄, z ∈ Metric.closedBall x δ →
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f z) ⊆
          Set.image2 (fun u v : Fin n → ℝ => u + v)
            ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
            (Metric.closedBall (0 : Fin n → ℝ) ε) := by
  let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
  rcases helperForCorollary_5_24_2_constantSequenceSetup (f := f) hproper with
    ⟨hf, hCopen, hCconv, hf_finite⟩
  -- Choose a small ambient ball around `x` that stays inside `int (dom f)`.
  obtain ⟨r, hrpos, hrball⟩ : ∃ r > 0, Metric.ball x r ⊆ C := by
    exact Metric.mem_nhds_iff.1 (hCopen.mem_nhds hx)
  by_contra hLocal
  push_neg at hLocal
  let targetSet : Set (Fin n → ℝ) :=
    Set.image2 (fun u v : Fin n → ℝ => u + v)
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
      (Metric.closedBall (0 : Fin n → ℝ) ε)
  let δSeq : ℕ → ℝ := fun k => min (r / 2) (1 / (k + 1 : ℝ))
  have hδSeq_pos : ∀ k, 0 < δSeq k := by
    intro k
    refine lt_min ?_ ?_
    · linarith
    · exact one_div_pos.2 (by positivity)
  have hbad :
      ∀ k, ∃ z : Fin n → ℝ, z ∈ Metric.closedBall x (δSeq k) ∧
        ¬ (((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f z) ⊆ targetSet) := by
    intro k
    exact hLocal (δSeq k) (hδSeq_pos k)
  choose zSeq hzSeq_mem hzSeq_bad using hbad
  have hzSeq_mem_C : ∀ k, zSeq k ∈ C := by
    intro k
    have hz_half :
        zSeq k ∈ Metric.closedBall x (r / 2) := by
      exact Metric.closedBall_subset_closedBall (min_le_left _ _) (hzSeq_mem k)
    have hz_ball :
        zSeq k ∈ Metric.ball x r := by
      exact Metric.closedBall_subset_ball (by linarith [hrpos]) hz_half
    exact hrball hz_ball
  have hdist_bound :
      ∀ k, dist (zSeq k) x ≤ (1 / (k + 1 : ℝ)) := by
    intro k
    have hzDist : dist (zSeq k) x ≤ δSeq k := by
      simpa [Metric.mem_closedBall, dist_comm] using hzSeq_mem k
    exact hzDist.trans (min_le_right _ _)
  have hdist_tendsto_zero :
      Filter.Tendsto (fun k => dist (zSeq k) x) Filter.atTop (nhds 0) := by
    -- The radii `δₖ ≤ 1 / (k + 1)` squeeze the bad points back to `x`.
    refine squeeze_zero (fun _ => dist_nonneg) hdist_bound
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hzSeq_tendsto : Filter.Tendsto zSeq Filter.atTop (nhds x) := by
    simpa using (tendsto_iff_dist_tendsto_zero.2 hdist_tendsto_zero)
  have hpoint :
      ∀ z ∈ C, Filter.Tendsto (fun _ : ℕ => f z) Filter.atTop (nhds (f z)) := by
    intro z hz
    -- Again the constant sequence converges pointwise immediately.
    simpa using Filter.tendsto_const_nhds
  have hmain :=
    convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
      (C := C) hCopen hCconv hf hf_finite (fun _ => f) (fun _ => hf)
      (fun _ z hz => hf_finite z hz) hx zSeq hzSeq_mem_C hzSeq_tendsto hpoint
  rcases hmain.2 ε hε with ⟨i0, hi0⟩
  have hball_eq : ({v : Fin n → ℝ | ‖v‖ ≤ ε} : Set (Fin n → ℝ)) =
      Metric.closedBall (0 : Fin n → ℝ) ε := by
    ext v
    simp [mem_closedBall_zero_iff]
  have hgood :
      ∀ i ≥ i0,
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f (zSeq i)) ⊆ targetSet := by
    intro i hi
    have hraw := hi0 i hi
    simpa [targetSet, hball_eq] using hraw
  exact hzSeq_bad i0 (hgood i0 le_rfl)

-- Proof sketch: apply Theorem 5.24.8 to the constant sequence `fᵢ = f` on the open set
-- `interior (dom f)`. This yields upper semicontinuity of `(x, y) ↦ f'(x; y)` on
-- `int (dom f) × ℝ^n`. For the subdifferentials, use the same constant-sequence specialization
-- to obtain the required closed-ball inclusion.
/-- Corollary 5.24.2: if `f` is a proper convex function on `ℝ^n`, then the upper directional
derivative map `(x, y) ↦ f'(x; y)` is upper semicontinuous on
`int (dom f) × ℝ^n`. Moreover, for every `x ∈ int (dom f)` and every `ε > 0`, there exists
`δ > 0` such that for every `z ∈ Metric.closedBall x δ`, the subdifferential `∂ f (z)` is contained in
`∂ f (x) + ε B`, written in Lean after identifying covectors with vectors via
`dotProductEquiv ℝ (Fin n)`. -/
theorem properConvex_upperSemicontinuousOn_upperDirectionalDerivative_and_subdifferential_subset
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    UpperSemicontinuousOn
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => upperDirectionalDerivativeAt f p.1 p.2)
        (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ×ˢ
          (Set.univ : Set (Fin n → ℝ))) ∧
      ∀ ⦃x : Fin n → ℝ⦄,
        x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) →
          ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
            ∀ ⦃z : Fin n → ℝ⦄, z ∈ Metric.closedBall x δ →
              ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f z) ⊆
                Set.image2 (fun u v : Fin n → ℝ => u + v)
                  ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
                  (Metric.closedBall (0 : Fin n → ℝ) ε) := by
  refine ⟨?_, ?_⟩
  · -- The first clause is exactly the upper-semicontinuity packaging of the limsup inequality.
    exact
      helperForCorollary_5_24_2_upperSemicontinuousOn_upperDirectionalDerivative
        (f := f) hproper
  · intro x hx ε hε
    -- The second clause is the local closed-ball reformulation of the eventual inclusion.
    exact
      helperForCorollary_5_24_2_local_subdifferential_subset
        (f := f) hproper hx ε hε

/-- The Euclidean face of `∂ f (x)` selected by the normal direction `y`: it consists of the
Euclidean representatives `xStar` of subgradients at `x` for which `y` lies in the normal cone of
the Euclideanized subdifferential at `xStar`. -/
def subdifferentialNormalFaceAt {n : ℕ} (f : (Fin n → ℝ) → EReal) (x y : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {xStar |
    dotProductEquiv ℝ (Fin n) xStar ∈ ∂ f x ∧
      ∀ zStar : Fin n → ℝ,
        dotProductEquiv ℝ (Fin n) zStar ∈ ∂ f x →
          dotProduct y (zStar - xStar) ≤ 0}

/-- Helper for Theorem 5.24.9: the ray hypothesis can always be strengthened to a strictly
positive parameter. -/
lemma helperForTheorem_5_24_9_positiveRayScale
    {n : ℕ} {f : (Fin n → ℝ) → EReal} {x y : Fin n → ℝ}
    (hray :
      ∃ t : ℝ, 0 ≤ t ∧ x + t • y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    ∃ s : ℝ, 0 < s ∧ x + s • y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
  rcases hray with ⟨t, ht_nonneg, ht_mem⟩
  by_cases ht_pos : 0 < t
  · -- If the given point already sits at positive distance on the ray, keep it.
    exact ⟨t, ht_pos, ht_mem⟩
  · have ht_zero : t = 0 := by linarith
    subst ht_zero
    -- Otherwise `x` itself is interior, so move a short positive step in the direction `y`.
    obtain ⟨r, hr_pos, hr_ball⟩ :
        ∃ r > 0, Metric.ball x r ⊆
          interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
      exact Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds (by simpa using ht_mem))
    let s : ℝ := min 1 (r / (2 * max 1 ‖y‖))
    have hmax_pos : 0 < max 1 ‖y‖ := by
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 ‖y‖)
    have hs_pos : 0 < s := by
      refine lt_min (by norm_num) ?_
      positivity
    have hs_le : s ≤ r / (2 * max 1 ‖y‖) := min_le_right _ _
    have hnorm_le_half : ‖s • y‖ ≤ r / 2 := by
      calc
        ‖s • y‖ = |s| * ‖y‖ := by simp [norm_smul]
        _ = s * ‖y‖ := by rw [abs_of_nonneg (le_of_lt hs_pos)]
        _ ≤ (r / (2 * max 1 ‖y‖)) * ‖y‖ := by
          exact mul_le_mul_of_nonneg_right hs_le (norm_nonneg y)
        _ ≤ (r / (2 * max 1 ‖y‖)) * max 1 ‖y‖ := by
          exact mul_le_mul_of_nonneg_left (le_max_right 1 ‖y‖) (by positivity)
        _ = r / 2 := by
          have hmax_ne : max 1 ‖y‖ ≠ 0 := ne_of_gt hmax_pos
          field_simp [hmax_ne]
    have hdist_lt : dist (x + s • y) x < r := by
      rw [dist_eq_norm]
      have hlt : ‖s • y‖ < r := by
        have hhalf_lt : r / 2 < r := by linarith
        exact lt_of_le_of_lt hnorm_le_half hhalf_lt
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlt
    have hs_mem_ball : x + s • y ∈ Metric.ball x r := by
      simpa [Metric.mem_ball, dist_comm] using hdist_lt
    exact ⟨s, hs_pos, hr_ball hs_mem_ball⟩

/-- Helper for Theorem 5.24.9: the secant lengths tend to `0`, remain positive, reconstruct the
original sequence, and carry the given normalized-direction convergence. -/
lemma helperForTheorem_5_24_9_normalizedSecantData
    {n : ℕ} {x y : Fin n → ℝ} (xSeq : ℕ → Fin n → ℝ)
    (hxSeq_tendsto : Filter.Tendsto xSeq Filter.atTop (nhds x))
    (hxSeq_ne : ∀ i : ℕ, xSeq i ≠ x)
    (hdir :
      Filter.Tendsto (fun i : ℕ => ‖xSeq i - x‖⁻¹ • (xSeq i - x)) Filter.atTop (nhds y)) :
    Filter.Tendsto (fun i : ℕ => ‖xSeq i - x‖) Filter.atTop (nhds 0) ∧
      (∀ i : ℕ, 0 < ‖xSeq i - x‖) ∧
      (∀ i : ℕ, xSeq i = x + ‖xSeq i - x‖ • (‖xSeq i - x‖⁻¹ • (xSeq i - x))) ∧
      Filter.Tendsto (fun i : ℕ => ‖xSeq i - x‖⁻¹ • (xSeq i - x)) Filter.atTop (nhds y) := by
  have hsub_tendsto : Filter.Tendsto (fun i : ℕ => xSeq i - x) Filter.atTop (nhds 0) := by
    simpa using
      (hxSeq_tendsto.sub tendsto_const_nhds :
        Filter.Tendsto (fun i : ℕ => xSeq i - x) Filter.atTop (nhds (x - x)))
  have hnorm_tendsto :
      Filter.Tendsto (fun i : ℕ => ‖xSeq i - x‖) Filter.atTop (nhds 0) := by
    simpa using hsub_tendsto.norm
  refine ⟨hnorm_tendsto, ?_, ?_, hdir⟩
  · intro i
    simpa [sub_eq_zero] using sub_ne_zero.mpr (hxSeq_ne i)
  · intro i
    have hnorm_ne : ‖xSeq i - x‖ ≠ 0 := by
      exact ne_of_gt (by simpa [sub_eq_zero] using sub_ne_zero.mpr (hxSeq_ne i))
    -- Rewrite the normalized secant by cancelling its scalar length.
    calc
      xSeq i = x + (xSeq i - x) := by abel
      _ = x + (1 : ℝ) • (xSeq i - x) := by simp
      _ = x + (‖xSeq i - x‖ * ‖xSeq i - x‖⁻¹) • (xSeq i - x) := by
            rw [mul_inv_cancel₀ hnorm_ne]
      _ = x + ‖xSeq i - x‖ • (‖xSeq i - x‖⁻¹ • (xSeq i - x)) := by
            rw [smul_smul]

/-- Helper for Theorem 5.24.9: the fixed ray-neighborhood
`{u | x + s • u ∈ int (dom f)}` is open and convex, contains `y`, and every shorter positive
secant from `x` to a point on that neighborhood stays inside `int (dom f)` with finite `f`
value. -/
lemma helperForTheorem_5_24_9_rayNeighborhood_geometry
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x y : Fin n → ℝ}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    {s : ℝ} (hs_pos : 0 < s)
    (hsy_mem :
      x + s • y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    let C : Set (Fin n → ℝ) :=
      {u : Fin n → ℝ | x + s • u ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)}
    IsOpen C ∧
      Convex ℝ C ∧
      y ∈ C ∧
      ∀ {u : Fin n → ℝ} {t : ℝ}, u ∈ C → 0 < t → t ≤ s →
        x + t • u ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
          f (x + t • u) ≠ (⊤ : EReal) ∧
          f (x + t • u) ≠ (⊥ : EReal) := by
  let domf : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
  let C : Set (Fin n → ℝ) := {u : Fin n → ℝ | x + s • u ∈ interior domf}
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hdomf_conv : Convex ℝ domf := effectiveDomain_convex (S := (Set.univ : Set _)) hf
  have hC_open : IsOpen C := by
    -- The neighborhood is the preimage of `int (dom f)` under an affine map.
    simpa [C, domf] using
      isOpen_interior.preimage (continuous_const.add (continuous_const.smul continuous_id))
  have hC_conv : Convex ℝ C := by
    intro u hu v hv a b ha hb hab
    change x + s • (a • u + b • v) ∈ interior domf
    have hmix :
        a • (x + s • u) + b • (x + s • v) ∈ interior domf :=
      hdomf_conv.interior hu hv ha hb hab
    have hrewrite :
        x + s • (a • u + b • v) = a • (x + s • u) + b • (x + s • v) := by
      have hab' : a = 1 - b := by linarith
      ext i
      rw [hab']
      simp
      ring
    exact hrewrite ▸ hmix
  have hy_mem : y ∈ C := by
    simpa [C, domf] using hsy_mem
  refine ⟨hC_open, hC_conv, hy_mem, ?_⟩
  intro u t hu ht_pos ht_le
  have hu_mem : x + s • u ∈ interior domf := hu
  have ha_nonneg : 0 ≤ 1 - t / s := by
    have hs_ne : s ≠ 0 := ne_of_gt hs_pos
    field_simp [hs_ne]
    linarith
  have hb_pos : 0 < t / s := by
    exact div_pos ht_pos hs_pos
  have hab : 1 - t / s + t / s = 1 := by ring
  have hshort_mem :
      (1 - t / s) • x + (t / s) • (x + s • u) ∈ interior domf :=
    hdomf_conv.combo_self_interior_mem_interior hx hu_mem ha_nonneg hb_pos hab
  have hrewrite :
      (1 - t / s) • x + (t / s) • (x + s • u) = x + t • u := by
    ext i
    have hs_ne : s ≠ 0 := ne_of_gt hs_pos
    simp
    field_simp [hs_ne]
    ring
  have hint : x + t • u ∈ interior domf := by
    exact hrewrite ▸ hshort_mem
  have hfinite_top : f (x + t • u) ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set _)) (f := f) (interior_subset hint)
  have hfinite_bot : f (x + t • u) ≠ (⊥ : EReal) := hproper.2.2 (x + t • u) (by simp)
  exact ⟨hint, hfinite_top, hfinite_bot⟩

/-- Helper for Theorem 5.24.9: after passing to a tail, the normalized secant directions stay in
the fixed ray-neighborhood and the secant lengths are bounded above by the chosen scale. -/
lemma helperForTheorem_5_24_9_eventually_mem_rayNeighborhood_and_le_scale
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x y : Fin n → ℝ}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    {s : ℝ} (hs_pos : 0 < s)
    (hsy_mem :
      x + s • y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (tSeq : ℕ → ℝ) (uSeq : ℕ → Fin n → ℝ)
    (ht_tendsto : Filter.Tendsto tSeq Filter.atTop (nhds 0))
    (hu_tendsto : Filter.Tendsto uSeq Filter.atTop (nhds y)) :
    let C : Set (Fin n → ℝ) :=
      {u : Fin n → ℝ | x + s • u ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)}
    ∃ i0 : ℕ, ∀ i ≥ i0, uSeq i ∈ C ∧ tSeq i ≤ s := by
  let C : Set (Fin n → ℝ) := {u : Fin n → ℝ |
    x + s • u ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)}
  rcases
      helperForTheorem_5_24_9_rayNeighborhood_geometry
        (f := f) hproper hx hs_pos hsy_mem with
    ⟨hC_open, _hC_conv, hy_mem, _hshort⟩
  have hu_eventually : ∀ᶠ i : ℕ in Filter.atTop, uSeq i ∈ C := by
    exact hu_tendsto.eventually (hC_open.mem_nhds hy_mem)
  have ht_eventually : ∀ᶠ i : ℕ in Filter.atTop, tSeq i ≤ s := by
    have ht_lt : ∀ᶠ i : ℕ in Filter.atTop, tSeq i < s := by
      exact ht_tendsto.eventually (Iio_mem_nhds hs_pos)
    exact ht_lt.mono (fun i hi => le_of_lt hi)
  have hboth : ∀ᶠ i : ℕ in Filter.atTop, uSeq i ∈ C ∧ tSeq i ≤ s :=
    hu_eventually.and ht_eventually
  rcases Filter.eventually_atTop.mp hboth with ⟨i0, hi0⟩
  exact ⟨i0, hi0⟩

/-- Helper for Theorem 5.24.9: a subgradient at the interior ray point `x + s • u` bounds the
full-step secant quotient from `x` along `u` from above. -/
lemma helperForTheorem_5_24_9_shortRayDifferenceQuotient_lowerBound_of_subgradient
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    {x u : Fin n → ℝ} {s : ℝ}
    {g : Module.Dual ℝ (Fin n → ℝ)}
    (hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (hsFinite : f (x + s • u) ≠ (⊤ : EReal) ∧ f (x + s • u) ≠ (⊥ : EReal))
    (hg : IsSubgradientAt f (x + s • u) g)
    (hs : 0 < s) :
    directionalDifferenceQuotientAt f x u s ≤ ((g u : ℝ) : EReal) := by
  -- Apply the standard subgradient lower bound to the reversed secant based at `x + s • u`.
  have hrev :
      f x ≥ f (x + s • u) + ((g (x - (x + s • u)) : ℝ) : EReal) := hg x
  have hrev_real :
      (f x).toReal ≥ (f (x + s • u)).toReal + g (x - (x + s • u)) := by
    have hx_coe : (((f x).toReal : ℝ) : EReal) = f x :=
      EReal.coe_toReal hxFinite.1 hxFinite.2
    have hs_coe : ((((f (x + s • u)).toReal : ℝ)) : EReal) = f (x + s • u) :=
      EReal.coe_toReal hsFinite.1 hsFinite.2
    rw [← hx_coe, ← hs_coe] at hrev
    exact_mod_cast hrev
  have hquot_real :
      ((f (x + s • u)).toReal - (f x).toReal) / s ≤ g u := by
    have hxsub : x - (x + s • u) = -(s • u) := by
      abel
    rw [hxsub] at hrev_real
    have hlin : g (-(s • u)) = -(s * g u) := by
      simp [smul_eq_mul]
    rw [hlin] at hrev_real
    have hstep : (f (x + s • u)).toReal - (f x).toReal ≤ s * g u := by
      linarith
    have hs_ne : s ≠ 0 := ne_of_gt hs
    field_simp [hs_ne]
    linarith
  have hquot :
      directionalDifferenceQuotientAt f x u s =
        ((((f (x + s • u)).toReal - (f x).toReal) / s : ℝ) : EReal) := by
    simp [directionalDifferenceQuotientAt, EReal.coe_div, EReal.coe_sub,
      EReal.coe_toReal hsFinite.1 hsFinite.2, EReal.coe_toReal hxFinite.1 hxFinite.2]
  -- Rewrite the quotient as a real coercion and discharge the bound in `ℝ`.
  rw [hquot]
  exact_mod_cast hquot_real

/-- Helper for Theorem 5.24.9: for a positive step, the secant quotient is convex as a function
of the direction variable. -/
lemma helperForTheorem_5_24_9_secantQuotient_convex
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf : ConvexFunction f) {x : Fin n → ℝ}
    (hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    {t : ℝ} (ht : 0 < t) :
    ConvexFunction (fun u => directionalDifferenceQuotientAt f x u t) := by
  have hconvEpigraph :
      Convex ℝ
        (epigraph (Set.univ : Set (Fin n → ℝ)) (fun u => directionalDifferenceQuotientAt f x u t)) := by
    intro p hp q hq a b ha hb hab
    have haeq : a = 1 - b := by
      linarith
    have hb_le_one : b ≤ 1 := by
      linarith
    have hp' : directionalDifferenceQuotientAt f x p.1 t ≤ (p.2 : EReal) := by
      simpa [epigraph] using hp.2
    have hq' : directionalDifferenceQuotientAt f x q.1 t ≤ (q.2 : EReal) := by
      simpa [epigraph] using hq.2
    have hmix :
        directionalDifferenceQuotientAt f x ((1 - b) • p.1 + b • q.1) t ≤
          ((((1 - b) * p.2 + b * q.2 : ℝ)) : EReal) := by
      -- The fixed-step quotient inherits the convex-combination bound from Chapter 23.1.
      exact
        helperForTheorem_23_1_pointwiseDifferenceQuotient_convexCombination_realBound
          f hf x p.1 q.1 hxFinite hb hb_le_one ht hp' hq'
    have hmem :
        (((1 - b) • p.1 + b • q.1), ((1 - b) * p.2 + b * q.2)) ∈
          epigraph (Set.univ : Set (Fin n → ℝ)) (fun u => directionalDifferenceQuotientAt f x u t) := by
      exact
        epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ)))
          (x := (1 - b) • p.1 + b • q.1) (μ := (1 - b) * p.2 + b * q.2) (by simp) hmix
    convert hmem using 1
    ext <;> simp [haeq, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  simpa [ConvexFunction] using hconvEpigraph

/-- Helper for Theorem 5.24.9: finite endpoint values imply the fixed-step secant quotient is
finite. -/
lemma helperForTheorem_5_24_9_secantQuotient_finite
    {n : ℕ} {f : (Fin n → ℝ) → EReal} {x u : Fin n → ℝ} {t : ℝ}
    (hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (huFinite : f (x + t • u) ≠ (⊤ : EReal) ∧ f (x + t • u) ≠ (⊥ : EReal))
    (ht : 0 < t) :
    directionalDifferenceQuotientAt f x u t ≠ (⊤ : EReal) ∧
      directionalDifferenceQuotientAt f x u t ≠ (⊥ : EReal) := by
  let A : ℝ := (f (x + t • u)).toReal
  let B : ℝ := (f x).toReal
  have hrepr : directionalDifferenceQuotientAt f x u t = ((((A - B) / t : ℝ)) : EReal) := by
    simp [A, B, directionalDifferenceQuotientAt, EReal.coe_div, EReal.coe_sub,
      EReal.coe_toReal huFinite.1 huFinite.2, EReal.coe_toReal hxFinite.1 hxFinite.2]
  rw [hrepr]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

/-- Helper for Theorem 5.24.9: on the ray-neighborhood `C`, the limit function
`u ↦ f'(x; u)` is finite. -/
lemma helperForTheorem_5_24_9_limitFunction_finite_on_rayNeighborhood
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x : Fin n → ℝ} (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    {s : ℝ} (hs_pos : 0 < s)
    {C : Set (Fin n → ℝ)}
    {y : Fin n → ℝ} (hy_mem : y ∈ C)
    (hyFinite : upperDirectionalDerivativeAt f x y ≠ (⊥ : EReal))
    (hshort_mem :
      ∀ {u : Fin n → ℝ} {t : ℝ}, u ∈ C → 0 < t → t ≤ s →
        x + t • u ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
          f (x + t • u) ≠ (⊤ : EReal) ∧
          f (x + t • u) ≠ (⊥ : EReal)) :
    ∀ u ∈ C, upperDirectionalDerivativeAt f x u ≠ (⊤ : EReal) ∧
      upperDirectionalDerivativeAt f x u ≠ (⊥ : EReal) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := by
    refine ⟨?_, ?_⟩
    · exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set _)) (f := f) hx
    · exact hproper.2.2 x (by simp)
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite with
    ⟨hdir, hposD, _hconvD, _hzeroD, _hsymmD⟩
  have hyStep := hshort_mem hy_mem hs_pos le_rfl
  have hyRi :
      x + s • y ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    exact helperForTheorem_23_4_mem_relativeInterior_of_mem_interior hyStep.1
  have hsub : Set.Nonempty (subdifferentialAt f x) := by
    by_contra hsubEmpty
    have h23_3 :=
      proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
        f hf x hxFinite
    have hbot_sy : upperDirectionalDerivativeAt f x (s • y) = (⊥ : EReal) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (((h23_3.2 hsubEmpty).2 (x + s • y) hyRi).1)
    have hscale :
        upperDirectionalDerivativeAt f x (s • y) =
          ((s : ℝ) : EReal) * upperDirectionalDerivativeAt f x y := by
      simpa [D] using hposD y s hs_pos
    have hscaled_ne_bot : upperDirectionalDerivativeAt f x (s • y) ≠ (⊥ : EReal) := by
      rw [hscale]
      exact ereal_mul_ne_bot_of_pos hs_pos hyFinite
    exact hscaled_ne_bot hbot_sy
  have hDproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) D :=
    helperForTheorem_23_4_upperDirectionalDerivative_proper_of_subdifferentiable
      f hproper x hsub
  intro u hu
  have huStep := hshort_mem hu hs_pos le_rfl
  have hquotFinite :
      directionalDifferenceQuotientAt f x u s ≠ (⊤ : EReal) ∧
        directionalDifferenceQuotientAt f x u s ≠ (⊥ : EReal) :=
    helperForTheorem_5_24_9_secantQuotient_finite
      (f := f) (x := x) (u := u) hxFinite ⟨huStep.2.1, huStep.2.2⟩ hs_pos
  have htop : D u ≠ (⊤ : EReal) := by
    intro huTop
    rcases hdir u with ⟨_hmono, _htend, hsInfEq⟩
    have hQbdd :
        BddBelow ((Set.Ioi (0 : ℝ)).image fun t : ℝ =>
          directionalDifferenceQuotientAt f x u t) := by
      refine ⟨⊥, ?_⟩
      intro q hq
      simp at hq ⊢
    have hle : D u ≤ directionalDifferenceQuotientAt f x u s := by
      simpa [D] using
        (show upperDirectionalDerivativeAt f x u ≤ directionalDifferenceQuotientAt f x u s by
          rw [hsInfEq]
          exact csInf_le hQbdd ⟨s, hs_pos, rfl⟩)
    have htop_le : (⊤ : EReal) ≤ directionalDifferenceQuotientAt f x u s := by
      simpa [D, huTop] using hle
    exact hquotFinite.1 (top_le_iff.mp htop_le)
  have hbot : D u ≠ (⊥ : EReal) := hDproper.2.2 u (by simp)
  exact ⟨by simpa [D] using htop, by simpa [D] using hbot⟩

/-- Helper for Theorem 5.24.9: the shifted secant-quotient family
`gTail i u = directionalDifferenceQuotientAt f x u (tSeq (i + i0))` satisfies the hypotheses
needed to apply Theorem 5.24.8 on the fixed ray-neighborhood `C`. -/
lemma helperForTheorem_5_24_9_secantQuotient_tailHypotheses
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x : Fin n → ℝ} (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    {s : ℝ} (hs_pos : 0 < s)
    {C : Set (Fin n → ℝ)}
    (hshort_mem :
      ∀ {u : Fin n → ℝ} {t : ℝ}, u ∈ C → 0 < t → t ≤ s →
        x + t • u ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
          f (x + t • u) ≠ (⊤ : EReal) ∧
          f (x + t • u) ≠ (⊥ : EReal))
    {tSeq : ℕ → ℝ} {uSeq : ℕ → Fin n → ℝ} {i0 : ℕ}
    (ht_pos : ∀ i : ℕ, 0 < tSeq i)
    (ht_tail : ∀ i ≥ i0, tSeq i ≤ s)
    (hu_tail : ∀ i ≥ i0, uSeq i ∈ C)
    (ht_tendsto : Filter.Tendsto tSeq Filter.atTop (nhds 0))
    {gTail : ℕ → (Fin n → ℝ) → EReal}
    (hgTail :
      gTail = fun i u => directionalDifferenceQuotientAt f x u (tSeq (i + i0))) :
    (∀ i, ConvexFunction (gTail i)) ∧
      (∀ i u, u ∈ C → gTail i u ≠ (⊤ : EReal) ∧ gTail i u ≠ (⊥ : EReal)) ∧
      (∀ u ∈ C,
        Filter.Tendsto (fun i => gTail i u) Filter.atTop
          (nhds (upperDirectionalDerivativeAt f x u))) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := by
    refine ⟨?_, ?_⟩
    · exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set _)) (f := f) hx
    · exact hproper.2.2 x (by simp)
  constructor
  · intro i
    -- Each fixed-step quotient is convex because it is a positive rescaling of a translated
    -- convex function.
    rw [hgTail]
    exact
      helperForTheorem_5_24_9_secantQuotient_convex
        (f := f) hproper hf hxFinite (ht_pos (i + i0))
  constructor
  · intro i u hu
    -- The ray-neighborhood geometry keeps the translated endpoint finite, so the quotient is
    -- finite as well.
    rw [hgTail]
    have hstep :=
      hshort_mem hu (ht_pos (i + i0)) (ht_tail (i + i0) (Nat.le_add_left i0 i))
    exact
      helperForTheorem_5_24_9_secantQuotient_finite
        (f := f) (x := x) (u := u) hxFinite ⟨hstep.2.1, hstep.2.2⟩ (ht_pos (i + i0))
  · intro u hu
    -- Compose the right-limit description of `f'(x; u)` with the positive tail of step sizes.
    rw [hgTail]
    have hmono : MonotoneOn (directionalDifferenceQuotientAt f x u) (Set.Ioi (0 : ℝ)) :=
      (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite).1 u |>.1
    have htailPos :
        Filter.Tendsto (fun i : ℕ => tSeq (i + i0)) Filter.atTop
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        (f := fun i : ℕ => tSeq (i + i0)) ?_ ?_
      · exact ht_tendsto.comp (Filter.tendsto_add_atTop_nat i0)
      · filter_upwards [Filter.Eventually.of_forall (fun i => ht_pos (i + i0))] with i hi
        simpa using hi
    exact (helperForTheorem_23_1_tendsto_upperDerivative f x u hmono).comp htailPos

/-- Helper for Theorem 5.24.9: translating the secant endpoint along `u + λ z` is the same as
first stepping to `x + t • u` and then moving by `(t * λ) • z`. -/
lemma helperForTheorem_5_24_9_translatedSecantEndpoint
    {n : ℕ} {x u z : Fin n → ℝ} {t lam : ℝ} :
    x + t • (u + lam • z) = (x + t • u) + (t * lam) • z := by
  -- Expand the scalar multiplication coordinatewise and collect the `t * lam` term.
  ext i
  simp [smul_add, smul_smul, mul_assoc, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 5.24.9: after subtracting the same finite real base value, the nested
positive-step secant quotient collapses to the single quotient with denominator `t * λ`. -/
lemma helperForTheorem_5_24_9_positiveDenominator_ereal_sub_div_cancel_of_finiteBase
    (A C : EReal) (β t lam : ℝ) (ht : 0 < t) (hlam : 0 < lam) :
    ((((A - ((β : ℝ) : EReal)) / (t : EReal)) - ((C - ((β : ℝ) : EReal)) / (t : EReal))) /
        (lam : EReal)) =
      ((A - C) / (((t * lam : ℝ)) : EReal)) := by
  cases A using EReal.rec with
  | bot =>
      cases C using EReal.rec with
      | bot =>
          -- Both inner secant quotients are `⊥`, so every positive rescaling stays at `⊥`.
          rw [EReal.div_eq_inv_mul, EReal.div_eq_inv_mul, EReal.div_eq_inv_mul]
          rw [← EReal.coe_inv t, ← EReal.coe_inv lam, ← EReal.coe_inv (t * lam)]
          have htinv : 0 < t⁻¹ := inv_pos.2 ht
          have hlaminv : 0 < lam⁻¹ := inv_pos.2 hlam
          simp [mul_assoc, sub_eq_add_neg, EReal.coe_mul_bot_of_pos htinv,
            EReal.coe_mul_bot_of_pos hlaminv]
      | coe c =>
          -- The left branch collapses to `⊥` before the outer quotient, and the right branch does
          -- the same because `⊥ - c = ⊥`.
          have htinv : 0 < t⁻¹ := inv_pos.2 ht
          have hlaminv : 0 < lam⁻¹ := inv_pos.2 hlam
          have hprodinv : 0 < (t * lam)⁻¹ := inv_pos.2 (mul_pos ht hlam)
          have hleft :
              ((((⊥ : EReal) - ((β : ℝ) : EReal)) / (t : EReal)) -
                    (((c : EReal) - ((β : ℝ) : EReal)) / (t : EReal))) /
                  (lam : EReal) =
                (⊥ : EReal) := by
            rw [EReal.div_eq_inv_mul, EReal.div_eq_inv_mul, ← EReal.coe_inv t,
              ← EReal.coe_inv lam]
            rw [show ((⊥ : EReal) - ((β : ℝ) : EReal)) = (⊥ : EReal) by
              simp [sub_eq_add_neg]]
            simp [sub_eq_add_neg, mul_assoc, EReal.coe_mul_bot_of_pos ht,
              EReal.coe_mul_bot_of_pos htinv, EReal.coe_mul_bot_of_pos hlaminv]
          have hright :
              (((⊥ : EReal) - (c : EReal)) / (((t * lam : ℝ)) : EReal)) = (⊥ : EReal) := by
            rw [show ((⊥ : EReal) - (c : EReal)) = (⊥ : EReal) by simp [sub_eq_add_neg]]
            rw [EReal.div_eq_inv_mul, ← EReal.coe_inv (t * lam)]
            simpa using EReal.coe_mul_bot_of_pos hprodinv
          rw [hleft, hright]
      | top =>
          -- Here the left numerator is `⊥ - ⊤ = ⊥`, so again both sides collapse to `⊥`.
          have htinv : 0 < t⁻¹ := inv_pos.2 ht
          have hlaminv : 0 < lam⁻¹ := inv_pos.2 hlam
          have hleftBot :
              (((⊥ : EReal) - ((β : ℝ) : EReal)) / (t : EReal)) = (⊥ : EReal) := by
            rw [EReal.div_eq_inv_mul, ← EReal.coe_inv t]
            rw [show ((⊥ : EReal) - ((β : ℝ) : EReal)) = (⊥ : EReal) by
              simp [sub_eq_add_neg]]
            simpa using EReal.coe_mul_bot_of_pos htinv
          have hleftTop :
              (((⊤ : EReal) - ((β : ℝ) : EReal)) / (t : EReal)) = (⊤ : EReal) := by
            rw [EReal.div_eq_inv_mul, ← EReal.coe_inv t]
            simp [sub_eq_add_neg, EReal.coe_mul_top_of_pos htinv]
          have hrightBot :
              (((⊥ : EReal) - (⊤ : EReal)) / (((t * lam : ℝ)) : EReal)) = (⊥ : EReal) := by
            rw [show ((⊥ : EReal) - (⊤ : EReal)) = (⊥ : EReal) by simp [sub_eq_add_neg]]
            rw [EReal.div_eq_inv_mul, ← EReal.coe_inv (t * lam)]
            simpa using EReal.coe_mul_bot_of_pos (inv_pos.2 (mul_pos ht hlam))
          rw [hleftBot, hleftTop, hrightBot]
          rw [EReal.div_eq_inv_mul, ← EReal.coe_inv lam]
          rw [show ((⊥ : EReal) - (⊤ : EReal)) = (⊥ : EReal) by simp [sub_eq_add_neg]]
          simpa using EReal.coe_mul_bot_of_pos hlaminv
  | coe a =>
      cases C using EReal.rec with
      | bot =>
          -- Subtracting `⊥` produces `⊤`, so the outer quotient stays at `⊤` on both sides.
          have htinv : 0 < t⁻¹ := inv_pos.2 ht
          have hlaminv : 0 < lam⁻¹ := inv_pos.2 hlam
          have hleftFinite :
              (((a : EReal) - ((β : ℝ) : EReal)) / (t : EReal)) =
                ((((a - β) / t : ℝ)) : EReal) := by
            simp [EReal.coe_div, EReal.coe_sub]
          have hleftBot :
              (((⊥ : EReal) - ((β : ℝ) : EReal)) / (t : EReal)) = (⊥ : EReal) := by
            rw [EReal.div_eq_inv_mul, ← EReal.coe_inv t]
            rw [show ((⊥ : EReal) - ((β : ℝ) : EReal)) = (⊥ : EReal) by
              simp [sub_eq_add_neg]]
            simpa using EReal.coe_mul_bot_of_pos htinv
          have hrightTop :
              (((a : EReal) - (⊥ : EReal)) / (((t * lam : ℝ)) : EReal)) = (⊤ : EReal) := by
            rw [show ((a : EReal) - (⊥ : EReal) = (⊤ : EReal)) by simp [sub_eq_add_neg]]
            exact
              EReal.top_div_of_pos_ne_top (by exact_mod_cast mul_pos ht hlam) (EReal.coe_ne_top _)
          rw [hleftFinite, hleftBot, hrightTop]
          rw [EReal.div_eq_inv_mul, ← EReal.coe_inv lam]
          rw [show ((((a - β) / t : ℝ)) : EReal) - (⊥ : EReal) = (⊤ : EReal) by
            simp [sub_eq_add_neg]]
          simpa using EReal.coe_mul_top_of_pos hlaminv
      | coe c =>
          -- In the fully finite branch, the identity is just ordinary real algebra.
          change (((((a - β) / t) - ((c - β) / t)) / lam : ℝ) : EReal) =
            (((a - c) / (t * lam) : ℝ) : EReal)
          congr 1
          field_simp [ht.ne', hlam.ne']
          ring
      | top =>
          -- Subtracting `⊤` forces the result to `⊥` before the outer positive scaling.
          have htinv : 0 < t⁻¹ := inv_pos.2 ht
          have hlaminv : 0 < lam⁻¹ := inv_pos.2 hlam
          have hleftFinite :
              (((a : EReal) - ((β : ℝ) : EReal)) / (t : EReal)) =
                ((((a - β) / t : ℝ)) : EReal) := by
            simp [EReal.coe_div, EReal.coe_sub]
          have hleftTop :
              (((⊤ : EReal) - ((β : ℝ) : EReal)) / (t : EReal)) = (⊤ : EReal) := by
            rw [EReal.div_eq_inv_mul, ← EReal.coe_inv t]
            simp [sub_eq_add_neg, EReal.coe_mul_top_of_pos htinv]
          have hrightBot :
              (((a : EReal) - (⊤ : EReal)) / (((t * lam : ℝ)) : EReal)) = (⊥ : EReal) := by
            rw [show ((a : EReal) - (⊤ : EReal) = (⊥ : EReal)) by simp [sub_eq_add_neg]]
            rw [EReal.div_eq_inv_mul, ← EReal.coe_inv (t * lam)]
            simpa using EReal.coe_mul_bot_of_pos (inv_pos.2 (mul_pos ht hlam))
          rw [hleftFinite, hleftTop, hrightBot]
          rw [EReal.div_eq_inv_mul, ← EReal.coe_inv lam]
          rw [show ((((a - β) / t : ℝ)) : EReal) - (⊤ : EReal) = (⊥ : EReal) by
            simp [sub_eq_add_neg]]
          simpa using EReal.coe_mul_bot_of_pos hlaminv
  | top =>
      cases C using EReal.rec with
      | bot =>
          -- The left side is `⊤ - ⊥ = ⊤`, so the outer quotient stays `⊤`, matching the right.
          have htinv : 0 < t⁻¹ := inv_pos.2 ht
          have hlaminv : 0 < lam⁻¹ := inv_pos.2 hlam
          have hleftTop :
              (((⊤ : EReal) - ((β : ℝ) : EReal)) / (t : EReal)) = (⊤ : EReal) := by
            rw [EReal.div_eq_inv_mul, ← EReal.coe_inv t]
            simp [sub_eq_add_neg, EReal.coe_mul_top_of_pos htinv]
          have hleftBot :
              (((⊥ : EReal) - ((β : ℝ) : EReal)) / (t : EReal)) = (⊥ : EReal) := by
            rw [EReal.div_eq_inv_mul, ← EReal.coe_inv t]
            rw [show ((⊥ : EReal) - ((β : ℝ) : EReal)) = (⊥ : EReal) by
              simp [sub_eq_add_neg]]
            simpa using EReal.coe_mul_bot_of_pos htinv
          have hrightTop :
              (((⊤ : EReal) - (⊥ : EReal)) / (((t * lam : ℝ)) : EReal)) = (⊤ : EReal) := by
            rw [show ((⊤ : EReal) - (⊥ : EReal) = (⊤ : EReal)) by simp [sub_eq_add_neg]]
            exact
              EReal.top_div_of_pos_ne_top (by exact_mod_cast mul_pos ht hlam) (EReal.coe_ne_top _)
          rw [hleftTop, hleftBot, hrightTop]
          rw [EReal.div_eq_inv_mul, ← EReal.coe_inv lam]
          simpa using EReal.coe_mul_top_of_pos hlaminv
      | coe c =>
          -- After rewriting the finite quotient as a real coercion, `⊤ - q` is still `⊤`.
          have htinv : 0 < t⁻¹ := inv_pos.2 ht
          have hlaminv : 0 < lam⁻¹ := inv_pos.2 hlam
          have hleftTop :
              (((⊤ : EReal) - ((β : ℝ) : EReal)) / (t : EReal)) = (⊤ : EReal) := by
            rw [EReal.div_eq_inv_mul, ← EReal.coe_inv t]
            simp [sub_eq_add_neg, EReal.coe_mul_top_of_pos htinv]
          have hrightTop :
              (((⊤ : EReal) - (c : EReal)) / (((t * lam : ℝ)) : EReal)) = (⊤ : EReal) := by
            exact
              EReal.top_div_of_pos_ne_top (by exact_mod_cast mul_pos ht hlam) (EReal.coe_ne_top _)
          rw [hleftTop, hrightTop]
          rw [EReal.div_eq_inv_mul, ← EReal.coe_inv lam]
          have hquot :
              (((c : EReal) - ((β : ℝ) : EReal)) / (t : EReal)) =
                ((((c - β) / t : ℝ)) : EReal) := by
            simp [EReal.coe_div, EReal.coe_sub]
          rw [hquot]
          rw [show (⊤ : EReal) - ((((c - β) / t : ℝ)) : EReal) = (⊤ : EReal) by
            simpa [sub_eq_add_neg] using EReal.top_add_coe (-((c - β) / t))]
          simpa using EReal.coe_mul_top_of_pos hlaminv
      | top =>
          -- When both branches are `⊤`, their difference is `⊥`, and positive scaling preserves
          -- that value.
          rw [EReal.div_eq_inv_mul, EReal.div_eq_inv_mul, EReal.div_eq_inv_mul]
          rw [← EReal.coe_inv t, ← EReal.coe_inv lam, ← EReal.coe_inv (t * lam)]
          have htinv : 0 < t⁻¹ := inv_pos.2 ht
          have hlaminv : 0 < lam⁻¹ := inv_pos.2 hlam
          have hsubAdd : (⊤ : EReal) + -((β : EReal)) = (⊤ : EReal) := by
            simp [sub_eq_add_neg]
          have htTop : (((t⁻¹ : ℝ)) : EReal) * (⊤ : EReal) = (⊤ : EReal) := by
            simpa using EReal.coe_mul_top_of_pos htinv
          rw [show (⊤ : EReal) - ((β : ℝ) : EReal) = (⊤ : EReal) by
            simpa [sub_eq_add_neg] using hsubAdd]
          rw [htTop]
          rw [show (⊤ : EReal) - (⊤ : EReal) = (⊥ : EReal) by simp [sub_eq_add_neg]]
          rw [show (((lam⁻¹ : ℝ)) : EReal) * (⊥ : EReal) = (⊥ : EReal) by
            simpa using EReal.coe_mul_bot_of_pos hlaminv]
          simpa using (EReal.coe_mul_bot_of_pos (inv_pos.2 (mul_pos ht hlam))).symm

/-- Helper for Theorem 5.24.9: the positive-step quotient of the fixed-step secant quotient is
the corresponding positive-step quotient of `f` at the translated base point. -/
lemma helperForTheorem_5_24_9_secantQuotient_pointwiseDifferenceQuotient_transport
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    {x u z : Fin n → ℝ} {t lam : ℝ}
    (hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (ht : 0 < t) (hlam : 0 < lam) :
    directionalDifferenceQuotientAt (fun v => directionalDifferenceQuotientAt f x v t) u z lam =
      directionalDifferenceQuotientAt f (x + t • u) z (t * lam) := by
  let β : ℝ := (f x).toReal
  have hxCoe : (((β : ℝ)) : EReal) = f x := EReal.coe_toReal hxFinite.1 hxFinite.2
  -- Unfold the nested quotients and rewrite the translated endpoint into the textbook form.
  rw [directionalDifferenceQuotientAt, directionalDifferenceQuotientAt, directionalDifferenceQuotientAt,
    directionalDifferenceQuotientAt]
  rw [helperForTheorem_5_24_9_translatedSecantEndpoint]
  rw [← hxCoe]
  -- With the common finite base value `f x = β`, the remaining identity is the scalar `EReal`
  -- normalization proved in the previous helper.
  exact
    helperForTheorem_5_24_9_positiveDenominator_ereal_sub_div_cancel_of_finiteBase
      (A := f (x + t • u + (t * lam) • z)) (C := f (x + t • u)) β t lam ht hlam

/-- Helper for Theorem 5.24.9: differentiating the fixed-step secant quotient at `u` recovers the
directional derivative of `f` at the translated point `x + t • u`. -/
lemma helperForTheorem_5_24_9_secantQuotient_derivative_transport
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf : ConvexFunction f)
    {x u z : Fin n → ℝ} {t : ℝ}
    (hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (huFinite : f (x + t • u) ≠ (⊤ : EReal) ∧ f (x + t • u) ≠ (⊥ : EReal))
    (ht : 0 < t) :
    upperDirectionalDerivativeAt (fun v => directionalDifferenceQuotientAt f x v t) u z =
      upperDirectionalDerivativeAt f (x + t • u) z := by
  let g : (Fin n → ℝ) → EReal := fun v => directionalDifferenceQuotientAt f x v t
  have hgConv : ConvexFunction g := by
    -- The fixed-step secant quotient is convex in the direction variable.
    exact helperForTheorem_5_24_9_secantQuotient_convex (f := f) hproper hf hxFinite ht
  have hguFinite : g u ≠ (⊤ : EReal) ∧ g u ≠ (⊥ : EReal) := by
    -- Finiteness at `x` and `x + t • u` gives finiteness of the quotient at `u`.
    simpa [g] using
      (helperForTheorem_5_24_9_secantQuotient_finite (f := f) (x := x) (u := u) hxFinite huFinite
        ht)
  rcases convex_directionalDerivative_monotone_exists_and_sublinear g hgConv u hguFinite with
    ⟨hdirG, _hposG, _hconvG, _hzeroG, _hsymmG⟩
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf (x + t • u) huFinite with
    ⟨hdirF, _hposF, _hconvF, _hzeroF, _hsymmF⟩
  have hleft :
      Filter.Tendsto (directionalDifferenceQuotientAt g u z) (𝓝[>] (0 : ℝ))
        (𝓝 (upperDirectionalDerivativeAt g u z)) :=
    helperForTheorem_23_1_tendsto_upperDerivative g u z (hdirG z).1
  have hscale :
      Filter.Tendsto (fun lam : ℝ => t * lam) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    -- Positive rescaling preserves the right-neighborhood filter at `0`.
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (f := fun lam : ℝ => t * lam) ?_
      ?_
    · simpa using
        ((show ContinuousWithinAt (fun lam : ℝ => t * lam) (Set.Ioi (0 : ℝ)) 0 by fun_prop).tendsto)
    · filter_upwards [self_mem_nhdsWithin] with lam hlam
      exact mul_pos ht hlam
  have hright :
      Filter.Tendsto (fun lam : ℝ => directionalDifferenceQuotientAt f (x + t • u) z (t * lam))
        (𝓝[>] (0 : ℝ)) (𝓝 (upperDirectionalDerivativeAt f (x + t • u) z)) :=
    (helperForTheorem_23_1_tendsto_upperDerivative f (x + t • u) z (hdirF z).1).comp hscale
  have heq :
      directionalDifferenceQuotientAt g u z =ᶠ[𝓝[>] (0 : ℝ)]
        fun lam : ℝ => directionalDifferenceQuotientAt f (x + t • u) z (t * lam) := by
    -- The two quotient families agree pointwise on the positive ray.
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    simpa [g] using
      helperForTheorem_5_24_9_secantQuotient_pointwiseDifferenceQuotient_transport
        (f := f) (x := x) (u := u) (z := z) (t := t) (lam := lam) hxFinite ht hlam
  -- Uniqueness of limits on the right ray identifies the two derivative values.
  exact tendsto_nhds_unique_of_eventuallyEq hleft hright heq

/-- Helper for Theorem 5.24.9: the Euclideanized subdifferential of the fixed-step secant
quotient at `u` is exactly the Euclideanized subdifferential of `f` at `x + t • u`. -/
lemma helperForTheorem_5_24_9_secantQuotient_subdifferential_transport
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf : ConvexFunction f)
    {x u : Fin n → ℝ} {t : ℝ}
    (hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (huFinite : f (x + t • u) ≠ (⊤ : EReal) ∧ f (x + t • u) ≠ (⊥ : EReal))
    (ht : 0 < t) :
    ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt
        (fun v => directionalDifferenceQuotientAt f x v t) u) =
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f (x + t • u)) := by
  ext v
  constructor <;> intro hv
  · have hv' :
        dotProductEquiv ℝ (Fin n) v ∈
          subdifferentialAt (fun w => directionalDifferenceQuotientAt f x w t) u := hv
    rw [helperForTheorem_23_2_subgradient_iff_vector_linear_minorant
      (f := fun w => directionalDifferenceQuotientAt f x w t)
      (hf := helperForTheorem_5_24_9_secantQuotient_convex (f := f) hproper hf hxFinite ht)
      (x := u)
      (hx := helperForTheorem_5_24_9_secantQuotient_finite (f := f) (x := x) (u := u) hxFinite
        huFinite ht)
      (v := v)] at hv'
    change dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt f (x + t • u)
    rw [helperForTheorem_23_2_subgradient_iff_vector_linear_minorant
      (f := f) (hf := hf) (x := x + t • u) (hx := huFinite) (v := v)]
    intro z
    simpa [helperForTheorem_5_24_9_secantQuotient_derivative_transport
      (f := f) hproper hf (x := x) (u := u) (z := z) (t := t) hxFinite huFinite ht] using hv' z
  · have hv' : dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt f (x + t • u) := hv
    rw [helperForTheorem_23_2_subgradient_iff_vector_linear_minorant
      (f := f) (hf := hf) (x := x + t • u) (hx := huFinite) (v := v)] at hv'
    change dotProductEquiv ℝ (Fin n) v ∈
      subdifferentialAt (fun w => directionalDifferenceQuotientAt f x w t) u
    rw [helperForTheorem_23_2_subgradient_iff_vector_linear_minorant
      (f := fun w => directionalDifferenceQuotientAt f x w t)
      (hf := helperForTheorem_5_24_9_secantQuotient_convex (f := f) hproper hf hxFinite ht)
      (x := u)
      (hx := helperForTheorem_5_24_9_secantQuotient_finite (f := f) (x := x) (u := u) hxFinite
        huFinite ht)
      (v := v)]
    intro z
    simpa [helperForTheorem_5_24_9_secantQuotient_derivative_transport
      (f := f) hproper hf (x := x) (u := u) (z := z) (t := t) hxFinite huFinite ht] using hv' z

/-- Helper for Theorem 5.24.9: every subgradient of the iterated upper directional derivative at
`y` is already a subgradient of `f` at `x`, and it realizes the support value at `y`. -/
lemma helperForTheorem_5_24_9_iteratedSubgradient_mem_subdifferential_and_supportEq
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x y v : Fin n → ℝ}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    (hfiniteDir : upperDirectionalDerivativeAt f x y ≠ (⊥ : EReal))
    (hv :
      v ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹'
        subdifferentialAt (upperDirectionalDerivativeAt f x) y)) :
    dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt f x ∧
      (((dotProduct v y : ℝ) : EReal) = upperDirectionalDerivativeAt f x y) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := by
    refine ⟨?_, ?_⟩
    · exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set _)) (f := f) hx
    · exact hproper.2.2 x (by simp)
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite with
    ⟨_hdirD, hposD, _hconvD, hzeroD, _hsymmD⟩
  have hvSub :
      dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt (upperDirectionalDerivativeAt f x) y := hv
  have hAtZero := hvSub 0
  have hAtTwoY := hvSub (2 • y)
  have hfiniteDirTop : upperDirectionalDerivativeAt f x y ≠ (⊤ : EReal) := by
    -- Testing the subgradient inequality at `0` rules out the value `⊤` at `y`.
    intro htop
    have hzeroLe : (⊤ : EReal) ≤ (0 : EReal) := by
      rw [hzeroD, htop, EReal.top_add_coe] at hAtZero
      simpa [dotProductEquiv_apply_apply, dotProduct_comm] using hAtZero
    exact (not_top_le_coe 0 hzeroLe).elim
  let d : ℝ := (upperDirectionalDerivativeAt f x y).toReal
  have hd : ((d : ℝ) : EReal) = upperDirectionalDerivativeAt f x y := by
    simp [d, EReal.coe_toReal, hfiniteDirTop, hfiniteDir]
  have hsupport_le : upperDirectionalDerivativeAt f x y ≤ (((dotProduct v y : ℝ)) : EReal) := by
    -- The inequality at `0` gives `D y ≤ ⟪v, y⟫`.
    have h0 : (((d - dotProduct v y : ℝ)) : EReal) ≤ 0 := by
      rw [← hd] at hAtZero
      simpa [hzeroD, dotProductEquiv_apply_apply, dotProduct_comm, sub_eq_add_neg, EReal.coe_sub]
        using hAtZero
    have h0real : d - dotProduct v y ≤ 0 := by
      exact_mod_cast h0
    have : d ≤ dotProduct v y := by
      linarith
    rw [← hd]
    exact_mod_cast this
  have hsupport_ge : (((dotProduct v y : ℝ)) : EReal) ≤ upperDirectionalDerivativeAt f x y := by
    -- The inequality at `2 • y` gives the reverse bound `⟪v, y⟫ ≤ D y`.
    have h2 : ((((d + dotProduct v y : ℝ)) : EReal)) ≤ (((2 * d : ℝ)) : EReal) := by
      have htwo :
          upperDirectionalDerivativeAt f x (2 • y) =
            (((2 : ℝ) : EReal) * upperDirectionalDerivativeAt f x y) := by
        simpa using hposD y 2 (by norm_num : (0 : ℝ) < 2)
      rw [htwo, ← hd] at hAtTwoY
      simpa [dotProductEquiv_apply_apply, dotProduct_comm, EReal.coe_add, EReal.coe_mul,
        add_comm, add_left_comm, add_assoc, two_smul] using hAtTwoY
    have h2real : d + dotProduct v y ≤ 2 * d := by
      exact_mod_cast h2
    have : dotProduct v y ≤ d := by
      linarith
    rw [← hd]
    exact_mod_cast this
  have hsupportEq :
      (((dotProduct v y : ℝ) : EReal) = upperDirectionalDerivativeAt f x y) :=
    le_antisymm hsupport_ge hsupport_le
  have hminorantD :
      ∀ z : Fin n → ℝ, (((dotProduct z v : ℝ)) : EReal) ≤ upperDirectionalDerivativeAt f x z := by
    intro z
    -- Replace the base value `D y` in the subgradient inequality by the support equality.
    have hz :
        (((dotProduct y v : ℝ)) : EReal) + (((dotProduct (z - y) v : ℝ)) : EReal) ≤
          upperDirectionalDerivativeAt f x z := by
      have hz0 :
          upperDirectionalDerivativeAt f x y + (((dotProduct (z - y) v : ℝ)) : EReal) ≤
            upperDirectionalDerivativeAt f x z := by
        simpa [dotProductEquiv_apply_apply, dotProduct_comm] using hvSub z
      rw [← hsupportEq] at hz0
      simpa [dotProduct_comm] using hz0
    have hdotSplit :
        ((dotProduct z v : ℝ) : EReal) =
          (((dotProduct y v : ℝ)) : EReal) + (((dotProduct (z - y) v : ℝ)) : EReal) := by
      -- Expand `⟪z, v⟫` as `⟪y, v⟫ + ⟪z - y, v⟫`.
      calc
        ((dotProduct z v : ℝ) : EReal) =
            (((dotProduct y v + dotProduct (z - y) v : ℝ)) : EReal) := by
              congr 1
              have hsplit : dotProduct (z - y) v = dotProduct z v - dotProduct y v := by
                unfold dotProduct
                have hterm : ∀ i, (z - y) i * v i = z i * v i - y i * v i := by
                  intro i
                  simp [sub_eq_add_neg]
                  ring
                simp_rw [hterm]
                rw [Finset.sum_sub_distrib]
              linarith
        _ = (((dotProduct y v : ℝ)) : EReal) + (((dotProduct (z - y) v : ℝ)) : EReal) := by
              rw [EReal.coe_add]
    exact hdotSplit ▸ hz
  -- Theorem 23.2 converts the global minorant property for `D` into subgradient membership for `f`.
  exact
    ⟨(helperForTheorem_23_2_subgradient_iff_vector_linear_minorant
        f hf x hxFinite v).2 hminorantD,
      hsupportEq⟩

end Section24
end Chap05
