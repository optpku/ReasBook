/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory Measure Filter Set
open scoped Topology CompactlySupported unitInterval

variable {E : Type u}

noncomputable section

/-- The family `Lip₁(E; [0,1])` of `[0,1]`-valued real functions on `E` with Lipschitz constant
at most `1`. -/
def unitIntervalLipschitzRealFunctionSpace (E : Type u) [MetricSpace E] : Set (E → ℝ) :=
  {f | LipschitzWith 1 f ∧ MapsTo f univ (Set.Icc (0 : ℝ) 1)}

/-- The family `C_c(E) ∩ Lip₁(E; [0,1])` inside the canonical owner type `C_c(E, ℝ)`. -/
def compactlySupportedUnitIntervalLipschitzRealMapSpace (E : Type u) [MetricSpace E] :
    Set (C_c(E, ℝ)) :=
  {f | LipschitzWith 1 f ∧ MapsTo f univ (Set.Icc (0 : ℝ) 1)}

/-- Helper for Theorem 13.11: two inner regular measures are equal once they agree on every
compact set. -/
lemma measure_eq_of_forall_isCompact [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ ν : Measure E} [InnerRegular μ] [InnerRegular ν]
    (hK : ∀ ⦃K : Set E⦄, IsCompact K → μ K = ν K) :
    μ = ν := by
  -- Compare any measurable set by exhausting it from inside with compact subsets.
  ext A hA
  rw [hA.measure_eq_iSup_isCompact μ, hA.measure_eq_iSup_isCompact ν]
  congr! 4 with K hKA hKc
  exact hK hKc

/-- Helper for Theorem 13.11: scaling the thickened indicator of `K` by `ε ≤ 1` produces a test
function in `Lip₁(E; [0,1])`. -/
lemma scaledThickenedIndicator_mem_unitIntervalLipschitz [MetricSpace E]
    {K : Set E} {ε : ℝ} (hε : 0 < ε) (hε_le_one : ε ≤ 1) :
    (fun x : E ↦ ε * (thickenedIndicator hε K x : ℝ)) ∈
      unitIntervalLipschitzRealFunctionSpace E := by
  refine ⟨?_, ?_⟩
  · -- Route correction: keep the Lipschitz proof in real-valued normal form by composing the
    -- coercion `NNReal → ℝ` with scalar multiplication by `ε`.
    have hε_toNNReal_pos : 0 < ε.toNNReal := by
      simpa [Real.toNNReal_of_nonneg hε.le] using hε
    have hbase :
        LipschitzWith ε.toNNReal⁻¹ (fun x : E ↦ (thickenedIndicator hε K x : ℝ)) :=
      by
        simpa using (NNReal.isometry_coe.lipschitz.comp (lipschitzWith_thickenedIndicator hε K))
    have hsmul : LipschitzWith ‖ε‖₊ (fun r : ℝ ↦ ε * r) := by
      simpa using (lipschitzWith_smul (α := ℝ) (β := ℝ) ε)
    have hcomp :
        LipschitzWith (‖ε‖₊ * ε.toNNReal⁻¹)
          (fun x : E ↦ ε * (thickenedIndicator hε K x : ℝ)) := by
      simpa [Function.comp] using hsmul.comp hbase
    have hconst : ‖ε‖₊ * ε.toNNReal⁻¹ = 1 := by
      rw [← Real.toNNReal_eq_nnnorm_of_nonneg hε.le]
      exact mul_inv_cancel₀ hε_toNNReal_pos.ne'
    -- Scaling by `ε` cancels the `ε⁻¹` Lipschitz constant of the cutoff.
    simpa [hconst] using hcomp
  · intro x _
    change
      0 ≤ ε * (thickenedIndicator hε K x : ℝ) ∧
        ε * (thickenedIndicator hε K x : ℝ) ≤ 1
    constructor
    · positivity
    · -- The thickened indicator is bounded by `1`, so the extra factor `ε ≤ 1` preserves the
      -- unit-interval range.
      have hx_le_one : (thickenedIndicator hε K x : ℝ) ≤ (1 : ℝ) := by
        have hNN := thickenedIndicator_le_one hε K x
        exact_mod_cast hNN
      have hmul_le : ε * (thickenedIndicator hε K x : ℝ) ≤ ε * 1 := by
        exact mul_le_mul_of_nonneg_left hx_le_one hε.le
      have hε_mul_one_le_one : ε * (1 : ℝ) ≤ 1 := by
        simpa using hε_le_one
      exact hmul_le.trans hε_mul_one_le_one

/-- Helper for Theorem 13.11: the real-valued scaled thickened indicator vanishes outside the
`ε`-thickening. -/
lemma smul_thickenedIndicator_eq_zero_of_not_mem_thickening [MetricSpace E]
    {K : Set E} {ε : ℝ} (hε : 0 < ε) {x : E} (hx : x ∉ Metric.thickening ε K) :
    ε * (thickenedIndicator hε K x : ℝ) = 0 := by
  -- Outside the thickening the cutoff itself is zero, so the scaled version is also zero.
  simp [thickenedIndicator_zero hε K hx]

/-- Helper for Theorem 13.11: if the `ε`-thickening of `K` stays inside `V` and `closure V` is
compact, then the scaled thickened indicator defines an element of `C_c(E, ℝ)`. -/
lemma compactlySupportedScaledThickenedIndicator [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    {K V : Set E} {ε : ℝ} (hε : 0 < ε)
    (hthick : Metric.thickening ε K ⊆ V) (hVc : IsCompact (closure V)) :
    ∃ g : C_c(E, ℝ), (g : E → ℝ) = fun x : E ↦ ε * (thickenedIndicator hε K x : ℝ) := by
  have hContinuousScaledThickenedIndicator :
      Continuous (fun x : E ↦ ε * (thickenedIndicator hε K x : ℝ)) := by
    -- The cutoff is continuous as a scalar multiple of the bundled continuous indicator.
    exact continuous_const.mul (NNReal.continuous_coe.comp (thickenedIndicator hε K).continuous)
  let f : C(E, ℝ) :=
    ⟨fun x : E ↦ ε * (thickenedIndicator hε K x : ℝ), hContinuousScaledThickenedIndicator⟩
  have hsupport :
      Function.support (fun x : E ↦ ε * (thickenedIndicator hε K x : ℝ)) ⊆ closure V := by
    -- Outside `V` the thickened indicator vanishes because its whole thickening stays in `V`.
    refine Function.support_subset_iff'.2 ?_
    intro x hxV
    have hxV' : x ∉ V := fun hx => hxV (subset_closure hx)
    have hx_not_thick : x ∉ Metric.thickening ε K := by
      intro hx_thick
      exact hxV' (hthick hx_thick)
    -- The support condition is pointwise: outside `closure V` the scaled cutoff is zero.
    exact smul_thickenedIndicator_eq_zero_of_not_mem_thickening (K := K) hε hx_not_thick
  -- The support is contained in the compact set `closure V`, so the continuous map is compactly
  -- supported.
  refine ⟨⟨f, HasCompactSupport.of_support_subset_isCompact hVc hsupport⟩, rfl⟩

/-- Helper for Theorem 13.11: a real-valued function that vanishes off `U` is integrable once its
restriction to `U` is integrable. -/
lemma integrable_of_integrable_restrict_of_eq_zero_off [MeasurableSpace E] {μ : Measure E}
    {U : Set E} (hU_meas : MeasurableSet U) {f : E → ℝ} (hzero : ∀ x ∉ U, f x = 0)
    (hf : Integrable f (μ.restrict U)) :
    Integrable f μ := by
  have hindicator : Integrable (U.indicator f) μ := (integrable_indicator_iff hU_meas).2 hf
  -- Replace the indicator by `f` using the off-support vanishing hypothesis.
  convert hindicator using 1
  ext x
  by_cases hx : x ∈ U
  · simp [Set.indicator, hx]
  · simp [Set.indicator, hx, hzero x hx]

/-- Helper for Theorem 13.11: a real-valued function that vanishes off `U` has the same integral
against `μ` and `μ.restrict U`. -/
lemma integral_eq_integral_restrict_of_eq_zero_off [MeasurableSpace E] {μ : Measure E}
    {U : Set E} (hU_meas : MeasurableSet U) {f : E → ℝ} (hzero : ∀ x ∉ U, f x = 0) :
    ∫ x, f x ∂μ = ∫ x, f x ∂(μ.restrict U) := by
  -- Rewrite the full integral as the integral of the indicator, then use the standard
  -- restriction formula.
  calc
    ∫ x, f x ∂μ = ∫ x, U.indicator f x ∂μ := by
      congr 1
      ext x
      by_cases hx : x ∈ U
      · simp [Set.indicator, hx]
      · simp [Set.indicator, hx, hzero x hx]
    _ = ∫ x, f x ∂(μ.restrict U) := integral_indicator hU_meas

/-- Helper for Theorem 13.11: if two measures agree on all common integrals over
`Lip₁(E; [0,1])`, then their restricted integrals of a thickened indicator agree on any measurable
set containing the corresponding thickening, provided the restrictions are finite. -/
lemma restrictIntegral_thickenedIndicator_eq_of_unitIntervalLipschitzTests
    [MeasurableSpace E] [MetricSpace E] [BorelSpace E] {μ ν : Measure E} {K U : Set E} {ε : ℝ}
    [IsFiniteMeasure (μ.restrict U)] [IsFiniteMeasure (ν.restrict U)]
    (hInt :
      ∀ ⦃f : E → ℝ⦄, f ∈ unitIntervalLipschitzRealFunctionSpace E →
        Integrable f μ → Integrable f ν → ∫ x, f x ∂μ = ∫ x, f x ∂ν)
    (hU_meas : MeasurableSet U) (hε : 0 < ε) (hε_le_one : ε ≤ 1)
    (hthick : Metric.thickening ε K ⊆ U) :
    ∫ x, (thickenedIndicator hε K x : ℝ) ∂(μ.restrict U) =
      ∫ x, (thickenedIndicator hε K x : ℝ) ∂(ν.restrict U) := by
  have htest :
      (fun x : E ↦ ε * (thickenedIndicator hε K x : ℝ)) ∈
        unitIntervalLipschitzRealFunctionSpace E :=
    scaledThickenedIndicator_mem_unitIntervalLipschitz (K := K) hε hε_le_one
  have hzero_off_U : ∀ x ∉ U, ε * (thickenedIndicator hε K x : ℝ) = 0 := by
    intro x hxU
    exact smul_thickenedIndicator_eq_zero_of_not_mem_thickening (K := K) hε fun hx_thick ↦
      hxU (hthick hx_thick)
  have hscaled_int_μ : Integrable (fun x : E ↦ ε * (thickenedIndicator hε K x : ℝ)) μ := by
    have hscaled_restrict : Integrable (fun x : E ↦ ε * (thickenedIndicator hε K x : ℝ))
        (μ.restrict U) := by
      -- On the finite restriction, integrability follows directly from the standard cutoff lemma.
      exact (integrable_thickenedIndicator K hε).const_mul ε
    exact integrable_of_integrable_restrict_of_eq_zero_off (μ := μ) hU_meas hzero_off_U
      hscaled_restrict
  have hscaled_int_ν : Integrable (fun x : E ↦ ε * (thickenedIndicator hε K x : ℝ)) ν := by
    have hscaled_restrict : Integrable (fun x : E ↦ ε * (thickenedIndicator hε K x : ℝ))
        (ν.restrict U) := by
      exact (integrable_thickenedIndicator K hε).const_mul ε
    exact integrable_of_integrable_restrict_of_eq_zero_off (μ := ν) hU_meas hzero_off_U
      hscaled_restrict
  have hEq_scaled :
      ∫ x, ε * (thickenedIndicator hε K x : ℝ) ∂μ =
        ∫ x, ε * (thickenedIndicator hε K x : ℝ) ∂ν :=
    hInt htest hscaled_int_μ hscaled_int_ν
  have hEq_scaled_restrict :
      ∫ x, ε * (thickenedIndicator hε K x : ℝ) ∂(μ.restrict U) =
        ∫ x, ε * (thickenedIndicator hε K x : ℝ) ∂(ν.restrict U) := by
    -- Rewrite both full integrals through restriction because the cutoff vanishes off `U`.
    calc
      ∫ x, ε * (thickenedIndicator hε K x : ℝ) ∂(μ.restrict U)
          = ∫ x, ε * (thickenedIndicator hε K x : ℝ) ∂μ := by
              symm
              exact integral_eq_integral_restrict_of_eq_zero_off (μ := μ) hU_meas hzero_off_U
      _ = ∫ x, ε * (thickenedIndicator hε K x : ℝ) ∂ν := hEq_scaled
      _ = ∫ x, ε * (thickenedIndicator hε K x : ℝ) ∂(ν.restrict U) := by
              exact integral_eq_integral_restrict_of_eq_zero_off (μ := ν) hU_meas hzero_off_U
  -- Divide out the positive scalar `ε` to recover equality for the unscaled cutoff.
  have hcancel := congrArg (fun t : ℝ => ε⁻¹ * t) hEq_scaled_restrict
  simpa [integral_const_mul, mul_assoc, hε.ne'] using hcancel

/-- Helper for Theorem 13.11: a compactly supported scaled thickened indicator yields the same
restricted integrals for `μ` and `ν` once the two measures agree on all compactly supported
`[0,1]`-valued `1`-Lipschitz tests. -/
lemma restrictIntegral_thickenedIndicator_eq_of_compactlySupportedTests
    [MeasurableSpace E] [MetricSpace E] [BorelSpace E] {μ ν : Measure E}
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] {K V : Set E} {ε : ℝ}
    (hInt :
      ∀ ⦃f : E → ℝ⦄,
        f ∈ (((↑) : C_c(E, ℝ) → E → ℝ) ''
            compactlySupportedUnitIntervalLipschitzRealMapSpace E) →
        Integrable f μ → Integrable f ν → ∫ x, f x ∂μ = ∫ x, f x ∂ν)
    (hV_meas : MeasurableSet V) (hVc : IsCompact (closure V)) (hε : 0 < ε) (hε_le_one : ε ≤ 1)
    (hthick : Metric.thickening ε K ⊆ V) :
    ∫ x, (thickenedIndicator hε K x : ℝ) ∂(μ.restrict V) =
      ∫ x, (thickenedIndicator hε K x : ℝ) ∂(ν.restrict V) := by
  obtain ⟨g, hg_def⟩ :=
    compactlySupportedScaledThickenedIndicator (K := K) (V := V) hε hthick hVc
  have hg_mem :
      (g : E → ℝ) ∈ (((↑) : C_c(E, ℝ) → E → ℝ) ''
        compactlySupportedUnitIntervalLipschitzRealMapSpace E) := by
    -- The packaged cutoff is exactly the scaled thickened indicator, so the previously proved
    -- admissibility lemma supplies the Lipschitz and range bounds.
    refine ⟨g, ?_, rfl⟩
    simpa
        [unitIntervalLipschitzRealFunctionSpace,
          compactlySupportedUnitIntervalLipschitzRealMapSpace, hg_def]
      using
      (scaledThickenedIndicator_mem_unitIntervalLipschitz (K := K) hε hε_le_one)
  have hg_int_μ : Integrable (g : E → ℝ) μ := by
    -- Compact support makes the test integrable against any locally finite measure.
    exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hg_int_ν : Integrable (g : E → ℝ) ν := by
    exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hEq_scaled : ∫ x, (g : E → ℝ) x ∂μ = ∫ x, (g : E → ℝ) x ∂ν := by
    exact hInt hg_mem hg_int_μ hg_int_ν
  have hzero_off_V : ∀ x ∉ V, ε * (thickenedIndicator hε K x : ℝ) = 0 := by
    intro x hxV
    exact smul_thickenedIndicator_eq_zero_of_not_mem_thickening (K := K) hε fun hx_thick ↦
      hxV (hthick hx_thick)
  have hEq_scaled_restrict :
      ∫ x, ε * (thickenedIndicator hε K x : ℝ) ∂(μ.restrict V) =
        ∫ x, ε * (thickenedIndicator hε K x : ℝ) ∂(ν.restrict V) := by
    -- Rewrite both full integrals through restriction because the cutoff vanishes off `V`.
    calc
      ∫ x, ε * (thickenedIndicator hε K x : ℝ) ∂(μ.restrict V)
          = ∫ x, ε * thickenedIndicator hε K x ∂μ := by
              symm
              exact integral_eq_integral_restrict_of_eq_zero_off (μ := μ) hV_meas hzero_off_V
      _ = ∫ x, ε * (thickenedIndicator hε K x : ℝ) ∂ν := by simpa [hg_def] using hEq_scaled
      _ = ∫ x, ε * (thickenedIndicator hε K x : ℝ) ∂(ν.restrict V) := by
              exact integral_eq_integral_restrict_of_eq_zero_off (μ := ν) hV_meas hzero_off_V
  -- Divide out the positive scalar `ε` to recover equality for the unscaled cutoff.
  have hcancel := congrArg (fun t : ℝ => ε⁻¹ * t) hEq_scaled_restrict
  simpa [integral_const_mul, mul_assoc, hε.ne'] using hcancel

/-- Helper for Theorem 13.11: equality of restricted integrals of thickened indicators along a
shrinking sequence forces equality on the underlying compact set. -/
lemma measure_isCompact_eq_of_restrictIntegral_thickenedIndicator_tendsto
    [MeasurableSpace E] [MetricSpace E] [BorelSpace E] {μ ν : Measure E} {K U : Set E}
    [IsFiniteMeasure (μ.restrict U)] [IsFiniteMeasure (ν.restrict U)]
    (hK : IsCompact K) (hU_meas : MeasurableSet U) (hKU : K ⊆ U) {δs : ℕ → ℝ}
    (hδs_pos : ∀ n, 0 < δs n) (hδs_tendsto : Filter.Tendsto δs atTop (𝓝 0))
    (hEq_restrict :
      ∀ n,
        ∫ x, (thickenedIndicator (hδs_pos n) K x : ℝ) ∂(μ.restrict U) =
          ∫ x, (thickenedIndicator (hδs_pos n) K x : ℝ) ∂(ν.restrict U)) :
    μ K = ν K := by
  have hμK_restrict_lt : (μ.restrict U) K < ⊤ := measure_lt_top (μ := μ.restrict U) K
  have hνK_restrict_lt : (ν.restrict U) K < ⊤ := measure_lt_top (μ := ν.restrict U) K
  have hμK_lt : μ K < ⊤ := by
    simpa [Measure.restrict_apply' hU_meas, inter_eq_left.mpr hKU] using hμK_restrict_lt
  have hνK_lt : ν K < ⊤ := by
    simpa [Measure.restrict_apply' hU_meas, inter_eq_left.mpr hKU] using hνK_restrict_lt
  have hμ_tendsto :
      Filter.Tendsto (fun n ↦ ∫ x, (thickenedIndicator (hδs_pos n) K x : ℝ) ∂(μ.restrict U))
        atTop (𝓝 ((μ.restrict U).real K)) := by
    simpa using
      tendsto_integral_thickenedIndicator_of_isClosed (μ := μ.restrict U) hK.isClosed
        hδs_pos hδs_tendsto
  have hν_tendsto :
      Filter.Tendsto (fun n ↦ ∫ x, (thickenedIndicator (hδs_pos n) K x : ℝ) ∂(ν.restrict U))
        atTop (𝓝 ((ν.restrict U).real K)) := by
    simpa using
      tendsto_integral_thickenedIndicator_of_isClosed (μ := ν.restrict U) hK.isClosed
        hδs_pos hδs_tendsto
  have hμ_tendsto' :
      Filter.Tendsto (fun n ↦ ∫ x, (thickenedIndicator (hδs_pos n) K x : ℝ) ∂(ν.restrict U))
        atTop (𝓝 ((μ.restrict U).real K)) := by
    refine hμ_tendsto.congr' ?_
    filter_upwards [Filter.Eventually.of_forall hEq_restrict] with n hn
    exact hn
  have hreal_restrict : (μ.restrict U).real K = (ν.restrict U).real K :=
    tendsto_nhds_unique hμ_tendsto' hν_tendsto
  have hμ_real : (μ.restrict U).real K = μ.real K := by
    simpa [inter_eq_left.mpr hKU] using
      (measureReal_restrict_apply' (μ := μ) (s := U) (t := K) hU_meas)
  have hν_real : (ν.restrict U).real K = ν.real K := by
    simpa [inter_eq_left.mpr hKU] using
      (measureReal_restrict_apply' (μ := ν) (s := U) (t := K) hU_meas)
  have hreal : μ.real K = ν.real K := by
    simpa [hμ_real, hν_real] using hreal_restrict
  exact (measureReal_eq_measureReal_iff (μ := μ) (ν := ν) (s := K) (t := K) hμK_lt.ne hνK_lt.ne).mp
    hreal

/-- Helper for Theorem 13.11: if two Radon measures agree on all common integrals over
`Lip₁(E; [0,1])`, then they agree on compact sets. -/
lemma measure_isCompact_eq_of_forall_integral_eq_unitIntervalLipschitz
    [MeasurableSpace E] [MetricSpace E] [BorelSpace E] {μ ν : Measure E}
    (hμ : IsRadonMeasure μ) (hν : IsRadonMeasure ν)
    (hInt :
      ∀ ⦃f : E → ℝ⦄, f ∈ unitIntervalLipschitzRealFunctionSpace E →
        Integrable f μ → Integrable f ν → ∫ x, f x ∂μ = ∫ x, f x ∂ν)
    {K : Set E} (hK : IsCompact K) :
    μ K = ν K := by
  letI : IsLocallyFiniteMeasure μ := hμ.locallyFinite
  letI : IsLocallyFiniteMeasure ν := hν.locallyFinite
  obtain ⟨Uμ, hKUμ, hUμ_open, hμUμ⟩ := hK.exists_open_superset_measure_lt_top μ
  obtain ⟨Uν, hKUν, hUν_open, hνUν⟩ := hK.exists_open_superset_measure_lt_top ν
  let U : Set E := Uμ ∩ Uν
  have hKU : K ⊆ U := fun x hx ↦ ⟨hKUμ hx, hKUν hx⟩
  have hU_open : IsOpen U := hUμ_open.inter hUν_open
  have hμU : μ U < ⊤ := lt_of_le_of_lt (measure_mono inter_subset_left) hμUμ
  have hνU : ν U < ⊤ := lt_of_le_of_lt (measure_mono inter_subset_right) hνUν
  obtain ⟨δ, hδ_pos, hδU⟩ := hK.exists_thickening_subset_open hU_open hKU
  let δ0 : ℝ := min δ 1
  have hδ0_pos : 0 < δ0 := lt_min hδ_pos zero_lt_one
  have hδ0_le_δ : δ0 ≤ δ := min_le_left _ _
  have hδ0_le_one : δ0 ≤ 1 := min_le_right _ _
  let δs : ℕ → ℝ := fun n ↦ δ0 / (n + 1)
  have hδs_pos : ∀ n, 0 < δs n := by
    intro n
    exact div_pos hδ0_pos (Nat.cast_add_one_pos n)
  have hδs_le_δ : ∀ n, δs n ≤ δ := by
    intro n
    calc
      δs n = δ0 / (n + 1) := rfl
      _ ≤ δ0 := div_le_self hδ0_pos.le (by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      _ ≤ δ := hδ0_le_δ
  have hδs_le_one : ∀ n, δs n ≤ 1 := by
    intro n
    calc
      δs n = δ0 / (n + 1) := rfl
      _ ≤ δ0 := div_le_self hδ0_pos.le (by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      _ ≤ 1 := hδ0_le_one
  have hδs_tendsto : Filter.Tendsto δs atTop (𝓝 0) := by
    -- Reuse the same shrinking radii as in part (2).
    simpa [δs, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ δ0) atTop (𝓝 δ0)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
          (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1))
          atTop (𝓝 (0 : ℝ)))
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  letI : IsFiniteMeasure (μ.restrict U) := isFiniteMeasure_restrict.2 hμU.ne
  letI : IsFiniteMeasure (ν.restrict U) := isFiniteMeasure_restrict.2 hνU.ne
  have hEq_restrict :
      ∀ n,
        ∫ x, (thickenedIndicator (hδs_pos n) K x : ℝ) ∂(μ.restrict U) =
          ∫ x, (thickenedIndicator (hδs_pos n) K x : ℝ) ∂(ν.restrict U) := by
    intro n
    have hthickU : Metric.thickening (δs n) K ⊆ U := by
      intro x hx
      exact hδU <| Metric.thickening_mono (hδs_le_δ n) K hx
    simpa using
      restrictIntegral_thickenedIndicator_eq_of_unitIntervalLipschitzTests
        (μ := μ) (ν := ν) (K := K) (U := U) hInt hU_meas (hδs_pos n) (hδs_le_one n) hthickU
  exact measure_isCompact_eq_of_restrictIntegral_thickenedIndicator_tendsto
    (μ := μ) (ν := ν) (K := K) (U := U) hK hU_meas hKU hδs_pos hδs_tendsto hEq_restrict

/-- Helper for Theorem 13.11: in the locally compact case, agreement on all common integrals over
`C_c(E) ∩ Lip₁(E; [0,1])` forces agreement on compact sets. -/
lemma measure_isCompact_eq_of_forall_integral_eq_compactlySupportedUnitIntervalLipschitz
    [MeasurableSpace E] [MetricSpace E] [BorelSpace E] [LocallyCompactSpace E]
    {μ ν : Measure E} (hμ : IsRadonMeasure μ) (hν : IsRadonMeasure ν)
    (hInt :
      ∀ ⦃f : E → ℝ⦄,
        f ∈ (((↑) : C_c(E, ℝ) → E → ℝ) ''
            compactlySupportedUnitIntervalLipschitzRealMapSpace E) →
        Integrable f μ → Integrable f ν → ∫ x, f x ∂μ = ∫ x, f x ∂ν)
    {K : Set E} (hK : IsCompact K) :
    μ K = ν K := by
  letI : IsLocallyFiniteMeasure μ := hμ.locallyFinite
  letI : IsLocallyFiniteMeasure ν := hν.locallyFinite
  obtain ⟨V, hV_open, hKV, hVc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨δ, hδ_pos, hδV⟩ := hK.exists_thickening_subset_open hV_open hKV
  let δ0 : ℝ := min δ 1
  have hδ0_pos : 0 < δ0 := lt_min hδ_pos zero_lt_one
  have hδ0_le_δ : δ0 ≤ δ := min_le_left _ _
  have hδ0_le_one : δ0 ≤ 1 := min_le_right _ _
  let δs : ℕ → ℝ := fun n ↦ δ0 / (n + 1)
  have hδs_pos : ∀ n, 0 < δs n := by
    intro n
    exact div_pos hδ0_pos (Nat.cast_add_one_pos n)
  have hδs_le_δ : ∀ n, δs n ≤ δ := by
    intro n
    calc
      δs n = δ0 / (n + 1) := rfl
      _ ≤ δ0 := div_le_self hδ0_pos.le (by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      _ ≤ δ := hδ0_le_δ
  have hδs_le_one : ∀ n, δs n ≤ 1 := by
    intro n
    calc
      δs n = δ0 / (n + 1) := rfl
      _ ≤ δ0 := div_le_self hδ0_pos.le (by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      _ ≤ 1 := hδ0_le_one
  have hδs_tendsto : Filter.Tendsto δs atTop (𝓝 0) := by
    -- Reuse the same shrinking radii as in part (1).
    simpa [δs, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ δ0) atTop (𝓝 δ0)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
          (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1))
          atTop (𝓝 (0 : ℝ)))
  have hμV : μ V < ⊤ := lt_of_le_of_lt (measure_mono subset_closure) hVc.measure_lt_top
  have hνV : ν V < ⊤ := lt_of_le_of_lt (measure_mono subset_closure) hVc.measure_lt_top
  have hV_meas : MeasurableSet V := hV_open.measurableSet
  letI : IsFiniteMeasure (μ.restrict V) := isFiniteMeasure_restrict.2 hμV.ne
  letI : IsFiniteMeasure (ν.restrict V) := isFiniteMeasure_restrict.2 hνV.ne
  have hEq_restrict :
      ∀ n,
        ∫ x, (thickenedIndicator (hδs_pos n) K x : ℝ) ∂(μ.restrict V) =
          ∫ x, (thickenedIndicator (hδs_pos n) K x : ℝ) ∂(ν.restrict V) := by
    intro n
    have hthickV : Metric.thickening (δs n) K ⊆ V := by
      intro x hx
      exact hδV <| Metric.thickening_mono (hδs_le_δ n) K hx
    simpa using
      restrictIntegral_thickenedIndicator_eq_of_compactlySupportedTests
        (μ := μ) (ν := ν) (K := K) (V := V) hInt hV_meas hVc (hδs_pos n) (hδs_le_one n) hthickV
  exact measure_isCompact_eq_of_restrictIntegral_thickenedIndicator_tendsto
    (μ := μ) (ν := ν) (K := K) (U := V) hK hV_meas hKV hδs_pos hδs_tendsto hEq_restrict

-- Proof sketch: apply Definition 13.9 to reduce separation to equality of two Radon measures from
-- agreement of all common integrable tests in `Lip₁(E; [0,1])`; then approximate compact-set
-- indicators by the distance cutoffs from Lemma 13.10 and conclude by inner regularity.
/-- Theorem 13.11 (1): The family `Lip₁(E; [0,1])` is separating for the Radon measures
`𝓜(E)`. -/
theorem unitIntervalLipschitzRealFunctionSpace_isSeparatingFamilyFor_radonMeasureSpace
    [MeasurableSpace E] [MetricSpace E] [BorelSpace E] :
    IsSeparatingFamilyFor {μ : Measure E | IsRadonMeasure μ}
      (unitIntervalLipschitzRealFunctionSpace E) := by
  unfold IsSeparatingFamilyFor
  constructor
  · -- Every `1`-Lipschitz real-valued test is continuous, hence measurable.
    intro f hf
    exact hf.1.continuous.measurable
  · intro μ ν hμ hν hInt
    have hμ_radon : IsRadonMeasure μ := hμ
    have hν_radon : IsRadonMeasure ν := hν
    letI : InnerRegular μ := hμ_radon.innerRegular
    letI : InnerRegular ν := hν_radon.innerRegular
    -- Equality on compact sets upgrades to equality of measures by inner regularity.
    apply measure_eq_of_forall_isCompact
    intro K hK
    exact measure_isCompact_eq_of_forall_integral_eq_unitIntervalLipschitz
      hμ_radon hν_radon hInt hK

-- Proof sketch: as in part (1), use the distance cutoffs around compact sets; local compactness
-- lets one choose relatively compact neighborhoods so that the same cutoffs have compact support
-- and therefore lie in `C_c(E) ∩ Lip₁(E; [0,1])`.
/-- Theorem 13.11 (2): If `E` is locally compact, then `C_c(E) ∩ Lip₁(E; [0,1])` is separating
for the Radon measures `𝓜(E)`. -/
theorem
    compactlySupportedUnitIntervalLipschitzRealFunctionSpace_isSeparatingFamilyFor_radonMeasureSpace
    [MeasurableSpace E] [MetricSpace E] [BorelSpace E] [LocallyCompactSpace E] :
    IsSeparatingFamilyFor {μ : Measure E | IsRadonMeasure μ}
      (((↑) : C_c(E, ℝ) → E → ℝ) '' compactlySupportedUnitIntervalLipschitzRealMapSpace E) := by
  unfold IsSeparatingFamilyFor
  constructor
  · -- The underlying function of a compactly supported continuous map is measurable.
    rintro f ⟨g, -, rfl⟩
    exact g.continuous.measurable
  · intro μ ν hμ hν hInt
    have hμ_radon : IsRadonMeasure μ := hμ
    have hν_radon : IsRadonMeasure ν := hν
    letI : InnerRegular μ := hμ_radon.innerRegular
    letI : InnerRegular ν := hν_radon.innerRegular
    -- In the locally compact case the same compact cutoffs can be bundled into `C_c(E, ℝ)`.
    apply measure_eq_of_forall_isCompact
    intro K hK
    exact measure_isCompact_eq_of_forall_integral_eq_compactlySupportedUnitIntervalLipschitz
      hμ_radon hν_radon hInt hK
