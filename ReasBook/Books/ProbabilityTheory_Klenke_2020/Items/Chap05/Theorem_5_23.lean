/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_22

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u

variable {Ω : Type u}

/-- Helper for Theorem 5.23: the open empirical cdf averages the indicators of the strict lower
intervals `(-∞, x)`. -/
private noncomputable def openEmpiricalDistributionFunction {n : ℕ}
    (X : Fin (n + 1) → Ω → ℝ) : Ω → ℝ → ℝ :=
  fun ω x ↦
    (∑ i : Fin (n + 1), if X i ω < x then (1 : ℝ) else 0) / (n + 1 : ℝ)

/-- Helper for Theorem 5.23: the open empirical cdf is the empirical average of the strict
lower-interval indicators. -/
private theorem openEmpiricalDistributionFunction_apply {n : ℕ}
    (X : Fin (n + 1) → Ω → ℝ) (ω : Ω) (x : ℝ) :
    openEmpiricalDistributionFunction X ω x =
      (∑ i : Fin (n + 1), if X i ω < x then (1 : ℝ) else 0) / (n + 1 : ℝ) :=
  rfl

variable [MeasurableSpace Ω]

/-- Helper for Theorem 5.23: the left limit of the cdf of a real random variable is the open-ray
probability `P[Y < x]`. -/
private theorem cdf_leftLim_eq_real_preimage_Iio
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Measurable Y) (x : ℝ) :
    Function.leftLim (cdf (P.map Y)) x = P.real (Y ⁻¹' Set.Iio x) := by
  have hprob : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hmeasure : (cdf (P.map Y)).measure (Set.Iio x) = P.map Y (Set.Iio x) := by
    -- Proof comment: the cdf of `P.map Y` reconstructs the pushed-forward measure.
    simpa using congrArg (fun μ : Measure ℝ ↦ μ (Set.Iio x))
      (measure_cdf (P.map Y))
  have hleft :
      (cdf (P.map Y)).measure (Set.Iio x) = ENNReal.ofReal (Function.leftLim (cdf (P.map Y)) x) := by
    -- Proof comment: the Stieltjes-measure formula for `Iio` identifies the open ray with the
    -- left limit because the cdf starts at `0` at `-∞`.
    simpa [sub_zero] using (cdf (P.map Y)).measure_Iio (tendsto_cdf_atBot (P.map Y)) x
  calc
    Function.leftLim (cdf (P.map Y)) x = ((cdf (P.map Y)).measure (Set.Iio x)).toReal := by
      have hleft_nonneg : 0 ≤ Function.leftLim (cdf (P.map Y)) x := by
        obtain ⟨y, hy⟩ := exists_lt x
        exact le_trans (cdf_nonneg (P.map Y) y) ((monotone_cdf (P.map Y)).le_leftLim hy)
      have hleft_toReal := congrArg ENNReal.toReal hleft
      simpa [hleft_nonneg] using hleft_toReal.symm
    _ = P.real (Y ⁻¹' Set.Iio x) := by
      rw [hmeasure, Measure.real_def,
        Measure.map_apply_of_aemeasurable hY.aemeasurable measurableSet_Iio]

/-- Helper for Theorem 5.23: at a fixed point `x`, the shifted closed and open empirical cdfs
converge almost surely to `F(x)` and `F(x-)`, respectively. -/
private theorem ae_tendsto_empirical_cdf_at_point
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P) (x : ℝ) :
    ∀ᵐ ω ∂P,
      Tendsto
          (fun n ↦ empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x)
          atTop (𝓝 (cdf (P.map (X 1)) x)) ∧
        Tendsto
          (fun n ↦ openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x)
          atTop (𝓝 (Function.leftLim (cdf (P.map (X 1))) x)) := by
  let F : ℝ → ℝ := cdf (P.map (X 1))
  let Fc : ℝ → ℝ := Set.indicator (Set.Iic x) (fun _ ↦ (1 : ℝ))
  let Fo : ℝ → ℝ := Set.indicator (Set.Iio x) (fun _ ↦ (1 : ℝ))
  let Yc : ℕ → Ω → ℝ := fun n ↦ Fc ∘ X (n + 1)
  let Yo : ℕ → Ω → ℝ := fun n ↦ Fo ∘ X (n + 1)
  have hX1_ae : AEMeasurable (X 1) P := (hX_iid.identDistrib 0 0).aemeasurable_fst
  let X1m : Ω → ℝ := hX1_ae.mk (X 1)
  have hX1m_ae : X1m =ᵐ[P] X 1 := hX1_ae.ae_eq_mk.symm
  haveI : IsProbabilityMeasure (P.map (X 1)) := Measure.isProbabilityMeasure_map hX1_ae
  haveI : IsProbabilityMeasure (P.map X1m) :=
    Measure.isProbabilityMeasure_map hX1_ae.measurable_mk.aemeasurable
  have hFc_meas : Measurable Fc := by
    -- Proof comment: the closed-ray indicator is measurable.
    exact (measurable_indicator_const_iff (1 : ℝ)).2 measurableSet_Iic
  have hFo_meas : Measurable Fo := by
    -- Proof comment: the open-ray indicator is measurable.
    exact (measurable_indicator_const_iff (1 : ℝ)).2 measurableSet_Iio
  have hYc_integrable : Integrable (Yc 0) P := by
    -- Proof comment: the closed indicator is a bounded simple function, hence integrable after
    -- composition with `X₁`.
    have hmk :
        Integrable
          ((SimpleFunc.piecewise (Set.Iic x) measurableSet_Iic
            (SimpleFunc.const ℝ (1 : ℝ)) (SimpleFunc.const ℝ (0 : ℝ))).comp X1m
              hX1_ae.measurable_mk) P :=
      SimpleFunc.integrable_of_isFiniteMeasure
        ((SimpleFunc.piecewise (Set.Iic x) measurableSet_Iic
          (SimpleFunc.const ℝ (1 : ℝ)) (SimpleFunc.const ℝ (0 : ℝ))).comp X1m
            hX1_ae.measurable_mk)
    refine hmk.congr ?_
    simpa [Yc, Fc, X1m] using (hX1m_ae.fun_comp Fc)
  have hYo_integrable : Integrable (Yo 0) P := by
    -- Proof comment: the open indicator is handled in the same way.
    have hmk :
        Integrable
          ((SimpleFunc.piecewise (Set.Iio x) measurableSet_Iio
            (SimpleFunc.const ℝ (1 : ℝ)) (SimpleFunc.const ℝ (0 : ℝ))).comp X1m
              hX1_ae.measurable_mk) P :=
      SimpleFunc.integrable_of_isFiniteMeasure
        ((SimpleFunc.piecewise (Set.Iio x) measurableSet_Iio
          (SimpleFunc.const ℝ (1 : ℝ)) (SimpleFunc.const ℝ (0 : ℝ))).comp X1m
            hX1_ae.measurable_mk)
    refine hmk.congr ?_
    simpa [Yo, Fo, X1m] using (hX1m_ae.fun_comp Fo)
  have hYc_iIndep : iIndepFun Yc P := by
    -- Proof comment: independence is preserved under measurable postcomposition.
    exact hX_iid.iIndepFun.comp (fun _ ↦ Fc) fun _ ↦ hFc_meas
  have hYo_iIndep : iIndepFun Yo P := by
    -- Proof comment: the same measurable postcomposition argument works for the open indicators.
    exact hX_iid.iIndepFun.comp (fun _ ↦ Fo) fun _ ↦ hFo_meas
  have hYc_ident : ∀ n, IdentDistrib (Yc n) (Yc 0) P P := by
    -- Proof comment: all shifted closed indicators have the same distribution because the
    -- underlying sequence is identically distributed.
    intro n
    exact (hX_iid.identDistrib n 0).comp hFc_meas
  have hYo_ident : ∀ n, IdentDistrib (Yo n) (Yo 0) P P := by
    -- Proof comment: likewise for the open indicators.
    intro n
    exact (hX_iid.identDistrib n 0).comp hFo_meas
  have hYc_limit :
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Yc i ω) / n) atTop (𝓝 P[Yc 0]) := by
    exact strong_law_ae_real Yc hYc_integrable
      (fun i j hij ↦ hYc_iIndep.indepFun hij) hYc_ident
  have hYo_limit :
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Yo i ω) / n) atTop (𝓝 P[Yo 0]) := by
    exact strong_law_ae_real Yo hYo_integrable
      (fun i j hij ↦ hYo_iIndep.indepFun hij) hYo_ident
  have hYc_expectation : P[Yc 0] = F x := by
    -- Proof comment: the expectation of the closed indicator is exactly the cdf value `F(x)`.
    calc
      P[Yc 0] = ∫ ω, Fc (X 1 ω) ∂P := by
        rfl
      _ = ∫ y, Fc y ∂(P.map (X 1)) := by
        rw [integral_map hX1_ae hFc_meas.aestronglyMeasurable]
      _ = (P.map (X 1)).real (Set.Iic x) := by
        simp [Fc, integral_indicator_const, measurableSet_Iic, smul_eq_mul]
      _ = F x := by
        simpa [F] using (cdf_eq_real (P.map (X 1)) x).symm
  have hYo_expectation : P[Yo 0] = Function.leftLim F x := by
    -- Proof comment: the expectation of the open indicator is the left limit `F(x-)`.
    have hmap : P.map X1m = P.map (X 1) := by
      simpa [X1m] using (Measure.map_congr hX1_ae.ae_eq_mk).symm
    calc
      P[Yo 0] = ∫ ω, Fo (X 1 ω) ∂P := by
        rfl
      _ = ∫ y, Fo y ∂(P.map (X 1)) := by
        rw [integral_map hX1_ae hFo_meas.aestronglyMeasurable]
      _ = (P.map (X 1)).real (Set.Iio x) := by
        simp [Fo, integral_indicator_const, measurableSet_Iio, smul_eq_mul]
      _ = Function.leftLim F x := by
        calc
          (P.map (X 1)).real (Set.Iio x) = (P.map X1m).real (Set.Iio x) := by
            rw [hmap]
          _ = P.real (X1m ⁻¹' Set.Iio x) := by
            have happly :
                P.map X1m (Set.Iio x) = P (X1m ⁻¹' Set.Iio x) :=
              Measure.map_apply hX1_ae.measurable_mk measurableSet_Iio
            simpa [Measure.real_def] using congrArg ENNReal.toReal happly
          _ = Function.leftLim (cdf (P.map X1m)) x := by
            exact (cdf_leftLim_eq_real_preimage_Iio P hX1_ae.measurable_mk x).symm
          _ = Function.leftLim F x := by
            simp [F, hmap]
  filter_upwards [hYc_limit, hYo_limit] with ω hωc hωo
  constructor
  · -- Proof comment: reindex the strong-law averages from `range n` to the empirical cdf with
    -- sample size `n + 1`.
    have hshift :
        Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range (n + 1), Yc i ω) / (n + 1 : ℝ)) atTop
          (𝓝 P[Yc 0]) := by
      convert hωc.comp (tendsto_add_atTop_nat 1) using 1
      ext n
      simp
    refine Tendsto.congr' ?_ (hYc_expectation ▸ hshift)
    refine Filter.Eventually.of_forall fun n ↦ ?_
    have hsum :
        ∑ i ∈ Finset.range (n + 1), Yc i ω =
          ∑ i ∈ Finset.range (n + 1), if X (i + 1) ω ≤ x then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hix : X (i + 1) ω ≤ x
      · simp [Yc, Fc, hix]
      · simp [Yc, Fc, hix]
    calc
      (∑ i ∈ Finset.range (n + 1), Yc i ω) / (n + 1 : ℝ) =
          (∑ i ∈ Finset.range (n + 1), if X (i + 1) ω ≤ x then (1 : ℝ) else 0) / (n + 1 : ℝ) := by
        rw [hsum]
      _ =
          (∑ i : Fin (n + 1), if X (i.1 + 1) ω ≤ x then (1 : ℝ) else 0) / (n + 1 : ℝ) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ if X (i + 1) ω ≤ x then (1 : ℝ) else 0)
          (n + 1)]
      _ = empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x := by
        simpa using
          (empiricalDistributionFunction_apply (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x).symm
  · -- Proof comment: the same reindexing turns the open averages into the strict empirical cdf.
    have hshift :
        Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range (n + 1), Yo i ω) / (n + 1 : ℝ)) atTop
          (𝓝 P[Yo 0]) := by
      convert hωo.comp (tendsto_add_atTop_nat 1) using 1
      ext n
      simp
    refine Tendsto.congr' ?_ (hYo_expectation ▸ hshift)
    refine Filter.Eventually.of_forall fun n ↦ ?_
    have hsum :
        ∑ i ∈ Finset.range (n + 1), Yo i ω =
          ∑ i ∈ Finset.range (n + 1), if X (i + 1) ω < x then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hix : X (i + 1) ω < x
      · simp [Yo, Fo, hix]
      · simp [Yo, Fo, hix]
    calc
      (∑ i ∈ Finset.range (n + 1), Yo i ω) / (n + 1 : ℝ) =
          (∑ i ∈ Finset.range (n + 1), if X (i + 1) ω < x then (1 : ℝ) else 0) / (n + 1 : ℝ) := by
        rw [hsum]
      _ =
          (∑ i : Fin (n + 1), if X (i.1 + 1) ω < x then (1 : ℝ) else 0) / (n + 1 : ℝ) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ if X (i + 1) ω < x then (1 : ℝ) else 0)
          (n + 1)]
      _ = openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x := by
        simpa using
          (openEmpiricalDistributionFunction_apply (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x).symm

/-- Helper for Theorem 5.23: on every finite grid of real points, the shifted closed and open
empirical cdfs converge almost surely and simultaneously at all grid points. -/
private theorem ae_tendsto_empirical_cdf_on_finite_grid
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P) (s : Finset ℝ) :
    ∀ᵐ ω ∂P,
      ∀ x ∈ s,
        Tendsto
            (fun n ↦ empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x)
            atTop (𝓝 (cdf (P.map (X 1)) x)) ∧
          Tendsto
            (fun n ↦ openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x)
            atTop (𝓝 (Function.leftLim (cdf (P.map (X 1))) x)) := by
  have hattach :
      ∀ᵐ ω ∂P, ∀ y : s,
        Tendsto
            (fun n ↦ empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω y.1)
            atTop (𝓝 (cdf (P.map (X 1)) y.1)) ∧
          Tendsto
            (fun n ↦ openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω y.1)
            atTop (𝓝 (Function.leftLim (cdf (P.map (X 1))) y.1)) := by
    -- Proof comment: intersect the finitely many almost-sure events by quantifying over the
    -- attached finite type.
    rw [ae_all_iff]
    intro y
    simpa using ae_tendsto_empirical_cdf_at_point P X hX_iid y.1
  filter_upwards [hattach] with ω hω x hx
  simpa using hω ⟨x, hx⟩

/-- Helper for Theorem 5.23: every interior level `t ∈ (0,1)` admits a real quantile point
`q` with `F(q-) ≤ t ≤ F(q)`. -/
private theorem exists_stieltjes_quantile
    (F : StieltjesFunction ℝ) (hbot : Tendsto F atBot (𝓝 0))
    (htop : Tendsto F atTop (𝓝 1)) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ q : ℝ, Function.leftLim F q ≤ t ∧ t ≤ F q := by
  let S : Set ℝ := {x | t ≤ F x}
  have hS_nonempty : S.Nonempty := by
    -- Proof comment: because `F(x) → 1` at `+∞`, some point has cdf value at least `t`.
    have hmem : Set.Ioi t ∈ 𝓝 (1 : ℝ) := Ioi_mem_nhds ht1
    have h_eventually : ∀ᶠ x in atTop, t < F x := htop hmem
    obtain ⟨x, hx⟩ := h_eventually.exists
    exact ⟨x, le_of_lt hx⟩
  have hS_bddBelow : BddBelow S := by
    -- Proof comment: because `F(x) → 0` at `-∞`, points with cdf value strictly below `t`
    -- provide lower bounds for the superlevel set `S`.
    have hhalf : 0 < t / 2 := by
      linarith
    have hmem : Set.Iio (t / 2) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hhalf
    have h_eventually : ∀ᶠ x in atBot, F x < t / 2 := hbot hmem
    obtain ⟨x, hx⟩ := h_eventually.exists
    refine ⟨x, ?_⟩
    intro y hy
    by_contra hxy
    have hyx : y < x := lt_of_not_ge hxy
    have hxlt : F x < t := by
      linarith
    exact absurd hxlt (not_lt_of_ge (le_trans hy (F.mono (le_of_lt hyx))))
  let q : ℝ := sInf S
  refine ⟨q, ?_, ?_⟩
  · -- Proof comment: if the left limit were above `t`, some point strictly left of `q` would
    -- already lie in the superlevel set, contradicting the infimum property of `q`.
    rw [Monotone.leftLim_eq_sSup F.mono (by infer_instance : NeBot (𝓝[<] q)).ne]
    refine csSup_le ?_ ?_
    · rcases exists_lt q with ⟨x, hx⟩
      exact ⟨F x, ⟨x, hx, rfl⟩⟩
    · rintro _ ⟨x, hxlt, rfl⟩
      by_cases hxt : t ≤ F x
      · have hq_le : q ≤ x := csInf_le hS_bddBelow hxt
        exact False.elim (absurd hxlt (not_lt_of_ge hq_le))
      · exact le_of_lt (lt_of_not_ge hxt)
  · -- Proof comment: right continuity at the infimum sends `q` into the infimum of the image of
    -- the superlevel set, and every point in that image is at least `t`.
    have hcont : ContinuousWithinAt F S q := by
      refine (F.right_continuous q).mono ?_
      intro x hx
      exact csInf_le hS_bddBelow hx
    have hq : F q = sInf (F '' S) :=
      MonotoneOn.map_csInf_of_continuousWithinAt hcont (F.mono.monotoneOn S) hS_nonempty
        hS_bddBelow
    have hlower : t ≤ sInf (F '' S) := by
      refine le_csInf ?_ ?_
      · rcases hS_nonempty with ⟨x, hx⟩
        exact ⟨F x, ⟨x, hx, rfl⟩⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact hx
    simpa [q, hq] using hlower

/-- Helper for Theorem 5.23: for every positive mesh size `1 / N`, the cdf has real left and
right tail cutoffs whose masses are at most `1 / N`. -/
private theorem exists_cdf_tail_cutoffs
    (F : StieltjesFunction ℝ) (hbot : Tendsto F atBot (𝓝 0))
    (htop : Tendsto F atTop (𝓝 1)) (N : ℕ) (hN : 0 < N) :
    ∃ a b : ℝ, F a ≤ (1 : ℝ) / N ∧ 1 - (1 : ℝ) / N ≤ F b := by
  have hN_real : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hleft_mem : Set.Iio ((1 : ℝ) / N) ∈ 𝓝 (0 : ℝ) := by
    apply Iio_mem_nhds
    exact one_div_pos.mpr hN_real
  have hright_mem : Set.Ioi (1 - (1 : ℝ) / N) ∈ 𝓝 (1 : ℝ) := by
    apply Ioi_mem_nhds
    linarith [one_div_pos.mpr hN_real]
  have hleft_eventually : ∀ᶠ x in atBot, F x < (1 : ℝ) / N := hbot hleft_mem
  have hright_eventually : ∀ᶠ x in atTop, 1 - (1 : ℝ) / N < F x := htop hright_mem
  obtain ⟨a, ha⟩ := hleft_eventually.exists
  obtain ⟨b, hb⟩ := hright_eventually.exists
  -- Proof comment: the tail estimates come directly from the cdf limits at `±∞`.
  exact ⟨a, b, ha.le, hb.le⟩

/-- Helper for Theorem 5.23: `cdfQuantilePoint F M j` is the canonical real quantile chosen from
the superlevel set `{x | j / (M + 1) ≤ F x}`. -/
private noncomputable def cdfQuantilePoint (F : StieltjesFunction ℝ) (M j : ℕ) : ℝ :=
  sInf {x : ℝ | (j : ℝ) / (M + 1 : ℝ) ≤ F x}

/-- Helper for Theorem 5.23: the superlevel set defining `cdfQuantilePoint F M j` is bounded below
as soon as `j / (M + 1)` is positive. -/
private theorem cdfQuantileSuperlevel_bddBelow
    (F : StieltjesFunction ℝ) (hbot : Tendsto F atBot (𝓝 0)) {M j : ℕ}
    (hj1 : 1 ≤ j) :
    BddBelow {x : ℝ | (j : ℝ) / (M + 1 : ℝ) ≤ F x} := by
  let t : ℝ := (j : ℝ) / (M + 1 : ℝ)
  have ht0 : 0 < t := by
    have hj_real : 0 < (j : ℝ) := by
      exact_mod_cast hj1
    positivity
  have hhalf : 0 < t / 2 := by
    linarith
  have hmem : Set.Iio (t / 2) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hhalf
  have h_eventually : ∀ᶠ x in atBot, F x < t / 2 := hbot hmem
  obtain ⟨x, hx⟩ := h_eventually.exists
  -- Proof comment: any point where `F` is strictly below the target level is a lower bound for
  -- the whole superlevel set by monotonicity of `F`.
  refine ⟨x, ?_⟩
  intro y hy
  by_contra hxy
  have hyx : y < x := lt_of_not_ge hxy
  have hxlt : F x < t := by
    linarith
  exact absurd hxlt (not_lt_of_ge (le_trans hy (F.mono (le_of_lt hyx))))

/-- Helper for Theorem 5.23: the canonical quantile point `cdfQuantilePoint F M j` satisfies the
expected Stieltjes left-limit and value bounds `F(q-) ≤ j / (M + 1) ≤ F(q)`. -/
private theorem cdfQuantilePoint_spec
    (F : StieltjesFunction ℝ) (hbot : Tendsto F atBot (𝓝 0))
    (htop : Tendsto F atTop (𝓝 1)) {M j : ℕ}
    (hj1 : 1 ≤ j) (hjM : j ≤ M) :
    Function.leftLim F (cdfQuantilePoint F M j) ≤ (j : ℝ) / (M + 1 : ℝ) ∧
      (j : ℝ) / (M + 1 : ℝ) ≤ F (cdfQuantilePoint F M j) := by
  let t : ℝ := (j : ℝ) / (M + 1 : ℝ)
  let S : Set ℝ := {x : ℝ | t ≤ F x}
  have ht0 : 0 < t := by
    have hj_real : 0 < (j : ℝ) := by
      exact_mod_cast hj1
    positivity
  have ht1 : t < 1 := by
    have hj_lt : (j : ℝ) < (M + 1 : ℝ) := by
      exact_mod_cast Nat.lt_succ_of_le hjM
    have hden : 0 < (M + 1 : ℝ) := by
      positivity
    simpa [t] using (div_lt_one hden).2 hj_lt
  have hS_nonempty : S.Nonempty := by
    -- Proof comment: because `F(x) → 1` at `+∞`, some point reaches the target superlevel.
    have hmem : Set.Ioi t ∈ 𝓝 (1 : ℝ) := Ioi_mem_nhds ht1
    have h_eventually : ∀ᶠ x in atTop, t < F x := htop hmem
    obtain ⟨x, hx⟩ := h_eventually.exists
    exact ⟨x, le_of_lt hx⟩
  have hS_bddBelow : BddBelow S := by
    simpa [S, t] using cdfQuantileSuperlevel_bddBelow F hbot (M := M) (j := j) hj1
  change Function.leftLim F (sInf S) ≤ t ∧ t ≤ F (sInf S)
  constructor
  · -- Proof comment: any point strictly left of the infimum lies outside the superlevel set.
    rw [Monotone.leftLim_eq_sSup F.mono (by infer_instance : NeBot (𝓝[<] sInf S)).ne]
    refine csSup_le ?_ ?_
    · rcases exists_lt (sInf S) with ⟨x, hx⟩
      exact ⟨F x, ⟨x, hx, rfl⟩⟩
    · rintro _ ⟨x, hxlt, rfl⟩
      by_cases hxt : t ≤ F x
      · have hsInf_le : sInf S ≤ x := csInf_le hS_bddBelow hxt
        exact False.elim (absurd hxlt (not_lt_of_ge hsInf_le))
      · exact le_of_lt (lt_of_not_ge hxt)
  · -- Proof comment: right continuity at the infimum turns the infimum of the superlevel set into
    -- the infimum of its image under `F`.
    have hcont : ContinuousWithinAt F S (sInf S) := by
      refine (F.right_continuous (sInf S)).mono ?_
      intro x hx
      exact csInf_le hS_bddBelow hx
    have hsInf :
        F (sInf S) = sInf (F '' S) :=
      MonotoneOn.map_csInf_of_continuousWithinAt hcont (F.mono.monotoneOn S) hS_nonempty
        hS_bddBelow
    have hlower : t ≤ sInf (F '' S) := by
      refine le_csInf ?_ ?_
      · rcases hS_nonempty with ⟨x, hx⟩
        exact ⟨F x, ⟨x, hx, rfl⟩⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact hx
    simpa [hsInf] using hlower

/-- Helper for Theorem 5.23: any point whose cdf value already reaches the level `j / (M + 1)`
lies to the right of the canonical quantile `cdfQuantilePoint F M j`. -/
private theorem cdfQuantilePoint_le_of_le
    (F : StieltjesFunction ℝ) (hbot : Tendsto F atBot (𝓝 0)) {M j : ℕ}
    (hj1 : 1 ≤ j) {x : ℝ} (hx : (j : ℝ) / (M + 1 : ℝ) ≤ F x) :
    cdfQuantilePoint F M j ≤ x := by
  let S : Set ℝ := {y : ℝ | (j : ℝ) / (M + 1 : ℝ) ≤ F y}
  have hS_bddBelow : BddBelow S := by
    simpa [S] using cdfQuantileSuperlevel_bddBelow F hbot (M := M) (j := j) hj1
  -- Proof comment: `x` itself belongs to the defining superlevel set, so the infimum is below it.
  change sInf S ≤ x
  exact csInf_le hS_bddBelow (by simpa [S] using hx)

/-- Helper for Theorem 5.23: if the cdf value at `x` is strictly below the level `j / (M + 1)`,
then `x` lies strictly to the left of the canonical quantile `cdfQuantilePoint F M j`. -/
private theorem lt_cdfQuantilePoint_of_lt
    (F : StieltjesFunction ℝ) (hbot : Tendsto F atBot (𝓝 0))
    (htop : Tendsto F atTop (𝓝 1)) {M j : ℕ}
    (hj1 : 1 ≤ j) (hjM : j ≤ M) {x : ℝ}
    (hx : F x < (j : ℝ) / (M + 1 : ℝ)) :
    x < cdfQuantilePoint F M j := by
  have hspec := (cdfQuantilePoint_spec F hbot htop (M := M) (j := j) hj1 hjM).2
  -- Proof comment: if the quantile were not strictly to the right of `x`, monotonicity of `F`
  -- would force `F x` to already exceed the target level.
  by_contra hqx
  have hq_le_x : cdfQuantilePoint F M j ≤ x := le_of_not_gt hqx
  have hlevel : (j : ℝ) / (M + 1 : ℝ) ≤ F x := le_trans hspec (F.mono hq_le_x)
  exact not_le_of_gt hx hlevel

/-- Helper for Theorem 5.23: the canonical quantile points are monotone in the level index. -/
private theorem cdfQuantilePoint_mono
    (F : StieltjesFunction ℝ) (hbot : Tendsto F atBot (𝓝 0))
    (htop : Tendsto F atTop (𝓝 1)) {M j k : ℕ}
    (hj1 : 1 ≤ j) (hjM : j ≤ M) (hk1 : 1 ≤ k) (hkM : k ≤ M) (hjk : j ≤ k) :
    cdfQuantilePoint F M j ≤ cdfQuantilePoint F M k := by
  have hspec := (cdfQuantilePoint_spec F hbot htop (M := M) (j := k) hk1 hkM).2
  have hlevel :
      (j : ℝ) / (M + 1 : ℝ) ≤ (k : ℝ) / (M + 1 : ℝ) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hjk) (by positivity)
  exact cdfQuantilePoint_le_of_le F hbot (M := M) (j := j) hj1 (hlevel.trans hspec)

/-- Helper for Theorem 5.23: the empirical cdf is monotone in the spatial variable. -/
private theorem monotone_empiricalDistributionFunction {n : ℕ}
    (X : Fin (n + 1) → Ω → ℝ) (ω : Ω) :
    Monotone (empiricalDistributionFunction X ω) := by
  intro x y hxy
  rw [empiricalDistributionFunction_apply, empiricalDistributionFunction_apply]
  have hsum :
      ∑ i : Fin (n + 1), (if X i ω ≤ x then (1 : ℝ) else 0) ≤
        ∑ i : Fin (n + 1), (if X i ω ≤ y then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    by_cases hix : X i ω ≤ x
    · have hiy : X i ω ≤ y := le_trans hix hxy
      simp [hix, hiy]
    · by_cases hiy : X i ω ≤ y
      · simp [hix, hiy]
      · simp [hix, hiy]
  exact div_le_div_of_nonneg_right hsum (by positivity)

/-- Helper for Theorem 5.23: if `x < y`, then the closed empirical cdf at `x` is bounded by the
open empirical cdf at `y`. -/
private theorem empiricalDistributionFunction_le_openEmpiricalDistributionFunction_of_lt {n : ℕ}
    (X : Fin (n + 1) → Ω → ℝ) (ω : Ω) {x y : ℝ} (hxy : x < y) :
    empiricalDistributionFunction X ω x ≤ openEmpiricalDistributionFunction X ω y := by
  rw [empiricalDistributionFunction_apply, openEmpiricalDistributionFunction_apply]
  have hsum :
      ∑ i : Fin (n + 1), (if X i ω ≤ x then (1 : ℝ) else 0) ≤
        ∑ i : Fin (n + 1), (if X i ω < y then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    by_cases hix : X i ω ≤ x
    · have hiy : X i ω < y := lt_of_le_of_lt hix hxy
      simp [hix, hiy]
    · by_cases hiy : X i ω < y
      · simp [hix, hiy]
      · simp [hix, hiy]
  exact div_le_div_of_nonneg_right hsum (by positivity)

-- Proof sketch: for each fixed `x`, apply the strong law of large numbers to the indicator
-- variables of the events `X_i <= x` and `X_i < x` to get almost
-- sure convergence of the empirical cdf at the finitely many quantile points used in the standard
-- proof. Those quantile controls imply that the Kolmogorov distance between the empirical
-- distribution function and the common cdf has almost-sure `limsup` equal to `0`.
/-- Theorem 5.23: Glivenko--Cantelli. For an i.i.d. real sequence `X_1, X_2, ...`, the Kolmogorov
distance between the empirical distribution function `F_n` and the common distribution function
`F` has almost-sure `limsup` equal to `0`. -/
theorem glivenko_cantelli_ae
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P) :
    ∀ᵐ ω ∂P,
      limsup
        (fun n ↦
          sSup <|
            Set.range fun x ↦
              |empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x -
                cdf (P.map (X 1)) x|) atTop = 0 := by
  let F := cdf (P.map (X 1))
  let K : Ω → ℕ → ℝ := fun ω n ↦
    sSup <|
      Set.range fun x ↦
        |empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x - F x|
  change ∀ᵐ ω ∂P, limsup (K ω) atTop = 0
  have hfinite_grid :
      ∀ s : Finset ℝ, ∀ᵐ ω ∂P,
        ∀ x ∈ s,
          Tendsto
              (fun n ↦ empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x)
              atTop (𝓝 (F x)) ∧
            Tendsto
              (fun n ↦ openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x)
              atTop (𝓝 (Function.leftLim F x)) := by
    intro s
    simpa [F] using ae_tendsto_empirical_cdf_on_finite_grid P X hX_iid s
  have hbot : Tendsto F atBot (𝓝 0) := by
    simpa [F] using tendsto_cdf_atBot (P.map (X 1))
  have htop : Tendsto F atTop (𝓝 1) := by
    simpa [F] using tendsto_cdf_atTop (P.map (X 1))
  have hF_nonneg : ∀ x : ℝ, 0 ≤ F x := by
    intro x
    simpa [F] using cdf_nonneg (P.map (X 1)) x
  have hF_le_one : ∀ x : ℝ, F x ≤ 1 := by
    intro x
    simpa [F] using cdf_le_one (P.map (X 1)) x
  have habs_le_one :
      ∀ ω n x,
        |empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x - F x| ≤ 1 := by
    intro ω n x
    have hFn :
        empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x ∈ Set.Icc (0 : ℝ) 1 :=
      empiricalDistributionFunction_mem_Icc (fun i : Fin (n + 1) ↦ X (i.1 + 1)) x ω
    have hFx : F x ∈ Set.Icc (0 : ℝ) 1 := ⟨hF_nonneg x, hF_le_one x⟩
    have hlower :
        -(1 : ℝ) ≤ empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x - F x := by
      nlinarith [hFn.1, hFx.2]
    have hupper :
        empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x - F x ≤ 1 := by
      nlinarith [hFn.2, hFx.1]
    exact abs_le.2 ⟨hlower, hupper⟩
  have hK_le_one : ∀ ω n, K ω n ≤ 1 := by
    intro ω n
    -- Proof comment: every pointwise empirical-cdf error is bounded by `1`, so the supremum is
    -- also bounded by `1`.
    refine Real.sSup_le ?_ zero_le_one
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact habs_le_one ω n x
  have hK_nonneg : ∀ ω n, 0 ≤ K ω n := by
    intro ω n
    refine Real.sSup_nonneg ?_
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact abs_nonneg _
  have hfixed : ∀ m : ℕ, ∀ᵐ ω ∂P, limsup (K ω) atTop ≤ 1 / ((m : ℝ) + 2) := by
    intro m
    let M : ℕ := m + 1
    let q : ℕ → ℝ := fun j ↦ cdfQuantilePoint F M j
    let closedErr : Ω → ℕ → ℕ → ℝ := fun ω n j ↦
      |empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω (q j) - F (q j)|
    let openErr : Ω → ℕ → ℕ → ℝ := fun ω n j ↦
      |openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω (q j) -
        Function.leftLim F (q j)|
    let R : Ω → ℕ → ℝ := fun ω n ↦
      ∑ j ∈ Finset.Icc 1 M, (closedErr ω n j + openErr ω n j)
    have hgrid :
        ∀ᵐ ω ∂P,
          ∀ j ∈ Finset.Icc 1 M,
            Tendsto
                (fun n ↦ empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω (q j))
                atTop (𝓝 (F (q j))) ∧
              Tendsto
                (fun n ↦
                  openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω (q j))
                atTop (𝓝 (Function.leftLim F (q j))) := by
      classical
      have hgrid_raw := hfinite_grid ((Finset.Icc 1 M).image q)
      filter_upwards [hgrid_raw] with ω hω j hj
      exact hω (q j) (by exact Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    have hR_nonneg : ∀ ω n, 0 ≤ R ω n := by
      intro ω n
      simpa [R] using Finset.sum_nonneg (fun j hj ↦ by positivity)
    have hclosed_le_R : ∀ ω n j, j ∈ Finset.Icc 1 M → closedErr ω n j ≤ R ω n := by
      intro ω n j hj
      have hsingle :
          closedErr ω n j + openErr ω n j ≤ R ω n := by
        have hnonneg : ∀ k ∈ Finset.Icc 1 M, 0 ≤ closedErr ω n k + openErr ω n k := by
          intro k hk
          positivity
        simpa [R] using
          (Finset.single_le_sum (f := fun k ↦ closedErr ω n k + openErr ω n k) hnonneg hj)
      linarith [show 0 ≤ openErr ω n j by simp [openErr], hsingle]
    have hopen_le_R : ∀ ω n j, j ∈ Finset.Icc 1 M → openErr ω n j ≤ R ω n := by
      intro ω n j hj
      have hsingle :
          closedErr ω n j + openErr ω n j ≤ R ω n := by
        have hnonneg : ∀ k ∈ Finset.Icc 1 M, 0 ≤ closedErr ω n k + openErr ω n k := by
          intro k hk
          positivity
        simpa [R] using
          (Finset.single_le_sum (f := fun k ↦ closedErr ω n k + openErr ω n k) hnonneg hj)
      linarith [show 0 ≤ closedErr ω n j by simp [closedErr], hsingle]
    have hq_spec :
        ∀ j, j ∈ Finset.Icc 1 M →
          Function.leftLim F (q j) ≤ (j : ℝ) / (M + 1 : ℝ) ∧
            (j : ℝ) / (M + 1 : ℝ) ≤ F (q j) := by
      intro j hj
      exact cdfQuantilePoint_spec F hbot htop (M := M) (j := j) (Finset.mem_Icc.mp hj).1
        (Finset.mem_Icc.mp hj).2
    have hR_tendsto : ∀ᵐ ω ∂P, Tendsto (fun n ↦ R ω n) atTop (𝓝 0) := by
      -- Proof comment: the finite sum of the closed/open grid errors tends to `0` because each
      -- summand converges to `0` almost surely on the finite quantile grid.
      filter_upwards [hgrid] with ω hω
      have hterm :
          ∀ j ∈ Finset.Icc 1 M,
            Tendsto (fun n ↦ closedErr ω n j + openErr ω n j) atTop (𝓝 0) := by
        intro j hj
        rcases hω j hj with ⟨hclose, hopen⟩
        have hclose_zero : Tendsto (fun n ↦ closedErr ω n j) atTop (𝓝 0) := by
          have hsub : Tendsto
              (fun n ↦ empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω (q j) -
                F (q j)) atTop (𝓝 0) := by
            simpa using hclose.sub
              (show Tendsto (fun _ : ℕ ↦ F (q j)) atTop (𝓝 (F (q j))) from tendsto_const_nhds)
          simpa [closedErr] using hsub.abs
        have hopen_zero : Tendsto (fun n ↦ openErr ω n j) atTop (𝓝 0) := by
          have hsub : Tendsto
              (fun n ↦ openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω
                (q j) - Function.leftLim F (q j)) atTop (𝓝 0) := by
            simpa using hopen.sub
              (show Tendsto (fun _ : ℕ ↦ Function.leftLim F (q j)) atTop
                (𝓝 (Function.leftLim F (q j))) from tendsto_const_nhds)
          simpa [openErr] using hsub.abs
        simpa using hclose_zero.add hopen_zero
      simpa [R] using tendsto_finset_sum (Finset.Icc 1 M) hterm
    have hpointwise :
        ∀ ω n x,
          |empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x - F x| ≤
            R ω n + 1 / (M + 1 : ℝ) := by
      intro ω n x
      let Fn : ℝ → ℝ := empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω
      let Gn : ℝ → ℝ := openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω
      have hFn_mem : Fn x ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Fn] using empiricalDistributionFunction_mem_Icc
          (fun i : Fin (n + 1) ↦ X (i.1 + 1)) x ω
      have hFn_mono : Monotone Fn := by
        simpa [Fn] using monotone_empiricalDistributionFunction
          (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω
      by_cases hlow : F x < 1 / (M + 1 : ℝ)
      · have hx_lt_q1 : x < q 1 := by
          exact lt_cdfQuantilePoint_of_lt F hbot htop (M := M) (j := 1) (by simp) (by simp [M])
            (by simpa using hlow)
        have hupper_emp : Fn x ≤ Gn (q 1) := by
          simpa [Fn, Gn] using
            empiricalDistributionFunction_le_openEmpiricalDistributionFunction_of_lt
              (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω hx_lt_q1
        have hupper_err :
            Gn (q 1) - Function.leftLim F (q 1) ≤ openErr ω n 1 := by
          simpa [Gn, openErr, q] using le_abs_self (Gn (q 1) - Function.leftLim F (q 1))
        have hupper :
            Fn x - F x ≤ R ω n + 1 / (M + 1 : ℝ) := by
          have hq1 := hq_spec 1 (by simp [M])
          have hopenR := hopen_le_R ω n 1 (by simp [M])
          linarith [hF_nonneg x, hupper_emp, hupper_err, hq1.1, hopenR]
        have hlower :
            F x - Fn x ≤ R ω n + 1 / (M + 1 : ℝ) := by
          linarith [hFn_mem.1, hlow, hR_nonneg ω n]
        rw [abs_sub_le_iff]
        constructor <;> linarith
      · by_cases hhigh : (M : ℝ) / (M + 1 : ℝ) ≤ F x
        · have hqM_le_x : q M ≤ x := by
            exact cdfQuantilePoint_le_of_le F hbot (M := M) (j := M) (by simp [M]) hhigh
          have hlower_emp : Fn (q M) ≤ Fn x := hFn_mono hqM_le_x
          have hlower_err :
              F (q M) - Fn (q M) ≤ closedErr ω n M := by
            simpa [Fn, closedErr, q, abs_sub_comm] using le_abs_self (F (q M) - Fn (q M))
          have hupper :
              Fn x - F x ≤ R ω n + 1 / (M + 1 : ℝ) := by
            have hmesh : 1 - (M : ℝ) / (M + 1 : ℝ) = (1 : ℝ) / (M + 1 : ℝ) := by
              field_simp
              ring
            linarith [hFn_mem.2, hhigh, hR_nonneg ω n, hmesh]
          have hlower :
              F x - Fn x ≤ R ω n + 1 / (M + 1 : ℝ) := by
            have hqM := hq_spec M (by simp [M])
            have hcloseR := hclosed_le_R ω n M (by simp [M])
            have hmesh : 1 - (M : ℝ) / (M + 1 : ℝ) = (1 : ℝ) / (M + 1 : ℝ) := by
              field_simp
              ring
            linarith [hF_le_one x, hlower_emp, hlower_err, hqM.2, hcloseR, hmesh]
          rw [abs_sub_le_iff]
          constructor <;> linarith
        · have hmid_low : (1 : ℝ) / (M + 1 : ℝ) ≤ F x := le_of_not_gt hlow
          have hmid_high : F x < (M : ℝ) / (M + 1 : ℝ) := lt_of_not_ge hhigh
          let j : ℕ := Nat.floor ((M + 1 : ℝ) * F x)
          have hmul_nonneg : 0 ≤ ((M + 1 : ℝ) * F x) := by
            exact mul_nonneg (by positivity) (hF_nonneg x)
          have hj1 : 1 ≤ j := by
            have hone : (1 : ℝ) ≤ (M + 1 : ℝ) * F x := by
              have hmid_low' := hmid_low
              field_simp at hmid_low' ⊢
              nlinarith
            simpa [j] using ((Nat.one_le_floor_iff ((M + 1 : ℝ) * F x)).2 hone)
          have hj_lt_M : j < M := by
            have hltM : ((M + 1 : ℝ) * F x) < M := by
              have hmid_high' := hmid_high
              field_simp at hmid_high' ⊢
              nlinarith
            simpa [j] using (Nat.floor_lt hmul_nonneg).2 hltM
          have hj_le_M : j ≤ M := Nat.le_of_lt hj_lt_M
          have hj_succ_le_M : j + 1 ≤ M := Nat.succ_le_of_lt hj_lt_M
          have hden : 0 < (M + 1 : ℝ) := by
            positivity
          have hj_lower : (j : ℝ) / (M + 1 : ℝ) ≤ F x := by
            have hfloor_le : (j : ℝ) ≤ (M + 1 : ℝ) * F x := by
              simpa [j] using (Nat.floor_le hmul_nonneg)
            have hfloor_le' := hfloor_le
            field_simp at hfloor_le' ⊢
            nlinarith
          have hj_upper : F x < ((j + 1 : ℕ) : ℝ) / (M + 1 : ℝ) := by
            have hlt_succ : ((M + 1 : ℝ) * F x) < (j + 1 : ℕ) := by
              simpa [j] using Nat.lt_succ_floor ((M + 1 : ℝ) * F x)
            have hlt_succ' := hlt_succ
            field_simp at hlt_succ' ⊢
            nlinarith
          have hqj_le_x : q j ≤ x := by
            exact cdfQuantilePoint_le_of_le F hbot (M := M) (j := j) hj1 hj_lower
          have hx_lt_qsucc : x < q (j + 1) := by
            exact lt_cdfQuantilePoint_of_lt F hbot htop (M := M) (j := j + 1)
              (Nat.succ_le_succ (Nat.zero_le j)) hj_succ_le_M hj_upper
          have hupper_emp : Fn x ≤ Gn (q (j + 1)) := by
            simpa [Fn, Gn] using
              empiricalDistributionFunction_le_openEmpiricalDistributionFunction_of_lt
                (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω hx_lt_qsucc
          have hupper_err :
              Gn (q (j + 1)) - Function.leftLim F (q (j + 1)) ≤ openErr ω n (j + 1) := by
            simpa [Gn, openErr, q] using
              le_abs_self (Gn (q (j + 1)) - Function.leftLim F (q (j + 1)))
          have hlower_emp : Fn (q j) ≤ Fn x := hFn_mono hqj_le_x
          have hlower_err :
              F (q j) - Fn (q j) ≤ closedErr ω n j := by
            simpa [Fn, closedErr, q, abs_sub_comm] using le_abs_self (F (q j) - Fn (q j))
          have hsplit :
              ((j + 1 : ℕ) : ℝ) / (M + 1 : ℝ) =
                (j : ℝ) / (M + 1 : ℝ) + 1 / (M + 1 : ℝ) := by
            field_simp
            norm_num
          have hupper :
              Fn x - F x ≤ R ω n + 1 / (M + 1 : ℝ) := by
            have hjsucc_mem : j + 1 ∈ Finset.Icc 1 M := by
              exact Finset.mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le j), hj_succ_le_M⟩
            have hqsucc := hq_spec (j + 1) hjsucc_mem
            have hopenR := hopen_le_R ω n (j + 1) hjsucc_mem
            linarith
          have hlower :
              F x - Fn x ≤ R ω n + 1 / (M + 1 : ℝ) := by
            have hj_mem : j ∈ Finset.Icc 1 M := by
              exact Finset.mem_Icc.mpr ⟨hj1, hj_le_M⟩
            have hqj := hq_spec j hj_mem
            have hcloseR := hclosed_le_R ω n j hj_mem
            linarith
          rw [abs_sub_le_iff]
          constructor <;> linarith
    have hK_le :
        ∀ ω n, K ω n ≤ R ω n + 1 / (M + 1 : ℝ) := by
      intro ω n
      -- Proof comment: the pointwise grid estimate controls the full Kolmogorov distance by
      -- taking the supremum over `x`.
      refine csSup_le ?_ ?_
      · exact Set.range_nonempty _
      · intro y hy
        rcases hy with ⟨x, rfl⟩
        exact hpointwise ω n x
    filter_upwards [hR_tendsto] with ω hRω
    have hRplus :
        Tendsto (fun n ↦ R ω n + 1 / (M + 1 : ℝ)) atTop (𝓝 (1 / (M + 1 : ℝ))) := by
      simpa using hRω.add tendsto_const_nhds
    have hK_cobounded : Filter.IsCoboundedUnder (fun x y => x ≤ y) atTop (K ω) := by
      exact Filter.isCoboundedUnder_le_of_le atTop (hK_nonneg ω)
    have hRplus_bounded :
        Filter.IsBoundedUnder (fun x y => x ≤ y) atTop (fun n ↦ R ω n + 1 / (M + 1 : ℝ)) := by
      exact hRplus.isBoundedUnder_le
    calc
      limsup (K ω) atTop ≤ limsup (fun n ↦ R ω n + 1 / (M + 1 : ℝ)) atTop := by
        exact Filter.limsup_le_limsup (Filter.Eventually.of_forall (hK_le ω)) hK_cobounded
          hRplus_bounded
      _ = 1 / (M + 1 : ℝ) := hRplus.limsup_eq
      _ = 1 / ((m : ℝ) + 2) := by
        simp [M]
        ring
  have hall : ∀ᵐ ω ∂P, ∀ m : ℕ, limsup (K ω) atTop ≤ 1 / ((m : ℝ) + 2) := by
    rw [ae_all_iff]
    exact hfixed
  filter_upwards [hall] with ω hω
  have hnonneg : 0 ≤ limsup (K ω) atTop := by
    have hK_bounded : Filter.IsBoundedUnder (fun x y => x ≤ y) atTop (K ω) := by
      exact Filter.isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall (hK_le_one ω))
    exact Filter.le_limsup_of_frequently_le
      (Filter.Frequently.of_forall fun n ↦ hK_nonneg ω n) hK_bounded
  have hle : limsup (K ω) atTop ≤ 0 := by
    by_contra hpos
    have hpos' : 0 < limsup (K ω) atTop := lt_of_not_ge hpos
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos'
    have hmesh_le : 1 / ((m : ℝ) + 2) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    have hbound : limsup (K ω) atTop ≤ 1 / ((m : ℝ) + 1) := le_trans (hω m) hmesh_le
    exact not_lt_of_ge hbound hm
  exact le_antisymm hle hnonneg
