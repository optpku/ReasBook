/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Corollary_8_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

section Setup

variable {μ : Measure Ω}

/-- Helper for Theorem 25.4: predictable processes give measurable ambient `Ω × ℝ`
realizations via `processToTimeSpaceFun`. -/
private theorem measurable_processToTimeSpaceFun_of_isPredictable
    {ℱ : TimeFiltration} {G : Process} (hG_pred : IsPredictable ℱ G) :
    Measurable (processToTimeSpaceFun G) := by
  have h_uncurry : Measurable (Function.uncurry G) := by
    have hPred_meas : Measurable[ℱ.predictable] (Function.uncurry G) := hG_pred.measurable
    have hPred_le : ℱ.predictable ≤ (inferInstance : MeasurableSpace (NNReal × Ω)) := by
      refine measurableSpace_le_predictable_of_measurableSet ?_ ?_
      · intro A hA
        exact (measurableSet_singleton _).prod <|
          show MeasurableSet A from (ℱ.le (0 : NNReal)) A hA
      · intro t A hA
        exact measurableSet_Ioi.prod <|
          show MeasurableSet A from (ℱ.le t) A hA
    rw [measurable_iff_comap_le] at hPred_meas ⊢
    exact hPred_meas.trans hPred_le
  have h_map : Measurable (fun x : Ω × ℝ ↦ (x.2.toNNReal, x.1)) := by
    -- Proof comment: `processToTimeSpaceFun` only swaps the coordinates and clamps the real time
    -- to `NNReal`.
    exact measurable_snd.real_toNNReal.prodMk measurable_fst
  -- Proof comment: compose the time-first predictable uncurry with the coordinate swap used by
  -- `processToTimeSpaceFun`.
  simpa [processToTimeSpaceFun, Function.uncurry] using h_uncurry.comp h_map
/-- Helper for Theorem 25.4: restricting `processMeasure μ` to a deterministic time interval
recovers the corresponding product measure with interval-restricted Lebesgue measure. -/
private theorem processMeasure_restrict_eq_prod_Icc
    (μ : Measure Ω) [SFinite μ] (T : NNReal) :
    (processMeasure μ).restrict ((Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) (T : ℝ)) =
      μ.prod (volume.restrict (Set.Icc (0 : ℝ) (T : ℝ))) := by
  have hsubset : Set.Icc (0 : ℝ) (T : ℝ) ⊆ Set.Ici (0 : ℝ) := by
    -- Proof comment: the deterministic cutoff interval already lies inside the nonnegative-time
    -- half-line used by `processMeasure`.
    intro t ht
    exact ht.1
  -- Proof comment: `processMeasure` is already a product measure, so restricting to
  -- `Ω × [0,T]` is exactly the same as restricting only the time factor to `Icc (0,T)`.
  rw [processMeasure, ← Measure.prod_restrict]
  simp [Measure.restrict_restrict, measurableSet_Icc,
    Set.inter_eq_left.mpr hsubset]
/-- Helper for Theorem 25.4: a predictable-step representation is uniformly bounded by the sum of
the absolute values of its chosen coefficient bounds. -/
private theorem predictableStepRepresentation_abs_le_sumCoeffBounds
    {ℱ : TimeFiltration} (data : PredictableStepRepresentation ℱ) :
    ∀ t ω,
      |data.toProcess t ω| ≤
        ∑ i, |Classical.choose (data.coeff_bounded i)| := by
  intro t ω
  -- Proof comment: bound each active coefficient by its chosen uniform constant and then use the
  -- triangle inequality on the finite sum defining `data.toProcess`.
  rw [PredictableStepRepresentation.toProcess_apply]
  calc
    |∑ i : Fin data.n,
        data.coeff i ω *
          Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
            (fun _ : NNReal ↦ (1 : ℝ)) t| ≤
        ∑ i : Fin data.n,
          |data.coeff i ω *
            Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
              (fun _ : NNReal ↦ (1 : ℝ)) t| := by
          simpa [Real.norm_eq_abs] using
            norm_sum_le
              (Finset.univ : Finset (Fin data.n))
              (fun i ↦
                data.coeff i ω *
                  Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
                    (fun _ : NNReal ↦ (1 : ℝ)) t)
    _ ≤ ∑ i : Fin data.n, |Classical.choose (data.coeff_bounded i)| := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          by_cases ht : t ∈ Set.Ioc (data.times i.castSucc) (data.times i.succ)
          · rw [Set.indicator_of_mem ht, mul_one]
            exact le_trans (Classical.choose_spec (data.coeff_bounded i) ω) (le_abs_self _)
          · rw [Set.indicator_of_notMem ht, mul_zero, abs_zero]
            positivity
/-- Helper for Theorem 25.4: a bounded predictable coefficient multiplied by one Brownian
increment is square-integrable. -/
private theorem predictableStepCoefficient_mul_brownianIncrement_memLp
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (data : PredictableStepRepresentation ℱ) (i : Fin data.n) :
    MemLp
      (fun ω ↦
        data.coeff i ω * (W (data.times i.succ) ω - W (data.times i.castSucc) ω))
      2 μ := by
  let inc : Ω → ℝ := fun ω ↦ W (data.times i.succ) ω - W (data.times i.castSucc) ω
  have hStartEnd : data.times i.castSucc ≤ data.times i.succ := by
    -- Proof comment: consecutive partition times are ordered by strict monotonicity.
    exact le_of_lt (data.times_strictMono i.castSucc_lt_succ)
  have hCoeff_sm : StronglyMeasurable (data.coeff i) := by
    -- Proof comment: the predictable coefficient is measurable for the ambient sigma-algebra once
    -- we forget down to `mΩ`.
    exact ((data.coeff_measurable i).mono (ℱ.le _) le_rfl).stronglyMeasurable
  have hInc_mem : MemLp inc 2 μ := by
    -- Proof comment: a single Brownian increment is an `L²` random variable.
    simpa [inc] using brownianIncrement_memLp_two hW hStartEnd
  have hTerm_sm :
      AEStronglyMeasurable (fun ω ↦ data.coeff i ω * inc ω) μ := by
    -- Proof comment: the product term is measurable because both factors are measurable.
    exact hCoeff_sm.aestronglyMeasurable.mul hInc_mem.aestronglyMeasurable
  rcases data.coeff_bounded i with ⟨C, hC⟩
  -- Proof comment: the bounded coefficient is absorbed into a deterministic scalar multiple of
  -- the Brownian increment.
  let c : ℝ := |C|
  refine @MemLp.of_le_mul Ω ℝ ℝ mΩ 2 μ _ _ (fun ω ↦ data.coeff i ω * inc ω) inc c
    hInc_mem hTerm_sm ?_
  filter_upwards with ω
  calc
    ‖data.coeff i ω * inc ω‖ = ‖data.coeff i ω‖ * ‖inc ω‖ := by
      rw [norm_mul]
    _ ≤ c * ‖inc ω‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      simpa [c, Real.norm_eq_abs] using le_trans (hC ω) (le_abs_self C)
/-- Every predictable simple process is globally square-integrable on `Ω × [0,∞)` for a
probability measure. -/
theorem predictableSimpleProcess_memLp
    {ℱ : TimeFiltration} [IsProbabilityMeasure μ]
    (H : PredictableSimpleProcess ℱ) :
    MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ) := by
  classical
  rcases PredictableSimpleProcess.exists_representation H with ⟨data, hdata⟩
  let T : NNReal := data.times (Fin.last data.n)
  let S : Set (Ω × ℝ) := (Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) (T : ℝ)
  let f : Ω × ℝ → ℝ := processToTimeSpaceFun (data.toProcess : Process)
  have hS_meas : MeasurableSet S := by
    exact (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω)).prod measurableSet_Icc
  have hf_meas : Measurable f := by
    -- Proof comment: the chosen predictable-step representation is already predictable, so its
    -- time-space realization is measurable.
    simpa [f] using
      measurable_processToTimeSpaceFun_of_isPredictable
        data.isPredictable_toProcess
  have hf_indicator : S.indicator f = f := by
    funext x
    by_cases hx : x ∈ S
    · -- Proof comment: on the deterministic support strip, the indicator does nothing.
      simp [S, f, hx]
    · rcases x with ⟨ω, t⟩
      have ht_not : t ∉ Set.Icc (0 : ℝ) (T : ℝ) := by
        intro ht
        exact hx <| by simp [S, ht]
      have hzero : f (ω, t) = 0 := by
        -- Proof comment: outside `Ω × [0,T]`, the clamped time is either `0` or strictly after
        -- the final partition point, so the step process vanishes.
        dsimp [f]
        by_cases ht0 : 0 ≤ t
        · have hTlt : (T : ℝ) < t := by
            exact lt_of_not_ge (fun hle ↦ ht_not ⟨ht0, hle⟩)
          have hTlt' : T < t.toNNReal := by
            simpa [Real.toNNReal_of_nonneg ht0] using hTlt
          simpa [T] using data.toProcess_eq_zero_of_last_lt hTlt' ω
        · have ht_nonpos : t ≤ 0 := le_of_not_ge ht0
          have htoNN : t.toNNReal = 0 := Real.toNNReal_of_nonpos ht_nonpos
          simp [PredictableStepRepresentation.toProcess_apply, htoNN]
      simp [S, hx, hzero]
  have hRestrictEq :
      ((processMeasure μ).restrict S) =
        μ.prod (volume.restrict (Set.Icc (0 : ℝ) (T : ℝ))) := by
    -- Proof comment: this packages the time-strip restriction as a finite product measure.
    simpa [S, T] using processMeasure_restrict_eq_prod_Icc μ T
  have hMemRestrict :
      MemLp f (2 : ℝ≥0∞) ((processMeasure μ).restrict S) := by
    rw [hRestrictEq]
    haveI : IsFiniteMeasure (μ.prod (volume.restrict (Set.Icc (0 : ℝ) (T : ℝ)))) := by
      infer_instance
    -- Proof comment: on the finite strip, the representation is uniformly bounded by the sum of
    -- the coefficient bounds, so `MemLp` follows from the bounded-function criterion.
    refine MemLp.of_bound hf_meas.aestronglyMeasurable
      (∑ i, |Classical.choose (data.coeff_bounded i)|) ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      rcases x with ⟨ω, t⟩
      simpa [f, Real.norm_eq_abs] using
        predictableStepRepresentation_abs_le_sumCoeffBounds
          data t.toNNReal ω
  have hMemIndicator :
      MemLp (S.indicator f) (2 : ℝ≥0∞) (processMeasure μ) := by
    -- Proof comment: restricting the measure to the support strip is equivalent to inserting the
    -- strip indicator into the integrand.
    exact (memLp_indicator_iff_restrict hS_meas).2 hMemRestrict
  have hMemF : MemLp f (2 : ℝ≥0∞) (processMeasure μ) := by
    -- Proof comment: the indicator version equals the original function everywhere because the
    -- process already vanishes off the finite strip.
    exact MemLp.ae_eq (Filter.EventuallyEq.of_eq hf_indicator) hMemIndicator
  -- Proof comment: transfer the `MemLp` witness from the chosen representation back to the
  -- source-facing predictable simple process.
  simpa [f, hdata] using hMemF
/-- The terminal Brownian elementary integral of a predictable simple process belongs to
`L²(μ)`. -/
theorem brownianElementaryIntegralAtInfinity_memLp
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    MemLp (brownianElementaryIntegralAtInfinity W H) 2 μ := by
  classical
  rcases PredictableSimpleProcess.exists_representation H with ⟨data, hdata⟩
  have hSum :
      MemLp
        (fun ω ↦
          ∑ i : Fin data.n,
            data.coeff i ω * (W (data.times i.succ) ω - W (data.times i.castSucc) ω))
        2 μ := by
    let term : Fin data.n → Ω → ℝ := fun i ω ↦
      data.coeff i ω * (W (data.times i.succ) ω - W (data.times i.castSucc) ω)
    have hTerms : ∀ i ∈ (Finset.univ : Finset (Fin data.n)), MemLp (term i) 2 μ := by
      intro i _
      simpa [term] using predictableStepCoefficient_mul_brownianIncrement_memLp hW data i
    -- Proof comment: the terminal elementary integral is a finite sum of the one-block `L²`
    -- increment terms.
    simpa [term] using
      (MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin data.n)) hTerms)
  -- Proof comment: move from the chosen representation back to the source-facing terminal
  -- integral formula.
  rw [MeasureTheory.brownianElementaryIntegralAtInfinity_spec W H hdata]
  simpa [MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity_apply]
    using hSum
/-- Helper for Theorem 25.4: conditioning one predictable-step coefficient times its future
Brownian increment on an earlier filtration gives zero. -/
private theorem predictableStepRepresentation_incrementTerm_condExp_eq_zero_of_le_start
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (data : PredictableStepRepresentation ℱ) (i : Fin data.n) {s : NNReal}
    (hs : s ≤ data.times i.castSucc) :
    μ[(fun ω ↦
      data.coeff i ω * (W (data.times i.succ) ω - W (data.times i.castSucc) ω)) | ℱ s] =ᵐ[μ] 0 := by
  let inc : Ω → ℝ := fun ω ↦ W (data.times i.succ) ω - W (data.times i.castSucc) ω
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  have hStartEnd : data.times i.castSucc ≤ data.times i.succ := by
    -- Proof comment: each partition interval is ordered because the representation times are
    -- strictly increasing.
    exact le_of_lt (data.times_strictMono i.castSucc_lt_succ)
  have hInc_meas : Measurable inc := by
    -- Proof comment: the increment is a difference of measurable Brownian marginals.
    exact (hW.stronglyMeasurable (data.times i.succ)).measurable.sub
      (hW.stronglyMeasurable (data.times i.castSucc)).measurable
  have hCoeff_sm :
      StronglyMeasurable[ℱ (data.times i.castSucc)] (data.coeff i) :=
    -- Proof comment: the predictable coefficient is measurable at its left endpoint.
    (data.coeff_measurable i).stronglyMeasurable
  have hInc_sm :
      StronglyMeasurable[MeasurableSpace.comap inc (borel ℝ)] inc :=
    -- Proof comment: the increment is strongly measurable for its own pullback sigma-algebra.
    (comap_measurable inc).stronglyMeasurable
  have hInc_indep :
      Indep (MeasurableSpace.comap inc (borel ℝ)) (ℱ (data.times i.castSucc)) μ := by
    -- Proof comment: Brownian future increments are independent of the past filtration at their
    -- start time.
    simpa [inc] using hW_indep hStartEnd
  have hInc_mean_zero : ∫ ω, inc ω ∂μ = 0 := by
    -- Proof comment: every Brownian increment has centered Gaussian law.
    simpa [inc] using (brownianIncrement_hasLaw hW hStartEnd).integral_eq
  have hInc_int : Integrable inc μ := by
    -- Proof comment: Brownian increments belong to `L²`, hence to `L¹`.
    exact (brownianIncrement_memLp_two hW hStartEnd).integrable (by norm_num)
  have hTerm_int :
      Integrable (fun ω ↦ data.coeff i ω * inc ω) μ := by
    -- Proof comment: the coefficient times increment term is already available as an `L²`
    -- building block for the elementary integral.
    simpa [inc] using
      (predictableStepCoefficient_mul_brownianIncrement_memLp hW data i).integrable (by norm_num)
  have hZeroAtStart :
      μ[(fun ω ↦ data.coeff i ω * inc ω) | ℱ (data.times i.castSucc)] =ᵐ[μ] 0 := by
    have hInc_condExp_zero :
        μ[inc | ℱ (data.times i.castSucc)] =ᵐ[μ] 0 := by
      -- Proof comment: independence from `ℱ_{t_i}` collapses the conditional expectation to the
      -- scalar mean of the increment, which is `0`.
      refine (MeasureTheory.condExp_indep_eq
        hInc_meas.comap_le
        (ℱ.le _)
        hInc_sm
        hInc_indep).trans ?_
      exact Filter.Eventually.of_forall fun _ ↦ hInc_mean_zero
    -- Proof comment: pull the predictable coefficient out of the conditional expectation, then
    -- use the centered increment identity.
    calc
      μ[(fun ω ↦ data.coeff i ω * inc ω) | ℱ (data.times i.castSucc)]
          =ᵐ[μ] data.coeff i * μ[inc | ℱ (data.times i.castSucc)] := by
              exact condExp_mul_of_stronglyMeasurable_left hCoeff_sm hTerm_int hInc_int
      _ =ᵐ[μ] data.coeff i * 0 := by
            filter_upwards [hInc_condExp_zero] with ω hω
            simp [hω]
      _ =ᵐ[μ] 0 := by
            simp
  -- Route correction: the stable route is to compute the conditional expectation at the block
  -- start, then descend to the earlier filtration `ℱ s` by the tower property.
  have hPast_le : ℱ s ≤ ℱ (data.times i.castSucc) := ℱ.mono hs
  calc
    μ[(fun ω ↦ data.coeff i ω * inc ω) | ℱ s]
        =ᵐ[μ] μ[μ[(fun ω ↦ data.coeff i ω * inc ω) | ℱ (data.times i.castSucc)] | ℱ s] := by
          exact
            (condExp_condExp_of_le hPast_le (ℱ.le _)).symm
    _ =ᵐ[μ] μ[0 | ℱ s] := by
          exact condExp_congr_ae hZeroAtStart
    _ =ᵐ[μ] 0 := by
          simp
/-- Helper for Theorem 25.4: the `k`-th Brownian increment term of a predictable-step
representation, written with a nat index. -/
private def predictableStepRepresentationIncrementTermNat
    {ℱ : TimeFiltration} (data : PredictableStepRepresentation ℱ) (W : Process)
    (k : ℕ) (hk : k < data.n) : Ω → ℝ :=
  fun ω ↦
    let i : Fin data.n := ⟨k, hk⟩
    data.coeff i ω * (W (data.times i.succ) ω - W (data.times i.castSucc) ω)

/-- Helper for Theorem 25.4: the first `m` nat-indexed Brownian increment terms of a
predictable-step representation summed as one prefix process. -/
private def predictableStepRepresentationPrefixSum
    {ℱ : TimeFiltration} (data : PredictableStepRepresentation ℱ) (W : Process)
    (m : ℕ) : Ω → ℝ :=
  fun ω ↦
    Finset.sum (Finset.range m) fun k ↦
      if hk : k < data.n then
        predictableStepRepresentationIncrementTermNat data W k hk ω
      else 0

/-- Helper for Theorem 25.4: one nat-indexed Brownian increment term is square-integrable. -/
private theorem predictableStepRepresentationIncrementTermNat_memLp
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (data : PredictableStepRepresentation ℱ) {k : ℕ} (hk : k < data.n) :
    MemLp (predictableStepRepresentationIncrementTermNat data W k hk) 2 μ := by
  -- Proof comment: the nat-indexed summand is just the `Fin`-indexed one with the corresponding
  -- index bundled explicitly.
  simpa [predictableStepRepresentationIncrementTermNat] using
    (predictableStepCoefficient_mul_brownianIncrement_memLp
      hW data ⟨k, hk⟩)
/-- Helper for Theorem 25.4: each nat-indexed increment term is measurable at any later
filtration time after its terminal endpoint. -/
private theorem predictableStepRepresentationIncrementTermNat_stronglyMeasurable_of_le
    {ℱ : TimeFiltration} {W : Process}
    (hW_adapted : Adapted ℱ W)
    (data : PredictableStepRepresentation ℱ) {k : ℕ} (hk : k < data.n) {s : NNReal}
    (hs : data.times ⟨k + 1, Nat.succ_lt_succ hk⟩ ≤ s) :
    StronglyMeasurable[ℱ s] (predictableStepRepresentationIncrementTermNat data W k hk) := by
  let i : Fin data.n := ⟨k, hk⟩
  have hW_strAdapted : StronglyAdapted ℱ W := hW_adapted.stronglyAdapted
  have hStart_le : data.times i.castSucc ≤ s := by
    -- Proof comment: the left endpoint of the block lies before its right endpoint, hence also
    -- before any later conditioning time `s`.
    exact le_trans (le_of_lt (data.times_strictMono i.castSucc_lt_succ)) hs
  have hCoeff_sm : StronglyMeasurable[ℱ s] (data.coeff i) := by
    -- Proof comment: a coefficient measurable at the block start stays measurable for later
    -- filtration times by monotonicity.
    exact ((data.coeff_measurable i).stronglyMeasurable).mono (ℱ.mono hStart_le)
  have hLeft_sm : StronglyMeasurable[ℱ s] (W (data.times i.castSucc)) :=
    hW_strAdapted.stronglyMeasurable_le hStart_le
  have hRight_sm : StronglyMeasurable[ℱ s] (W (data.times i.succ)) :=
    hW_strAdapted.stronglyMeasurable_le hs
  -- Proof comment: products and differences preserve strong measurability in the relative
  -- filtration sigma-algebra.
  simpa [predictableStepRepresentationIncrementTermNat, i] using
    hCoeff_sm.mul (hRight_sm.sub hLeft_sm)
/-- Helper for Theorem 25.4: the `m`-term nat-indexed prefix sum is measurable at the `m`-th
partition time. -/
private theorem predictableStepRepresentationPrefixSum_stronglyMeasurable
    {ℱ : TimeFiltration} {W : Process}
    (hW_adapted : Adapted ℱ W)
    (data : PredictableStepRepresentation ℱ) {m : ℕ} (hm : m ≤ data.n) :
    StronglyMeasurable[ℱ (data.times ⟨m, Nat.lt_succ_of_le hm⟩)]
      (predictableStepRepresentationPrefixSum data W m) := by
  have hTerms :
      ∀ k ∈ Finset.range m,
        StronglyMeasurable[ℱ (data.times ⟨m, Nat.lt_succ_of_le hm⟩)]
          (fun ω ↦
            if hk : k < data.n then
              predictableStepRepresentationIncrementTermNat data W k hk ω
            else 0) := by
    intro k hkRange
    by_cases hkData : k < data.n
    · have hSucc_le_m : k + 1 ≤ m := Nat.succ_le_of_lt (Finset.mem_range.mp hkRange)
      have hEnd_le :
          data.times ⟨k + 1, Nat.succ_lt_succ hkData⟩ ≤
            data.times ⟨m, Nat.lt_succ_of_le hm⟩ := by
        exact data.times_strictMono.monotone <|
          show (⟨k + 1, Nat.succ_lt_succ hkData⟩ : Fin (data.n + 1)) ≤
              ⟨m, Nat.lt_succ_of_le hm⟩ by
            exact hSucc_le_m
      -- Proof comment: every summand appearing in the first `m` blocks is measurable by the time
      -- we reach the `m`-th partition point.
      simpa [hkData] using
        predictableStepRepresentationIncrementTermNat_stronglyMeasurable_of_le
          hW_adapted data hkData hEnd_le
    · simpa [hkData] using
        (stronglyMeasurable_zero :
          StronglyMeasurable[ℱ (data.times ⟨m, Nat.lt_succ_of_le hm⟩)] (0 : Ω → ℝ))
  -- Proof comment: the prefix process is a finite sum of the block terms already known to be
  -- measurable at the terminal block time.
  simpa [predictableStepRepresentationPrefixSum] using
    (Finset.stronglyMeasurable_fun_sum (Finset.range m) hTerms)
/-- Helper for Theorem 25.4: every nat-indexed prefix sum of Brownian increment terms is in
`L²(μ)`. -/
private theorem predictableStepRepresentationPrefixSum_memLp
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (data : PredictableStepRepresentation ℱ) (m : ℕ) :
    MemLp (predictableStepRepresentationPrefixSum data W m) 2 μ := by
  have hTerms :
      ∀ k ∈ Finset.range m,
        MemLp
          (fun ω ↦
            if hk : k < data.n then
              predictableStepRepresentationIncrementTermNat data W k hk ω
            else 0) 2 μ := by
    intro k hkRange
    by_cases hkData : k < data.n
    · -- Proof comment: active nat indices are exactly the one-block `L²` terms already proved.
      simpa [hkData] using
        predictableStepRepresentationIncrementTermNat_memLp
          hW data hkData
    · -- Proof comment: indices beyond the representation length contribute the zero function.
      simpa [hkData] using (MemLp.zero : MemLp (0 : Ω → ℝ) 2 μ)
  -- Proof comment: finite sums of `L²` functions stay in `L²`.
  simpa [predictableStepRepresentationPrefixSum] using
    (MeasureTheory.memLp_finset_sum (Finset.range m) hTerms)
/-- Helper for Theorem 25.4: the centered squared Brownian increment over `[s,t]` has zero
conditional expectation with respect to the past filtration `ℱ s`. -/
private theorem brownianIncrement_sq_sub_timeLag_condExp_eq_zero
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {s t : NNReal} (hst : s ≤ t) :
    μ[(fun ω ↦ (W t ω - W s ω) ^ 2 - ((t - s : NNReal) : ℝ)) | ℱ s] =ᵐ[μ] 0 := by
  let inc : Ω → ℝ := fun ω ↦ W t ω - W s ω
  let incSqComp : Ω → ℝ := fun ω ↦ inc ω ^ 2 - ((t - s : NNReal) : ℝ)
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  have hInc_meas : Measurable inc := by
    -- Proof comment: the Brownian increment is the difference of two measurable evaluations.
    exact (hW.stronglyMeasurable t).measurable.sub (hW.stronglyMeasurable s).measurable
  have hInc_mem : MemLp inc 2 μ := brownianIncrement_memLp_two hW hst
  have hIncSqComp_sm :
      StronglyMeasurable[MeasurableSpace.comap inc (borel ℝ)] incSqComp := by
    -- Proof comment: the compensated square is still a measurable function of the increment
    -- alone, so it lives on the same pullback sigma-algebra.
    exact ((comap_measurable inc).stronglyMeasurable.pow 2).sub stronglyMeasurable_const
  have hInc_indep :
      Indep (MeasurableSpace.comap inc (borel ℝ)) (ℱ s) μ := by
    -- Proof comment: use the explicit filtration-side Brownian increment independence input.
    simpa [inc] using hW_indep hst
  have hIncSqComp_mean_zero : ∫ ω, incSqComp ω ∂μ = 0 := by
    -- Proof comment: subtracting the deterministic lag removes exactly the second moment of the
    -- increment.
    rw [show incSqComp = fun ω ↦ inc ω ^ 2 - ((t - s : NNReal) : ℝ) by rfl]
    rw [integral_sub hInc_mem.integrable_sq (integrable_const _),
      brownianIncrement_sq_integral_eq_timeLag hW hst, integral_const, probReal_univ]
    simp
  -- Proof comment: conditional expectation onto `ℱ s` collapses to the mean because the centered
  -- square is measurable in the future increment alone and independent of the past.
  refine (MeasureTheory.condExp_indep_eq
    hInc_meas.comap_le
    (ℱ.le _)
    hIncSqComp_sm
    hInc_indep).trans ?_
  exact Filter.Eventually.of_forall fun _ ↦ hIncSqComp_mean_zero
/-- Helper for Theorem 25.4: conditioning the square of one Brownian increment term on its start
time keeps only the predictable coefficient square times the interval length. -/
private theorem predictableStepRepresentation_incrementSq_condExp_eq_coeffSq_timeLag
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (data : PredictableStepRepresentation ℱ) (i : Fin data.n) :
    μ[(fun ω ↦
      (data.coeff i ω * (W (data.times i.succ) ω - W (data.times i.castSucc) ω)) ^ 2) |
      ℱ (data.times i.castSucc)] =ᵐ[μ]
      fun ω ↦
        (data.coeff i ω) ^ 2 *
          ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := by
  let inc : Ω → ℝ := fun ω ↦ W (data.times i.succ) ω - W (data.times i.castSucc) ω
  let lag : ℝ := ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ)
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  have hStartEnd : data.times i.castSucc ≤ data.times i.succ := by
    -- Proof comment: the representation times are strictly increasing along each block.
    exact le_of_lt (data.times_strictMono i.castSucc_lt_succ)
  have hCoeffSq_sm :
      StronglyMeasurable[ℱ (data.times i.castSucc)] (fun ω ↦ (data.coeff i ω) ^ 2) := by
    -- Proof comment: the predictable coefficient is measurable at the block start, hence so is
    -- its square.
    exact ((data.coeff_measurable i).stronglyMeasurable).pow 2
  have hInc_mem : MemLp inc 2 μ := by
    -- Proof comment: one Brownian increment is always square-integrable.
    simpa [inc] using brownianIncrement_memLp_two hW hStartEnd
  have hProd_int :
      Integrable (fun ω ↦ (data.coeff i ω) ^ 2 * inc ω ^ 2) μ := by
    have hSquare_int :
        Integrable
          (fun ω ↦ (data.coeff i ω * (W (data.times i.succ) ω - W (data.times i.castSucc) ω)) ^ 2) μ := by
      -- Proof comment: the one-block increment term already lives in `L²`, so its square is
      -- integrable.
      exact
        (predictableStepCoefficient_mul_brownianIncrement_memLp
          hW data i).integrable_sq
    -- Proof comment: rewrite the square term to the coefficient-square times increment-square
    -- normal form expected by `condExp_mul_of_stronglyMeasurable_left`.
    refine hSquare_int.congr ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      dsimp [inc]
      ring
  have hIncSq_condExp :
      μ[(fun ω ↦ inc ω ^ 2) | ℱ (data.times i.castSucc)] =ᵐ[μ] fun _ ↦ lag := by
    have hCentered :
        μ[(fun ω ↦ inc ω ^ 2 - lag) | ℱ (data.times i.castSucc)] =ᵐ[μ] 0 := by
      -- Proof comment: first isolate the raw Brownian stochastic part, then import the generic
      -- centered-square conditional-expectation bridge.
      simpa [inc, lag] using
        brownianIncrement_sq_sub_timeLag_condExp_eq_zero
          hW hW_indep hStartEnd
    -- Proof comment: add back the deterministic lag after conditioning.
    calc
      μ[(fun ω ↦ inc ω ^ 2) | ℱ (data.times i.castSucc)]
          =ᵐ[μ] μ[(fun ω ↦ (inc ω ^ 2 - lag) + lag) | ℱ (data.times i.castSucc)] := by
              exact condExp_congr_ae <| Filter.Eventually.of_forall fun ω ↦ by ring
      _ =ᵐ[μ]
          μ[(fun ω ↦ inc ω ^ 2 - lag) | ℱ (data.times i.castSucc)] +
            μ[(fun _ : Ω ↦ lag) | ℱ (data.times i.castSucc)] := by
              exact condExp_add (hInc_mem.integrable_sq.sub (integrable_const _))
                (integrable_const _) (ℱ (data.times i.castSucc))
      _ =ᵐ[μ] 0 + fun _ : Ω ↦ lag := by
            simpa using hCentered.add
              (Filter.EventuallyEq.of_eq
                (condExp_const (ℱ.le (data.times i.castSucc)) lag))
      _ =ᵐ[μ] fun _ : Ω ↦ lag := by
            simp
  -- Proof comment: pull out the predictable coefficient square and replace the conditioned
  -- increment square by its deterministic lag.
  calc
    μ[(fun ω ↦ (data.coeff i ω * inc ω) ^ 2) | ℱ (data.times i.castSucc)]
        =ᵐ[μ] μ[(fun ω ↦ (data.coeff i ω) ^ 2 * inc ω ^ 2) | ℱ (data.times i.castSucc)] := by
          exact condExp_congr_ae <| Filter.Eventually.of_forall fun ω ↦ by ring
    _ =ᵐ[μ] (fun ω ↦ (data.coeff i ω) ^ 2) *
          μ[(fun ω ↦ inc ω ^ 2) | ℱ (data.times i.castSucc)] := by
            exact condExp_mul_of_stronglyMeasurable_left hCoeffSq_sm hProd_int
              hInc_mem.integrable_sq
    _ =ᵐ[μ] (fun ω ↦ (data.coeff i ω) ^ 2) * (fun _ : Ω ↦ lag) := by
          filter_upwards [hIncSq_condExp] with ω hω
          simp [hω]
    _ =ᵐ[μ] fun ω ↦ (data.coeff i ω) ^ 2 * lag := by
          exact Filter.Eventually.of_forall fun _ ↦ rfl
/-- Helper for Theorem 25.4: integrating one Brownian increment square yields the predictable
coefficient square times the interval length. -/
private theorem predictableStepRepresentation_incrementSq_integral_eq_coeffSq_timeLag
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (data : PredictableStepRepresentation ℱ) (i : Fin data.n) :
    ∫ ω,
        (data.coeff i ω * (W (data.times i.succ) ω - W (data.times i.castSucc) ω)) ^ 2 ∂μ =
      (∫ ω, (data.coeff i ω) ^ 2 ∂μ) *
        ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let f : Ω → ℝ := fun ω ↦
    (data.coeff i ω * (W (data.times i.succ) ω - W (data.times i.castSucc) ω)) ^ 2
  let lag : ℝ := ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ)
  have hCond :
      μ[f | ℱ (data.times i.castSucc)] =ᵐ[μ] fun ω ↦ (data.coeff i ω) ^ 2 * lag := by
    -- Proof comment: the conditional second moment of one block is exactly its predictable
    -- coefficient square times the interval length.
    simpa [f, lag] using
      predictableStepRepresentation_incrementSq_condExp_eq_coeffSq_timeLag
        hW hW_indep data i
  -- Proof comment: integrate the conditional-expectation identity to recover the scalar second
  -- moment formula.
  calc
    ∫ ω, f ω ∂μ = ∫ ω, μ[f | ℱ (data.times i.castSucc)] ω ∂μ := by
      symm
      exact integral_condExp (ℱ.le _)
    _ = ∫ ω, (data.coeff i ω) ^ 2 * lag ∂μ := by
          exact integral_congr_ae hCond
    _ = (∫ ω, (data.coeff i ω) ^ 2 ∂μ) * lag := by
          rw [integral_mul_const]
/-- Helper for Theorem 25.4: the prefix sum up to time `m` is orthogonal in `L²(μ)` to the next
Brownian increment term. -/
private theorem predictableStepRepresentation_prefixSum_mul_nextIncrement_integral_eq_zero
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (data : PredictableStepRepresentation ℱ) {m : ℕ} (hm : m < data.n) :
    ∫ ω,
        predictableStepRepresentationPrefixSum data W m ω *
          predictableStepRepresentationIncrementTermNat data W m hm ω ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  have hPrefix_sm :
      StronglyMeasurable[ℱ (data.times ⟨m, Nat.lt_succ_of_lt hm⟩)]
        (predictableStepRepresentationPrefixSum data W m) := by
    -- Proof comment: the `m`-term prefix only depends on increments up to the `m`-th block
    -- start, so it is measurable there.
    simpa using
      predictableStepRepresentationPrefixSum_stronglyMeasurable
        hW_adapted data (Nat.le_of_lt hm)
  have hPrefix_mem : MemLp (predictableStepRepresentationPrefixSum data W m) 2 μ :=
    predictableStepRepresentationPrefixSum_memLp hW data m
  have hNext_mem :
      MemLp (predictableStepRepresentationIncrementTermNat data W m hm) 2 μ :=
    predictableStepRepresentationIncrementTermNat_memLp
      hW data hm
  have hProd_int :
      Integrable
        (fun ω ↦
          predictableStepRepresentationPrefixSum data W m ω *
            predictableStepRepresentationIncrementTermNat data W m hm ω) μ :=
    hPrefix_mem.integrable_mul hNext_mem
  have hNext_int :
      Integrable (predictableStepRepresentationIncrementTermNat data W m hm) μ :=
    hNext_mem.integrable (by norm_num)
  have hNext_zero :
      μ[predictableStepRepresentationIncrementTermNat data W m hm |
          ℱ (data.times ⟨m, Nat.lt_succ_of_lt hm⟩)] =ᵐ[μ] 0 := by
    -- Proof comment: the next Brownian increment term has zero conditional expectation when we
    -- condition at its left endpoint.
    simpa [predictableStepRepresentationIncrementTermNat] using
      predictableStepRepresentation_incrementTerm_condExp_eq_zero_of_le_start
        hW hW_indep data ⟨m, hm⟩ le_rfl
  -- Proof comment: pull the measurable prefix outside the conditional expectation and then kill
  -- the future increment term by the zero-conditional-expectation lemma.
  calc
    ∫ ω,
        predictableStepRepresentationPrefixSum data W m ω *
          predictableStepRepresentationIncrementTermNat data W m hm ω ∂μ
        =
          ∫ ω,
            μ[(fun ω ↦
              predictableStepRepresentationPrefixSum data W m ω *
                predictableStepRepresentationIncrementTermNat data W m hm ω) |
              ℱ (data.times ⟨m, Nat.lt_succ_of_lt hm⟩)] ω ∂μ := by
            symm
            exact integral_condExp (ℱ.le _)
    _ = ∫ ω,
          predictableStepRepresentationPrefixSum data W m ω *
            μ[predictableStepRepresentationIncrementTermNat data W m hm |
              ℱ (data.times ⟨m, Nat.lt_succ_of_lt hm⟩)] ω ∂μ := by
          refine integral_congr_ae ?_
          exact condExp_mul_of_stronglyMeasurable_left hPrefix_sm hProd_int hNext_int
    _ = ∫ ω, predictableStepRepresentationPrefixSum data W m ω * 0 ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hNext_zero] with ω hω
          simp [hω]
    _ = 0 := by
          simp
/-- Helper for Theorem 25.4: the nat-indexed variance contribution of one predictable-step block.
-/
private def predictableStepRepresentationCoeffSqTimeLagNat
    (μ : Measure Ω) {ℱ : TimeFiltration} (data : PredictableStepRepresentation ℱ) (k : ℕ) : ℝ :=
  if hk : k < data.n then
    (∫ ω, (data.coeff ⟨k, hk⟩ ω) ^ 2 ∂μ) *
      ((data.times ⟨k + 1, Nat.succ_lt_succ hk⟩ - data.times ⟨k, Nat.lt_succ_of_lt hk⟩ :
        NNReal) : ℝ)
  else 0

/-- Helper for Theorem 25.4: adding the next increment term extends the nat-indexed prefix sum by
one step. -/
private theorem predictableStepRepresentationPrefixSum_succ
    {ℱ : TimeFiltration} {W : Process}
    (data : PredictableStepRepresentation ℱ) {m : ℕ} (hm : m < data.n) :
    predictableStepRepresentationPrefixSum data W (m + 1) =
      fun ω ↦
        predictableStepRepresentationPrefixSum data W m ω +
          predictableStepRepresentationIncrementTermNat data W m hm ω := by
  -- Proof comment: split the finite range sum at the new terminal index `m`.
  funext ω
  rw [predictableStepRepresentationPrefixSum, Finset.sum_range_succ]
  simp [predictableStepRepresentationPrefixSum, predictableStepRepresentationIncrementTermNat, hm]
/-- Helper for Theorem 25.4: the square integral of one nat-indexed increment term is exactly the
corresponding coefficient-square time-lag contribution. -/
private theorem predictableStepRepresentation_incrementSqIntegralNat_eq
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (data : PredictableStepRepresentation ℱ) {m : ℕ} (hm : m < data.n) :
    ∫ ω, (predictableStepRepresentationIncrementTermNat data W m hm ω) ^ 2 ∂μ =
      predictableStepRepresentationCoeffSqTimeLagNat μ data m := by
  -- Proof comment: rewrite the nat-indexed summand through the corresponding `Fin` index and
  -- then apply the one-block square-integral identity already proved for `Fin` indices.
  simpa [predictableStepRepresentationIncrementTermNat,
    predictableStepRepresentationCoeffSqTimeLagNat, hm] using
    predictableStepRepresentation_incrementSq_integral_eq_coeffSq_timeLag
      hW hW_indep data ⟨m, hm⟩
/-- Helper for Theorem 25.4: the square integral of the nat-indexed prefix sum is the sum of the
individual coefficient-square time-lag contributions. -/
private theorem predictableStepRepresentation_prefixSum_sq_integral_eq_sum
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (data : PredictableStepRepresentation ℱ) :
    ∀ {m : ℕ}, m ≤ data.n →
      ∫ ω, (predictableStepRepresentationPrefixSum data W m ω) ^ 2 ∂μ =
        Finset.sum (Finset.range m) fun k ↦
          predictableStepRepresentationCoeffSqTimeLagNat μ data k
    := by
  intro m hm
  induction m with
  | zero =>
      -- Proof comment: the empty prefix sum is the zero function, so both sides vanish.
      simp [predictableStepRepresentationPrefixSum]
  | succ m ih =>
      have hmn : m < data.n := Nat.lt_of_succ_le hm
      have hm_le : m ≤ data.n := Nat.le_of_lt hmn
      have hPrefix_mem : MemLp (predictableStepRepresentationPrefixSum data W m) 2 μ :=
        predictableStepRepresentationPrefixSum_memLp hW data m
      have hNext_mem :
          MemLp (predictableStepRepresentationIncrementTermNat data W m hmn) 2 μ :=
        predictableStepRepresentationIncrementTermNat_memLp
          hW data hmn
      have hProd_int :
          Integrable
            (fun ω ↦
              predictableStepRepresentationPrefixSum data W m ω *
                predictableStepRepresentationIncrementTermNat data W m hmn ω) μ :=
        hPrefix_mem.integrable_mul hNext_mem
      have hExpand :
          ∫ ω,
              (predictableStepRepresentationPrefixSum data W m ω +
                predictableStepRepresentationIncrementTermNat data W m hmn ω) ^ 2 ∂μ =
            ∫ ω,
              ((predictableStepRepresentationPrefixSum data W m ω) ^ 2 +
                  (2 : ℝ) *
                    (predictableStepRepresentationPrefixSum data W m ω *
                      predictableStepRepresentationIncrementTermNat data W m hmn ω)) +
                (predictableStepRepresentationIncrementTermNat data W m hmn ω) ^ 2 ∂μ := by
        -- Proof comment: expand the square of the updated prefix sum pointwise before
        -- integrating.
        refine integral_congr_ae ?_
        exact Filter.Eventually.of_forall fun ω ↦ by
          ring
      have hDecomp :
          ∫ ω, (predictableStepRepresentationPrefixSum data W (m + 1) ω) ^ 2 ∂μ =
            ∫ ω, (predictableStepRepresentationPrefixSum data W m ω) ^ 2 ∂μ +
              (2 : ℝ) *
                ∫ ω,
                  predictableStepRepresentationPrefixSum data W m ω *
                    predictableStepRepresentationIncrementTermNat data W m hmn ω ∂μ +
              ∫ ω, (predictableStepRepresentationIncrementTermNat data W m hmn ω) ^ 2 ∂μ := by
        -- Proof comment: after rewriting the successor prefix, integrate the algebraic square
        -- expansion term by term.
        rw [predictableStepRepresentationPrefixSum_succ data hmn]
        calc
          ∫ ω,
              (predictableStepRepresentationPrefixSum data W m ω +
                predictableStepRepresentationIncrementTermNat data W m hmn ω) ^ 2 ∂μ
              =
                ∫ ω,
                  ((predictableStepRepresentationPrefixSum data W m ω) ^ 2 +
                      (2 : ℝ) *
                        (predictableStepRepresentationPrefixSum data W m ω *
                          predictableStepRepresentationIncrementTermNat data W m hmn ω)) +
                    (predictableStepRepresentationIncrementTermNat data W m hmn ω) ^ 2 ∂μ := hExpand
          _ =
              ∫ ω,
                (predictableStepRepresentationPrefixSum data W m ω) ^ 2 +
                  (2 : ℝ) *
                    (predictableStepRepresentationPrefixSum data W m ω *
                      predictableStepRepresentationIncrementTermNat data W m hmn ω) ∂μ +
                ∫ ω, (predictableStepRepresentationIncrementTermNat data W m hmn ω) ^ 2 ∂μ := by
                  rw [integral_add]
                  · exact (hPrefix_mem.integrable_sq.add (hProd_int.const_mul (2 : ℝ)))
                  · exact hNext_mem.integrable_sq
          _ =
              (∫ ω, (predictableStepRepresentationPrefixSum data W m ω) ^ 2 ∂μ +
                ∫ ω,
                  (2 : ℝ) *
                    (predictableStepRepresentationPrefixSum data W m ω *
                      predictableStepRepresentationIncrementTermNat data W m hmn ω) ∂μ) +
                ∫ ω, (predictableStepRepresentationIncrementTermNat data W m hmn ω) ^ 2 ∂μ := by
                  congr 1
                  rw [integral_add]
                  · exact hPrefix_mem.integrable_sq
                  · exact hProd_int.const_mul (2 : ℝ)
          _ =
              (∫ ω, (predictableStepRepresentationPrefixSum data W m ω) ^ 2 ∂μ +
                (2 : ℝ) *
                  ∫ ω,
                    predictableStepRepresentationPrefixSum data W m ω *
                      predictableStepRepresentationIncrementTermNat data W m hmn ω ∂μ) +
                ∫ ω, (predictableStepRepresentationIncrementTermNat data W m hmn ω) ^ 2 ∂μ := by
                  congr 1
                  congr 1
                  rw [integral_const_mul]
      -- Proof comment: the induction step adds one new diagonal term, while the cross term
      -- disappears by the orthogonality lemma.
      calc
        ∫ ω, (predictableStepRepresentationPrefixSum data W (m + 1) ω) ^ 2 ∂μ
            = ∫ ω, (predictableStepRepresentationPrefixSum data W m ω) ^ 2 ∂μ +
                (2 : ℝ) *
                  ∫ ω,
                    predictableStepRepresentationPrefixSum data W m ω *
                      predictableStepRepresentationIncrementTermNat data W m hmn ω ∂μ +
                ∫ ω, (predictableStepRepresentationIncrementTermNat data W m hmn ω) ^ 2 ∂μ := hDecomp
        _ = ∫ ω, (predictableStepRepresentationPrefixSum data W m ω) ^ 2 ∂μ +
              ∫ ω, (predictableStepRepresentationIncrementTermNat data W m hmn ω) ^ 2 ∂μ := by
              rw [predictableStepRepresentation_prefixSum_mul_nextIncrement_integral_eq_zero
                hW hW_adapted hW_indep data hmn]
              ring
        _ = Finset.sum (Finset.range m) (fun k ↦ predictableStepRepresentationCoeffSqTimeLagNat μ data k) +
              predictableStepRepresentationCoeffSqTimeLagNat μ data m := by
                rw [ih hm_le,
                  predictableStepRepresentation_incrementSqIntegralNat_eq
                    hW hW_indep data hmn]
        _ = Finset.sum (Finset.range (m + 1))
              (fun k ↦ predictableStepRepresentationCoeffSqTimeLagNat μ data k) := by
                rw [Finset.sum_range_succ]
/-- Helper for Theorem 25.4: at the terminal index, the nat-indexed prefix sum is exactly the
representation-level terminal Brownian elementary integral. -/
private theorem predictableStepRepresentation_prefixSum_eq_brownianElementaryIntegralAtInfinity
    {ℱ : TimeFiltration} {W : Process}
    (data : PredictableStepRepresentation ℱ) :
    predictableStepRepresentationPrefixSum data W data.n =
      MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity data W := by
  -- Proof comment: at the terminal index every nat-indexed increment is present, so the prefix
  -- sum is exactly the defining finite increment sum of the terminal elementary integral.
  funext ω
  rw [predictableStepRepresentationPrefixSum,
    MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity_apply]
  have hsum :
      (∑ i : Fin data.n,
        data.coeff i ω * (W (data.times i.succ) ω - W (data.times i.castSucc) ω)) =
        Finset.sum (Finset.range data.n) fun k ↦
          if hk : k < data.n then
            predictableStepRepresentationIncrementTermNat data W k hk ω
          else 0 := by
    -- Proof comment: `Fin.sum_univ_eq_sum_range` rewrites the terminal `Fin`-sum as a nat-indexed
    -- range sum, and every range index carries exactly the corresponding nat increment term.
    simpa [predictableStepRepresentationIncrementTermNat] using
      (Fin.sum_univ_eq_sum_range
        (fun k : ℕ ↦
        if hk : k < data.n then
          predictableStepRepresentationIncrementTermNat data W k hk ω
        else 0)
        data.n)
  exact hsum.symm
/-- Helper for Theorem 25.4: the terminal Brownian elementary integral has square integral equal
to the textbook predictable simple process norm square. -/
private theorem brownianElementaryIntegralAtInfinity_sq_integral_eq_predictableSimpleProcessNormSq
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcess ℱ) :
    ∫ ω, (MeasureTheory.brownianElementaryIntegralAtInfinity W H ω) ^ 2 ∂μ =
      (letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
       predictableSimpleProcessNormSq μ H) := by
  classical
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  rcases PredictableSimpleProcess.exists_representation H with ⟨data, hdata⟩
  have hH_eq : H = data.toPredictableSimpleProcess := by
    -- Proof comment: the chosen predictable-step representation canonically recovers the source
    -- predictable simple process.
    apply Subtype.ext
    exact hdata.trans data.toPredictableSimpleProcess_coe.symm
  -- Proof comment: rewrite the source-facing terminal integral through the chosen representation,
  -- evaluate the representation-level second moment, and then compare with the textbook norm sum.
  calc
    ∫ ω, (MeasureTheory.brownianElementaryIntegralAtInfinity W H ω) ^ 2 ∂μ
        =
          ∫ ω,
            (MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
              data W ω) ^ 2 ∂μ := by
                rw [MeasureTheory.brownianElementaryIntegralAtInfinity_spec W H hdata]
    _ = ∫ ω, (predictableStepRepresentationPrefixSum data W data.n ω) ^ 2 ∂μ := by
          rw [predictableStepRepresentation_prefixSum_eq_brownianElementaryIntegralAtInfinity data]
    _ =
        Finset.sum (Finset.range data.n) (fun k ↦
          predictableStepRepresentationCoeffSqTimeLagNat μ data k) := by
            exact predictableStepRepresentation_prefixSum_sq_integral_eq_sum
              hW hW_adapted hW_indep data le_rfl
    _ =
        ∑ i : Fin data.n,
          (∫ ω, (data.coeff i ω) ^ 2 ∂μ) *
            ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := by
              simpa [predictableStepRepresentationCoeffSqTimeLagNat] using
                (Fin.sum_univ_eq_sum_range
                  (fun k : ℕ ↦ predictableStepRepresentationCoeffSqTimeLagNat μ data k)
                  data.n).symm
    _ = predictableSimpleProcessNormSq μ data.toPredictableSimpleProcess := by
          simpa using (predictableSimpleProcessNormSq_eq_sum μ data).symm
    _ = predictableSimpleProcessNormSq μ H := by
          simpa [hH_eq]
/-- Helper for Theorem 25.4: scaling the coefficient bounds of a predictable-step representation
produces another predictable-step representation. -/
private theorem smulPredictableStepRepresentation_coeff_bounded
    {ℱ : TimeFiltration} (a : ℝ) (data : PredictableStepRepresentation ℱ) :
    ∀ i, ∃ C : ℝ, ∀ ω, |a * data.coeff i ω| ≤ C := by
  intro i
  -- Proof comment: scale the original uniform coefficient bound by `|a|`.
  rcases data.coeff_bounded i with ⟨C, hC⟩
  refine ⟨|a| * |C|, ?_⟩
  intro ω
  calc
    |a * data.coeff i ω| = |a| * |data.coeff i ω| := by rw [abs_mul]
    _ ≤ |a| * |C| := by
          exact mul_le_mul_of_nonneg_left
            (le_trans (hC ω) (le_abs_self C))
            (abs_nonneg a)
/-- Helper for Theorem 25.4: scaling the coefficients preserves the required measurability for a
predictable-step representation. -/
private theorem smulPredictableStepRepresentation_coeff_measurable
    {ℱ : TimeFiltration} (a : ℝ) (data : PredictableStepRepresentation ℱ) :
    ∀ i, Measurable[ℱ (data.times i.castSucc)] (fun ω ↦ a * data.coeff i ω) := by
  intro i
  -- Proof comment: scalar multiplication preserves measurability of each predictable
  -- coefficient.
  exact measurable_const.mul (data.coeff_measurable i)
/-- Helper for Theorem 25.4: scaling every coefficient of a predictable-step representation gives
the scalar multiple of the represented process. -/
private def smulPredictableStepRepresentation
    {ℱ : TimeFiltration} (a : ℝ) (data : PredictableStepRepresentation ℱ) :
    PredictableStepRepresentation ℱ where
  n := data.n
  times := data.times
  coeff := fun i ω ↦ a * data.coeff i ω
  times_zero := data.times_zero
  times_strictMono := data.times_strictMono
  coeff_bounded := smulPredictableStepRepresentation_coeff_bounded a data
  coeff_measurable := smulPredictableStepRepresentation_coeff_measurable a data

/-- Helper for Theorem 25.4: the process encoded by the scaled predictable-step representation is
the scalar multiple of the original represented process. -/
private theorem smulPredictableStepRepresentation_toProcess
    {ℱ : TimeFiltration} (a : ℝ) (data : PredictableStepRepresentation ℱ) :
    (smulPredictableStepRepresentation a data).toProcess = a • data.toProcess := by
  -- Proof comment: unfold both processes and factor the scalar through the finite increment
  -- formula.
  funext t ω
  simp [smulPredictableStepRepresentation, PredictableStepRepresentation.toProcess_apply, mul_assoc,
    smul_eq_mul, Finset.mul_sum]
/-- Helper for Theorem 25.4: the terminal Brownian increment sum commutes with scalar
multiplication on a fixed predictable-step representation. -/
private theorem predictableStepRepresentation_brownianElementaryIntegralAtInfinity_smul
    {ℱ : TimeFiltration} {W : Process} (a : ℝ) (data : PredictableStepRepresentation ℱ) :
    MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
        (smulPredictableStepRepresentation a data) W =
      a • MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
        data W := by
  -- Proof comment: the terminal Brownian increment sum is linear in the predictable
  -- coefficients term by term.
  funext ω
  simp [MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity_apply,
    smulPredictableStepRepresentation, smul_eq_mul, mul_assoc, Finset.mul_sum]
/-- The source-facing terminal Brownian elementary integral commutes with scalar multiplication of
the predictable simple integrand. -/
theorem brownianElementaryIntegralAtInfinity_smul
    {ℱ : TimeFiltration} {W : Process}
    (a : ℝ) (H : PredictableSimpleProcess ℱ) :
    MeasureTheory.brownianElementaryIntegralAtInfinity W (a • H) =
      a • MeasureTheory.brownianElementaryIntegralAtInfinity W H := by
  classical
  -- Proof comment: choose a predictable-step representation of `H`, scale that representation,
  -- and compare both source-facing terminal integrals through the representation formulas.
  rcases PredictableSimpleProcess.exists_representation H with ⟨data, hdata⟩
  have hsmul :
      ((a • H : PredictableSimpleProcess ℱ) : Process) =
        (smulPredictableStepRepresentation a data).toProcess := by
    simpa [hdata, smulPredictableStepRepresentation_toProcess, Pi.smul_apply, smul_eq_mul]
  calc
    MeasureTheory.brownianElementaryIntegralAtInfinity W (a • H) =
        MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
          (smulPredictableStepRepresentation a data) W := by
            exact MeasureTheory.brownianElementaryIntegralAtInfinity_spec W (a • H) hsmul
    _ = a • MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
          data W :=
          predictableStepRepresentation_brownianElementaryIntegralAtInfinity_smul a data
    _ = a • MeasureTheory.brownianElementaryIntegralAtInfinity W H := by
          rw [MeasureTheory.brownianElementaryIntegralAtInfinity_spec W H hdata]
/-- Helper for Theorem 25.4: no point of a finite ordered set lies strictly between consecutive
values of its increasing `orderEmbOfFin` enumeration. -/
private theorem not_mem_Ioo_between_orderEmbOfFin_consecutive
    (B : Finset NNReal) {n : ℕ} (hB : B.card = n + 1) (i : Fin n) {x : NNReal} (hx : x ∈ B) :
    x ∉ Set.Ioo (B.orderEmbOfFin hB i.castSucc) (B.orderEmbOfFin hB i.succ) := by
  -- Proof comment: pull `x` back to its enumeration index and compare that index with the two
  -- consecutive refined indices.
  intro hxIoo
  let j : Fin (n + 1) := (B.orderIsoOfFin hB).symm ⟨x, hx⟩
  have hjx : B.orderEmbOfFin hB j = x := by
    change ((B.orderIsoOfFin hB) j : NNReal) = x
    have happly :
        ((B.orderIsoOfFin hB) ((B.orderIsoOfFin hB).symm ⟨x, hx⟩) : B) = ⟨x, hx⟩ :=
      (B.orderIsoOfFin hB).apply_symm_apply ⟨x, hx⟩
    simpa [j] using congrArg Subtype.val happly
  have hij_left : i.castSucc < j := by
    exact (B.orderEmbOfFin hB).lt_iff_lt.mp (by simpa [hjx] using hxIoo.1)
  have hij_right : j < i.succ := by
    exact (B.orderEmbOfFin hB).lt_iff_lt.mp (by simpa [hjx] using hxIoo.2)
  have hij_left_nat : (i : ℕ) < (j : ℕ) := by
    change ((i.castSucc : Fin (n + 1)) : ℕ) < (j : ℕ)
    exact hij_left
  have hij_right_nat : (j : ℕ) < (i : ℕ) + 1 := by
    change (j : ℕ) < ((i.succ : Fin (n + 1)) : ℕ)
    exact hij_right
  omega
/-- Helper for Theorem 25.4: every element of a finite ordered set is bounded above by the last
value of its increasing `orderEmbOfFin` enumeration. -/
private theorem le_orderEmbOfFin_last_of_mem
    (B : Finset NNReal) {n : ℕ} (hB : B.card = n + 1) {x : NNReal} (hx : x ∈ B) :
    x ≤ B.orderEmbOfFin hB (Fin.last n) := by
  -- Proof comment: compare the index of `x` with the maximal enumeration index.
  let j : Fin (n + 1) := (B.orderIsoOfFin hB).symm ⟨x, hx⟩
  have hjx : B.orderEmbOfFin hB j = x := by
    change ((B.orderIsoOfFin hB) j : NNReal) = x
    have happly :
        ((B.orderIsoOfFin hB) ((B.orderIsoOfFin hB).symm ⟨x, hx⟩) : B) = ⟨x, hx⟩ :=
      (B.orderIsoOfFin hB).apply_symm_apply ⟨x, hx⟩
    simpa [j] using congrArg Subtype.val happly
  exact hjx ▸ (B.orderEmbOfFin hB).monotone (Fin.le_last j)
/-- Helper for Theorem 25.4: a representation-level common-refinement formula simplifies at the
terminal time to the full increment sum on the refined grid. -/
private theorem predictableStepRepresentation_brownianElementaryIntegralAtInfinity_eq_commonRefinementSum
    {ℱ : TimeFiltration} {W : Process} (data : PredictableStepRepresentation ℱ)
    {nRef : ℕ} (times : Fin (nRef + 1) → NNReal) (hTimesStrictMono : StrictMono times)
    (coeff : Fin nRef → Ω → ℝ)
    (hCoeffEq :
      ∀ i : Fin nRef, ∀ ⦃s : NNReal⦄, s ∈ Set.Ioc (times i.castSucc) (times i.succ) →
        data.toProcess s = coeff i)
    (hEndpointMem :
      ∀ j : Fin (data.n + 1), ∃ k : Fin (nRef + 1), times k = data.times j)
    (hLastLe : data.times (Fin.last data.n) ≤ times (Fin.last nRef)) :
    MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity data W =
      fun ω ↦
        ∑ i : Fin nRef,
          coeff i ω * (W (times i.succ) ω - W (times i.castSucc) ω) := by
  have hStopped :=
    MeasureTheory.brownianElementaryIntegral_eq_commonRefinementSum
      W data times hTimesStrictMono coeff hCoeffEq hEndpointMem hLastLe
  -- Proof comment: evaluate the common-refinement stopped formula at the terminal refined time,
  -- where each truncation `min (times ·) (times last)` collapses to the corresponding endpoint.
  funext ω
  calc
    MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity data W ω
        =
          MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral data W
            (times (Fin.last nRef)) ω := by
              simpa using congrFun
                (MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral_eq_atInfinity
                  data W hLastLe).symm ω
    _ =
        (fun t ω ↦
          ∑ i : Fin nRef,
            coeff i ω *
              (W (min (times i.succ) t) ω - W (min (times i.castSucc) t) ω))
          (times (Fin.last nRef)) ω := by
            simpa using congrFun (congrFun hStopped (times (Fin.last nRef))) ω
    _ =
        ∑ i : Fin nRef,
          coeff i ω * (W (times i.succ) ω - W (times i.castSucc) ω) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [min_eq_left (hTimesStrictMono.monotone (Fin.le_last i.succ)),
              min_eq_left (hTimesStrictMono.monotone (Fin.le_last i.castSucc))]
/-- The source-facing terminal Brownian elementary integral is additive on predictable simple
integrands. -/
theorem brownianElementaryIntegralAtInfinity_add
    {ℱ : TimeFiltration} {W : Process}
    (H K : PredictableSimpleProcess ℱ) :
    MeasureTheory.brownianElementaryIntegralAtInfinity W (H + K) =
      MeasureTheory.brownianElementaryIntegralAtInfinity W H +
        MeasureTheory.brownianElementaryIntegralAtInfinity W K := by
  classical
  rcases PredictableSimpleProcess.exists_representation H with ⟨dataH, hdataH⟩
  rcases PredictableSimpleProcess.exists_representation K with ⟨dataK, hdataK⟩
  let B : Finset NNReal :=
    Finset.image dataH.times Finset.univ ∪ Finset.image dataK.times Finset.univ
  have hB0 : (0 : NNReal) ∈ B := by
    apply Finset.mem_union_left
    exact Finset.mem_image.2 ⟨0, Finset.mem_univ _, dataH.times_zero⟩
  have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨0, hB0⟩
  let nRef : ℕ := B.card - 1
  have hBcard : B.card = nRef + 1 := by
    have hcard : B.card = (B.card - 1) + 1 := by
      omega
    simpa [nRef] using hcard
  let times : Fin (nRef + 1) → NNReal := B.orderEmbOfFin hBcard
  have hTimesZero : times 0 = 0 := by
    have hBmin : B.min' (Finset.card_pos.mp hBpos) = 0 := by
      refine (Finset.min'_eq_iff B (Finset.card_pos.mp hBpos) 0).2 ?_
      constructor
      · exact hB0
      · intro b hb
        exact bot_le
    calc
      times 0 = B.min' (Finset.card_pos.mp hBpos) := by
        have hzero :=
          Finset.orderEmbOfFin_zero hBcard (by simpa [hBcard] using hBpos)
        simpa [times] using hzero
      _ = 0 := hBmin
  have hTimesStrictMono : StrictMono times := (B.orderEmbOfFin hBcard).strictMono
  have hStripH :
      ∀ i : Fin nRef,
        ∃ g : Ω → ℝ,
          Measurable[ℱ (times i.castSucc)] g ∧
          (∃ C : ℝ, ∀ ω, |g ω| ≤ C) ∧
          ∀ ⦃t : NNReal⦄, t ∈ Set.Ioc (times i.castSucc) (times i.succ) → dataH.toProcess t = g :=
      by
    intro i
    have huv : times i.castSucc < times i.succ := hTimesStrictMono i.castSucc_lt_succ
    have hboundary :
        ∀ j : Fin dataH.n, dataH.times j.succ ∉ Set.Ioo (times i.castSucc) (times i.succ) := by
      intro j
      apply not_mem_Ioo_between_orderEmbOfFin_consecutive B hBcard
      apply Finset.mem_union_left
      exact Finset.mem_image.2 ⟨j.succ, Finset.mem_univ _, rfl⟩
    -- Proof comment: on each refined strip, the old representation `dataH` is constant with one
    -- bounded predictable coefficient.
    exact dataH.exists_bddMeasurable_eq_on_Ioc_of_no_boundary huv hboundary
  have hStripK :
      ∀ i : Fin nRef,
        ∃ g : Ω → ℝ,
          Measurable[ℱ (times i.castSucc)] g ∧
          (∃ C : ℝ, ∀ ω, |g ω| ≤ C) ∧
          ∀ ⦃t : NNReal⦄, t ∈ Set.Ioc (times i.castSucc) (times i.succ) → dataK.toProcess t = g :=
      by
    intro i
    have huv : times i.castSucc < times i.succ := hTimesStrictMono i.castSucc_lt_succ
    have hboundary :
        ∀ j : Fin dataK.n, dataK.times j.succ ∉ Set.Ioo (times i.castSucc) (times i.succ) := by
      intro j
      apply not_mem_Ioo_between_orderEmbOfFin_consecutive B hBcard
      apply Finset.mem_union_right
      exact Finset.mem_image.2 ⟨j.succ, Finset.mem_univ _, rfl⟩
    -- Proof comment: the same stripwise decomposition works for `dataK`.
    exact dataK.exists_bddMeasurable_eq_on_Ioc_of_no_boundary huv hboundary
  let coeffH : Fin nRef → Ω → ℝ := fun i ↦ Classical.choose (hStripH i)
  let coeffK : Fin nRef → Ω → ℝ := fun i ↦ Classical.choose (hStripK i)
  have hCoeffH_meas : ∀ i : Fin nRef, Measurable[ℱ (times i.castSucc)] (coeffH i) := by
    intro i
    exact (Classical.choose_spec (hStripH i)).1
  have hCoeffK_meas : ∀ i : Fin nRef, Measurable[ℱ (times i.castSucc)] (coeffK i) := by
    intro i
    exact (Classical.choose_spec (hStripK i)).1
  have hCoeffH_bounded : ∀ i : Fin nRef, ∃ C : ℝ, ∀ ω, |coeffH i ω| ≤ C := by
    intro i
    exact (Classical.choose_spec (hStripH i)).2.1
  have hCoeffK_bounded : ∀ i : Fin nRef, ∃ C : ℝ, ∀ ω, |coeffK i ω| ≤ C := by
    intro i
    exact (Classical.choose_spec (hStripK i)).2.1
  have hCoeffH_eq :
      ∀ i : Fin nRef, ∀ ⦃t : NNReal⦄, t ∈ Set.Ioc (times i.castSucc) (times i.succ) →
        dataH.toProcess t = coeffH i := by
    intro i t ht
    exact (Classical.choose_spec (hStripH i)).2.2 ht
  have hCoeffK_eq :
      ∀ i : Fin nRef, ∀ ⦃t : NNReal⦄, t ∈ Set.Ioc (times i.castSucc) (times i.succ) →
        dataK.toProcess t = coeffK i := by
    intro i t ht
    exact (Classical.choose_spec (hStripK i)).2.2 ht
  let coeff : Fin nRef → Ω → ℝ := fun i ω ↦ coeffH i ω + coeffK i ω
  have hCoeffBounded : ∀ i, ∃ C : ℝ, ∀ ω, |coeff i ω| ≤ C := by
    intro i
    rcases hCoeffH_bounded i with ⟨CH, hCH⟩
    rcases hCoeffK_bounded i with ⟨CK, hCK⟩
    refine ⟨|CH| + |CK|, ?_⟩
    intro ω
    have hHle : |coeffH i ω| ≤ |CH| := le_trans (hCH ω) (le_abs_self CH)
    have hKle : |coeffK i ω| ≤ |CK| := le_trans (hCK ω) (le_abs_self CK)
    have htriangle : |coeffH i ω + coeffK i ω| ≤ |coeffH i ω| + |coeffK i ω| := by
      simpa [Real.norm_eq_abs] using norm_add_le (coeffH i ω) (coeffK i ω)
    calc
      |coeff i ω| = |coeffH i ω + coeffK i ω| := rfl
      _ ≤ |coeffH i ω| + |coeffK i ω| := htriangle
      _ ≤ |CH| + |CK| := add_le_add hHle hKle
  have hCoeffMeasurable : ∀ i, Measurable[ℱ (times i.castSucc)] (coeff i) := by
    intro i
    exact (hCoeffH_meas i).add (hCoeffK_meas i)
  let refined : PredictableStepRepresentation ℱ :=
    { n := nRef
      times := times
      coeff := coeff
      times_zero := hTimesZero
      times_strictMono := hTimesStrictMono
      coeff_bounded := hCoeffBounded
      coeff_measurable := hCoeffMeasurable }
  have hEndpointMemH :
      ∀ j : Fin (dataH.n + 1), ∃ k : Fin (nRef + 1), times k = dataH.times j := by
    intro j
    have hj : dataH.times j ∈ B := by
      apply Finset.mem_union_left
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    refine ⟨(B.orderIsoOfFin hBcard).symm ⟨dataH.times j, hj⟩, ?_⟩
    change ((B.orderIsoOfFin hBcard) ((B.orderIsoOfFin hBcard).symm ⟨dataH.times j, hj⟩) :
      NNReal) = dataH.times j
    simpa using congrArg Subtype.val
      ((B.orderIsoOfFin hBcard).apply_symm_apply ⟨dataH.times j, hj⟩)
  have hEndpointMemK :
      ∀ j : Fin (dataK.n + 1), ∃ k : Fin (nRef + 1), times k = dataK.times j := by
    intro j
    have hj : dataK.times j ∈ B := by
      apply Finset.mem_union_right
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    refine ⟨(B.orderIsoOfFin hBcard).symm ⟨dataK.times j, hj⟩, ?_⟩
    change ((B.orderIsoOfFin hBcard) ((B.orderIsoOfFin hBcard).symm ⟨dataK.times j, hj⟩) :
      NNReal) = dataK.times j
    simpa using congrArg Subtype.val
      ((B.orderIsoOfFin hBcard).apply_symm_apply ⟨dataK.times j, hj⟩)
  have hLastH_le : dataH.times (Fin.last dataH.n) ≤ times (Fin.last nRef) := by
    apply le_orderEmbOfFin_last_of_mem B hBcard
    apply Finset.mem_union_left
    exact Finset.mem_image.2 ⟨Fin.last dataH.n, Finset.mem_univ _, rfl⟩
  have hLastK_le : dataK.times (Fin.last dataK.n) ≤ times (Fin.last nRef) := by
    apply le_orderEmbOfFin_last_of_mem B hBcard
    apply Finset.mem_union_right
    exact Finset.mem_image.2 ⟨Fin.last dataK.n, Finset.mem_univ _, rfl⟩
  have hRefined :
      ((H + K : PredictableSimpleProcess ℱ) : Process) = refined.toProcess := by
    -- Proof comment: on each refined strip, `H + K` is constant with coefficient
    -- `coeffH i + coeffK i`, so the refined representation realizes the sum process.
    funext t ω
    by_cases hAfter : times (Fin.last nRef) < t
    · have hHzero : dataH.toProcess t ω = 0 := by
        exact dataH.toProcess_eq_zero_of_last_lt (lt_of_le_of_lt hLastH_le hAfter) ω
      have hKzero : dataK.toProcess t ω = 0 := by
        exact dataK.toProcess_eq_zero_of_last_lt (lt_of_le_of_lt hLastK_le hAfter) ω
      have hRefZero : refined.toProcess t ω = 0 := by
        exact refined.toProcess_eq_zero_of_last_lt hAfter ω
      simp [hdataH, hdataK, hHzero, hKzero, hRefZero]
    · by_cases ht0 : t = 0
      · subst ht0
        simp [hdataH, hdataK, PredictableStepRepresentation.toProcess_apply, refined, times, coeff]
      · have ht_pos : 0 < t := lt_of_le_of_ne bot_le (Ne.symm ht0)
        have ht_le_last : t ≤ times (Fin.last nRef) := le_of_not_gt hAfter
        obtain ⟨i, hti⟩ := refined.exists_mem_interval_of_pos_le_last ht_pos ht_le_last
        have hH_eq : dataH.toProcess t ω = coeffH i ω := by
          exact congrFun (hCoeffH_eq i hti) ω
        have hK_eq : dataK.toProcess t ω = coeffK i ω := by
          exact congrFun (hCoeffK_eq i hti) ω
        calc
          ((H + K : PredictableSimpleProcess ℱ) : Process) t ω
              = dataH.toProcess t ω + dataK.toProcess t ω := by
                  simp [hdataH, hdataK]
          _ = coeff i ω := by
                simp [coeff, hH_eq, hK_eq]
          _ = refined.toProcess t ω := by
                symm
                exact refined.toProcess_eq_coeff_of_mem_interval i hti ω
  have hIntegralAdd :
      MeasureTheory.brownianElementaryIntegralAtInfinity W (H + K) =
        MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
          refined W := by
    exact MeasureTheory.brownianElementaryIntegralAtInfinity_spec W (H + K) hRefined
  have hIntegralH :
      MeasureTheory.brownianElementaryIntegralAtInfinity W H =
        fun ω ↦
          ∑ i : Fin nRef,
            coeffH i ω * (W (times i.succ) ω - W (times i.castSucc) ω) := by
    rw [MeasureTheory.brownianElementaryIntegralAtInfinity_spec W H hdataH]
    exact predictableStepRepresentation_brownianElementaryIntegralAtInfinity_eq_commonRefinementSum
      dataH times hTimesStrictMono coeffH hCoeffH_eq hEndpointMemH hLastH_le
  have hIntegralK :
      MeasureTheory.brownianElementaryIntegralAtInfinity W K =
        fun ω ↦
          ∑ i : Fin nRef,
            coeffK i ω * (W (times i.succ) ω - W (times i.castSucc) ω) := by
    rw [MeasureTheory.brownianElementaryIntegralAtInfinity_spec W K hdataK]
    exact predictableStepRepresentation_brownianElementaryIntegralAtInfinity_eq_commonRefinementSum
      dataK times hTimesStrictMono coeffK hCoeffK_eq hEndpointMemK hLastK_le
  have hIntegralRefined :
      MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity refined W =
        fun ω ↦
          ∑ i : Fin nRef,
            coeff i ω * (W (times i.succ) ω - W (times i.castSucc) ω) := by
    exact predictableStepRepresentation_brownianElementaryIntegralAtInfinity_eq_commonRefinementSum
      refined times hTimesStrictMono coeff
      (by
        intro i t ht
        funext ω
        exact refined.toProcess_eq_coeff_of_mem_interval i ht ω)
      (by
        intro j
        exact ⟨j, rfl⟩)
      le_rfl
  calc
    MeasureTheory.brownianElementaryIntegralAtInfinity W (H + K)
        = MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
            refined W := hIntegralAdd
    _ =
        fun ω ↦
          ∑ i : Fin nRef,
            coeff i ω * (W (times i.succ) ω - W (times i.castSucc) ω) := hIntegralRefined
    _ =
        (fun ω ↦
          ∑ i : Fin nRef,
            coeffH i ω * (W (times i.succ) ω - W (times i.castSucc) ω)) +
          fun ω ↦
            ∑ i : Fin nRef,
              coeffK i ω * (W (times i.succ) ω - W (times i.castSucc) ω) := by
              funext ω
              simp [coeff, Finset.sum_add_distrib, add_mul]
    _ = MeasureTheory.brownianElementaryIntegralAtInfinity W H +
          MeasureTheory.brownianElementaryIntegralAtInfinity W K := by
          rw [hIntegralH, hIntegralK]
/-- Helper for Theorem 25.4: the squared textbook norm of a predictable simple process is the
single ambient `processMeasure μ` integral of its squared time-space representative. -/
private theorem predictableSimpleProcessNormSq_eq_processMeasureIntegralSq
    {ℱ : TimeFiltration} [IsProbabilityMeasure μ]
    (H : PredictableSimpleProcess ℱ) :
    predictableSimpleProcessNormSq μ H =
      ∫ x, (processToTimeSpaceFun (H : Process) x) ^ 2 ∂ processMeasure μ := by
  let hMem :
      MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ) :=
    predictableSimpleProcess_memLp  H
  have hSq_int :
      Integrable (fun x : Ω × ℝ ↦ (processToTimeSpaceFun (H : Process) x) ^ 2)
        (processMeasure μ) := by
    -- Proof comment: an `L²` time-space representative has integrable square.
    simpa using hMem.integrable_sq
  -- Proof comment: `processMeasure μ` is the product `μ ⊗ dt` on `Ω × [0,∞)`, so Fubini
  -- rewrites the ambient square integral exactly to the textbook iterated integral.
  rw [predictableSimpleProcessNormSq_def]
  simpa [processMeasure, processToTimeSpaceFun, Function.uncurry] using
    (integral_prod (fun x : Ω × ℝ ↦ (processToTimeSpaceFun (H : Process) x) ^ 2) hSq_int).symm
/-- Helper for Theorem 25.4: the squared norm of an `Lp` class at exponent `2` is the raw second
moment of any real-valued representative. -/
private theorem toLpNormSq_eq_integral_sq
    {α : Type*} [MeasurableSpace α] {P : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂P := by
  -- Proof comment: identify the `L²` norm with the square root of the second moment, then
  -- square back using nonnegativity of `∫ f²`.
  have hnorm : ‖hf.toLp f‖ = Real.sqrt (∫ x, (f x) ^ 2 ∂P) := by
    rw [Lp.norm_toLp]
    rw [show eLpNorm f 2 P = ENNReal.ofReal (Real.sqrt (∫ x, (f x) ^ 2 ∂P)) by
      simpa [Real.sqrt_eq_rpow, one_div, sq_abs] using
        (MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top hf)]
    rw [ENNReal.toReal_ofReal]
    positivity
  calc
    ‖hf.toLp f‖ ^ 2 = (Real.sqrt (∫ x, (f x) ^ 2 ∂P)) ^ 2 := by rw [hnorm]
    _ = ∫ x, (f x) ^ 2 ∂P := by
          rw [Real.sq_sqrt]
          positivity
/-- Helper for Theorem 25.4: the ambient `L²(μ ⊗ dt)` norm of a predictable simple process class
agrees at the square level with the textbook norm from Definition 25.2. -/
private theorem predictableSimpleProcessToL2_norm_sq_eq_predictableSimpleProcessNormSq
    {ℱ : TimeFiltration} [IsProbabilityMeasure μ]
    (H : PredictableSimpleProcess ℱ)
    (hH : MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ)) :
    ‖(predictableSimpleProcessToL2 H hH : predictableSimpleProcessL2 ℱ μ)‖ ^ 2 =
      predictableSimpleProcessNormSq μ H := by
  -- Proof comment: coerce the canonical owner back to the ambient `L²(μ ⊗ dt)` class, compute
  -- its squared norm by the raw second moment, and then rewrite that moment to the textbook
  -- process norm square.
  calc
    ‖(predictableSimpleProcessToL2 H hH : predictableSimpleProcessL2 ℱ μ)‖ ^ 2
        = ‖hH.toLp (processToTimeSpaceFun (H : Process))‖ ^ 2 := by
            rfl
    _ = ∫ x, (processToTimeSpaceFun (H : Process) x) ^ 2 ∂ processMeasure μ := by
          exact toLpNormSq_eq_integral_sq hH
    _ = predictableSimpleProcessNormSq μ H := by
          exact (predictableSimpleProcessNormSq_eq_processMeasureIntegralSq H).symm
private theorem brownianElementaryIntegralAtInfinityL2_congr
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {H K : PredictableSimpleProcess ℱ}
    {hH : MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ)}
    {hK : MemLp (processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞) (processMeasure μ)}
    (hHK :
      (predictableSimpleProcessToL2 H hH : Lp ℝ 2 (processMeasure μ)) =
        predictableSimpleProcessToL2 K hK) :
    (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H).toLp
        (brownianElementaryIntegralAtInfinity W H) =
      (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K).toLp
        (brownianElementaryIntegralAtInfinity W K) := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let hSub : MemLp
      (processToTimeSpaceFun (((H - K : PredictableSimpleProcess ℱ) : Process)))
      (2 : ℝ≥0∞) (processMeasure μ) := by
    simpa [processToTimeSpaceFun, sub_eq_add_neg, Pi.sub_apply] using hH.sub hK
  have hSubToL2Zero :
      (predictableSimpleProcessToL2 (H - K) hSub : Lp ℝ 2 (processMeasure μ)) = 0 := by
    calc
      (predictableSimpleProcessToL2 (H - K) hSub : Lp ℝ 2 (processMeasure μ))
          =
            (predictableSimpleProcessToL2 H hH : Lp ℝ 2 (processMeasure μ)) -
              predictableSimpleProcessToL2 K hK := by
                simpa [predictableSimpleProcessToL2, processToTimeSpaceFun, sub_eq_add_neg,
                  Pi.sub_apply] using MemLp.toLp_sub hH hK
      _ = 0 := by exact sub_eq_zero.mpr hHK
  have hSubEq : predictableSimpleProcessToL2 (H - K) hSub = 0 := by
    apply Subtype.ext
    exact hSubToL2Zero
  have hSourceNormSqZero :
      predictableSimpleProcessNormSq μ (H - K : PredictableSimpleProcess ℱ) = 0 := by
    calc
      predictableSimpleProcessNormSq μ (H - K : PredictableSimpleProcess ℱ)
          = ‖(predictableSimpleProcessToL2 (H - K) hSub : predictableSimpleProcessL2 ℱ μ)‖ ^ 2 :=
              (predictableSimpleProcessToL2_norm_sq_eq_predictableSimpleProcessNormSq
                (H - K) hSub).symm
      _ = 0 := by
            rw [hSubEq]
            simp
  have hIntegralZero :
      ∫ ω, (MeasureTheory.brownianElementaryIntegralAtInfinity W (H - K) ω) ^ 2 ∂μ = 0 := by
    rw [brownianElementaryIntegralAtInfinity_sq_integral_eq_predictableSimpleProcessNormSq
      hW hW_adapted hW_indep (H - K)]
    exact hSourceNormSqZero
  have hBrownianNormZero :
      ‖(brownianElementaryIntegralAtInfinity_memLp hW hW_adapted (H - K)).toLp
          (brownianElementaryIntegralAtInfinity W (H - K))‖ = 0 := by
    have hBrownianNormSq :
        ‖(brownianElementaryIntegralAtInfinity_memLp hW hW_adapted (H - K)).toLp
            (brownianElementaryIntegralAtInfinity W (H - K))‖ ^ 2 = 0 := by
      calc
        ‖(brownianElementaryIntegralAtInfinity_memLp hW hW_adapted (H - K)).toLp
            (brownianElementaryIntegralAtInfinity W (H - K))‖ ^ 2
            = ∫ ω, (brownianElementaryIntegralAtInfinity W (H - K) ω) ^ 2 ∂μ := by
                exact toLpNormSq_eq_integral_sq
                  (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted (H - K))
        _ = 0 := hIntegralZero
    exact sq_eq_zero_iff.mp hBrownianNormSq
  have hBrownianAeZero :
      MeasureTheory.brownianElementaryIntegralAtInfinity W (H - K) =ᵐ[μ] 0 := by
    have hENormZero :
        eLpNorm (brownianElementaryIntegralAtInfinity W (H - K)) 2 μ = 0 := by
      calc
        eLpNorm (brownianElementaryIntegralAtInfinity W (H - K)) 2 μ
            = ‖(brownianElementaryIntegralAtInfinity_memLp hW hW_adapted (H - K)).toLp
                (brownianElementaryIntegralAtInfinity W (H - K))‖ₑ := by
                  symm
                  exact Lp.enorm_toLp
                    (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted (H - K))
        _ = ENNReal.ofReal
              ‖(brownianElementaryIntegralAtInfinity_memLp hW hW_adapted (H - K)).toLp
                  (brownianElementaryIntegralAtInfinity W (H - K))‖ := by
                    rw [← ofReal_norm_eq_enorm]
        _ = 0 := by simp [hBrownianNormZero]
    exact
      (eLpNorm_eq_zero_iff
        (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted (H - K)).aestronglyMeasurable
        two_ne_zero).mp hENormZero
  have hIntegralSub :
      MeasureTheory.brownianElementaryIntegralAtInfinity W (H - K) =
        MeasureTheory.brownianElementaryIntegralAtInfinity W H -
          MeasureTheory.brownianElementaryIntegralAtInfinity W K := by
    -- Route correction: rewrite the terminal integral of `H - K` through the source-facing
    -- additivity and homogeneity lemmas before passing to `Lp`.
    have hNeg :
        MeasureTheory.brownianElementaryIntegralAtInfinity W (-K) =
          -MeasureTheory.brownianElementaryIntegralAtInfinity W K := by
      simpa using brownianElementaryIntegralAtInfinity_smul (-1 : ℝ) K
    have hAdd :
        MeasureTheory.brownianElementaryIntegralAtInfinity W (H + -K) =
          MeasureTheory.brownianElementaryIntegralAtInfinity W H +
            MeasureTheory.brownianElementaryIntegralAtInfinity W (-K) :=
      brownianElementaryIntegralAtInfinity_add H (-K)
    simpa [sub_eq_add_neg, hNeg] using hAdd
  have hDiffAeZero :
      (MeasureTheory.brownianElementaryIntegralAtInfinity W H -
        MeasureTheory.brownianElementaryIntegralAtInfinity W K) =ᵐ[μ] 0 := by
    simpa [hIntegralSub] using hBrownianAeZero
  apply Lp.ext
  filter_upwards
      [(brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H).coeFn_toLp,
        (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K).coeFn_toLp,
        hDiffAeZero] with ω hωH hωK hωDiff
  exact by
    have hωEq :
        MeasureTheory.brownianElementaryIntegralAtInfinity W H ω =
          MeasureTheory.brownianElementaryIntegralAtInfinity W K ω := by
      exact sub_eq_zero.mp hωDiff
    simpa [hωH, hωK] using hωEq
private theorem existsUnique_brownianElementaryIntegralAtInfinityL2
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : predictableSimpleProcessL2 ℱ μ) :
    ∃! I : Lp ℝ 2 μ,
      ∀ K : PredictableSimpleProcess ℱ,
        ∀ hK : MemLp (processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞) (processMeasure μ),
          (H : Lp ℝ 2 (processMeasure μ)) = predictableSimpleProcessToL2 K hK →
            I =
              (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K).toLp
                (brownianElementaryIntegralAtInfinity W K) := by
  classical
  rcases H.property with ⟨K₀, hK₀, hHK₀_raw⟩
  have hHK₀ :
      (H : Lp ℝ 2 (processMeasure μ)) = predictableSimpleProcessToL2 K₀ hK₀ := by
    simpa using hHK₀_raw
  refine ⟨(brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K₀).toLp
      (brownianElementaryIntegralAtInfinity W K₀), ?_, ?_⟩
  · intro K hK hHK
    -- Proof comment: any other concrete representative of the same `L²(μ ⊗ dt)` class gives the
    -- same terminal Brownian integral class by the quotient congruence lemma.
    exact brownianElementaryIntegralAtInfinityL2_congr
      hW hW_adapted hW_indep (hHK₀.symm.trans hHK)
  · intro I hI
    exact hI K₀ hK₀ hHK₀

private noncomputable def brownianElementaryIntegralAtInfinityL2Data
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : predictableSimpleProcessL2 ℱ μ) : Lp ℝ 2 μ :=
  Classical.choose <|
    ExistsUnique.exists
      (existsUnique_brownianElementaryIntegralAtInfinityL2 hW hW_adapted hW_indep H)

private theorem brownianElementaryIntegralAtInfinityL2Data_spec
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : predictableSimpleProcessL2 ℱ μ)
    {K : PredictableSimpleProcess ℱ}
    {hK : MemLp (processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞) (processMeasure μ)}
    (hHK :
      (H : Lp ℝ 2 (processMeasure μ)) = predictableSimpleProcessToL2 K hK) :
    brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep H =
      (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K).toLp
        (brownianElementaryIntegralAtInfinity W K) := by
  -- Proof comment: unfold the chosen owner and read off the specification from the underlying
  -- existence statement.
  simpa [brownianElementaryIntegralAtInfinityL2Data] using
    (Classical.choose_spec <|
      ExistsUnique.exists
        (existsUnique_brownianElementaryIntegralAtInfinityL2 hW hW_adapted hW_indep H))
      K hK hHK
private theorem brownianElementaryIntegralAtInfinityL2_map_add
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H K : predictableSimpleProcessL2 ℱ μ) :
    brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep (H + K) =
      brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep H +
        brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep K := by
  classical
  rcases H.property with ⟨H₀, hH₀, hRepH_raw⟩
  rcases K.property with ⟨K₀, hK₀, hRepK_raw⟩
  have hRepH :
      (H : Lp ℝ 2 (processMeasure μ)) = predictableSimpleProcessToL2 H₀ hH₀ := by
    simpa using hRepH_raw
  have hRepK :
      (K : Lp ℝ 2 (processMeasure μ)) = predictableSimpleProcessToL2 K₀ hK₀ := by
    simpa using hRepK_raw
  let hAdd : MemLp
      (processToTimeSpaceFun (((H₀ + K₀ : PredictableSimpleProcess ℱ) : Process)))
      (2 : ℝ≥0∞) (processMeasure μ) := by
    simpa [processToTimeSpaceFun] using hH₀.add hK₀
  have hRepAdd :
      ((H + K : predictableSimpleProcessL2 ℱ μ) : Lp ℝ 2 (processMeasure μ)) =
        predictableSimpleProcessToL2 (H₀ + K₀) hAdd := by
    calc
      ((H + K : predictableSimpleProcessL2 ℱ μ) : Lp ℝ 2 (processMeasure μ))
          = (H : Lp ℝ 2 (processMeasure μ)) + (K : Lp ℝ 2 (processMeasure μ)) := rfl
      _ = predictableSimpleProcessToL2 H₀ hH₀ + predictableSimpleProcessToL2 K₀ hK₀ := by
            rw [hRepH, hRepK]
      _ = predictableSimpleProcessToL2 (H₀ + K₀) hAdd := by
            symm
            simpa [predictableSimpleProcessToL2, processToTimeSpaceFun] using MemLp.toLp_add hH₀ hK₀
  calc
    brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep (H + K)
        =
          (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted (H₀ + K₀)).toLp
            (brownianElementaryIntegralAtInfinity W (H₀ + K₀)) := by
              exact brownianElementaryIntegralAtInfinityL2Data_spec
                hW hW_adapted hW_indep (H + K) hRepAdd
    _ =
        (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H₀).toLp
          (brownianElementaryIntegralAtInfinity W H₀) +
        (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K₀).toLp
          (brownianElementaryIntegralAtInfinity W K₀) := by
            simpa [brownianElementaryIntegralAtInfinity_add] using
              MemLp.toLp_add
                (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H₀)
                (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K₀)
    _ =
        brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep H +
          brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep K := by
            rw [brownianElementaryIntegralAtInfinityL2Data_spec
                  hW hW_adapted hW_indep H hRepH,
              brownianElementaryIntegralAtInfinityL2Data_spec
                  hW hW_adapted hW_indep K hRepK]
private theorem brownianElementaryIntegralAtInfinityL2_map_smul
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (a : ℝ) (H : predictableSimpleProcessL2 ℱ μ) :
    brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep (a • H) =
      a • brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep H := by
  classical
  rcases H.property with ⟨H₀, hH₀, hRepH_raw⟩
  have hRepH :
      (H : Lp ℝ 2 (processMeasure μ)) = predictableSimpleProcessToL2 H₀ hH₀ := by
    simpa using hRepH_raw
  let hSmul : MemLp
      (processToTimeSpaceFun (((a • H₀ : PredictableSimpleProcess ℱ) : Process)))
      (2 : ℝ≥0∞) (processMeasure μ) := by
    simpa [processToTimeSpaceFun] using hH₀.const_smul a
  have hRepSmul :
      ((a • H : predictableSimpleProcessL2 ℱ μ) : Lp ℝ 2 (processMeasure μ)) =
        predictableSimpleProcessToL2 (a • H₀) hSmul := by
    calc
      ((a • H : predictableSimpleProcessL2 ℱ μ) : Lp ℝ 2 (processMeasure μ))
          = a • (H : Lp ℝ 2 (processMeasure μ)) := rfl
      _ = a • predictableSimpleProcessToL2 H₀ hH₀ := by rw [hRepH]
      _ = predictableSimpleProcessToL2 (a • H₀) hSmul := by
            symm
            simpa [predictableSimpleProcessToL2, processToTimeSpaceFun] using
              MemLp.toLp_const_smul a hH₀
  calc
    brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep (a • H)
        =
          (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted (a • H₀)).toLp
            (brownianElementaryIntegralAtInfinity W (a • H₀)) := by
              exact brownianElementaryIntegralAtInfinityL2Data_spec
                hW hW_adapted hW_indep (a • H) hRepSmul
    _ = a • (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H₀).toLp
          (brownianElementaryIntegralAtInfinity W H₀) := by
            simpa [brownianElementaryIntegralAtInfinity_smul] using
              MemLp.toLp_const_smul a
                (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H₀)
    _ = a • brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep H := by
          rw [brownianElementaryIntegralAtInfinityL2Data_spec
            hW hW_adapted hW_indep H hRepH]
private theorem brownianElementaryIntegralAtInfinityL2_norm_map
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : predictableSimpleProcessL2 ℱ μ) :
    ‖brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep H‖ = ‖H‖ := by
  classical
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  rcases H.property with ⟨H₀, hH₀, hRepH_raw⟩
  have hRepH_sub :
      H = predictableSimpleProcessToL2 H₀ hH₀ := by
    apply Subtype.ext
    change (H : Lp ℝ 2 (processMeasure μ)) =
      (predictableSimpleProcessToL2 H₀ hH₀ : Lp ℝ 2 (processMeasure μ))
    exact hRepH_raw
  have hImageRep :
      brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep H =
        (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H₀).toLp
          (brownianElementaryIntegralAtInfinity W H₀) := by
    exact brownianElementaryIntegralAtInfinityL2Data_spec
      hW hW_adapted hW_indep H <| by
        change (H : Lp ℝ 2 (processMeasure μ)) =
          (predictableSimpleProcessToL2 H₀ hH₀ : Lp ℝ 2 (processMeasure μ))
        exact hRepH_raw
  have hDomainSq :
      ‖H‖ ^ 2 = predictableSimpleProcessNormSq μ H₀ := by
    rw [hRepH_sub]
    exact predictableSimpleProcessToL2_norm_sq_eq_predictableSimpleProcessNormSq
      H₀ hH₀
  have hCodomainSq :
      ‖brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep H‖ ^ 2 =
        predictableSimpleProcessNormSq μ H₀ := by
    rw [hImageRep]
    calc
      ‖(brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H₀).toLp
          (brownianElementaryIntegralAtInfinity W H₀)‖ ^ 2
          = ∫ ω, (brownianElementaryIntegralAtInfinity W H₀ ω) ^ 2 ∂μ := by
              exact toLpNormSq_eq_integral_sq
                (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H₀)
      _ = predictableSimpleProcessNormSq μ H₀ := by
            exact brownianElementaryIntegralAtInfinity_sq_integral_eq_predictableSimpleProcessNormSq
              hW hW_adapted hW_indep H₀
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 <| by
    calc
      ‖brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep H‖ ^ 2
          = predictableSimpleProcessNormSq μ H₀ := hCodomainSq
      _ = ‖H‖ ^ 2 := hDomainSq.symm
/-- The canonical linear isometric `L²` lift of the terminal Brownian elementary integral from
the upstream `L²(μ ⊗ dt)` image `predictableSimpleProcessL2 ℱ μ` of predictable simple
integrands for a Brownian motion whose increments are independent of the filtration `ℱ`. This is
the core/canonical owner for the isometry clause of the Brownian elementary integral theorem. -/
noncomputable def brownianElementaryIntegralAtInfinityLinearIsometry
    (ℱ : TimeFiltration) {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ) :
    predictableSimpleProcessL2 ℱ μ →ₗᵢ[ℝ] Lp ℝ 2 μ where
  toLinearMap :=
    { toFun := brownianElementaryIntegralAtInfinityL2Data hW hW_adapted hW_indep
      map_add' := brownianElementaryIntegralAtInfinityL2_map_add hW hW_adapted hW_indep
      map_smul' := brownianElementaryIntegralAtInfinityL2_map_smul hW hW_adapted hW_indep }
  norm_map' := brownianElementaryIntegralAtInfinityL2_norm_map hW hW_adapted hW_indep

/-- Applying the canonical `L²` linear isometry above to a concrete predictable
simple process recovers the `Lp` class of the source-facing terminal Brownian elementary integral
from Definition 25.3. -/
@[simp] theorem brownianElementaryIntegralAtInfinityLinearIsometry_apply
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcess ℱ) :
    brownianElementaryIntegralAtInfinityLinearIsometry ℱ hW hW_adapted hW_indep
        (letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
         predictableSimpleProcessToL2 H (predictableSimpleProcess_memLp H)) =
      (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H).toLp
        (brownianElementaryIntegralAtInfinity W H) := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  -- Proof comment: applying the canonical linear isometry to the concrete `L²` class of `H`
  -- specializes the defining uniqueness statement of `brownianElementaryIntegralAtInfinityL2Data`.
  simpa [brownianElementaryIntegralAtInfinityLinearIsometry] using
    (brownianElementaryIntegralAtInfinityL2Data_spec
      hW hW_adapted hW_indep
      (predictableSimpleProcessToL2 H (predictableSimpleProcess_memLp H))
      rfl)
/-- On a concrete predictable simple process, the canonical `L²` linear isometry above agrees
almost everywhere with the source-facing terminal Brownian elementary integral from
Definition 25.3. -/
theorem brownianElementaryIntegralAtInfinityLinearIsometry_ae_eq
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcess ℱ) :
    (brownianElementaryIntegralAtInfinityLinearIsometry ℱ hW hW_adapted hW_indep
      (letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
       predictableSimpleProcessToL2 H (predictableSimpleProcess_memLp H)) : Ω → ℝ) =ᵐ[μ]
        brownianElementaryIntegralAtInfinity W H := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  -- Proof comment: first rewrite the canonical owner back to the concrete `toLp` class of the
  -- source-facing terminal integral, then use the standard `MemLp.coeFn_toLp` representative fact.
  rw [brownianElementaryIntegralAtInfinityLinearIsometry_apply
    hW hW_adapted hW_indep H]
  exact (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H).coeFn_toLp
/-- Helper for Theorem 25.4: the representation-level stopped Brownian elementary integral is
strongly adapted to the underlying filtration. -/
private theorem predictableStepRepresentation_brownianElementaryIntegral_stronglyAdapted
    {ℱ : TimeFiltration} {W : Process}
    (hW_adapted : Adapted ℱ W)
    (data : PredictableStepRepresentation ℱ) :
    StronglyAdapted ℱ (MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral
      data W) := by
  intro t
  have hW_str : StronglyAdapted ℱ W := hW_adapted.stronglyAdapted
  have hTerms :
      ∀ i ∈ (Finset.univ : Finset (Fin data.n)),
        StronglyMeasurable[ℱ t]
          (fun ω ↦
            data.coeff i ω *
              (W (min (data.times i.succ) t) ω - W (min (data.times i.castSucc) t) ω)) := by
    intro i _
    by_cases hti : t ≤ data.times i.castSucc
    · have hti_succ : t ≤ data.times i.succ := by
        exact le_trans hti (le_of_lt (data.times_strictMono i.castSucc_lt_succ))
      have hZero :
          (fun ω ↦
            data.coeff i ω *
              (W (min (data.times i.succ) t) ω - W (min (data.times i.castSucc) t) ω)) = 0 := by
        -- Proof comment: before the left endpoint of the block, both truncations equal `t`, so
        -- the Brownian increment vanishes identically.
        funext ω
        simp [min_eq_right hti_succ, min_eq_right hti]
      simpa [hZero] using
        (stronglyMeasurable_zero : StronglyMeasurable[ℱ t] (0 : Ω → ℝ))
    · have hstart_lt : data.times i.castSucc < t := lt_of_not_ge hti
      have hCoeff_sm : StronglyMeasurable[ℱ t] (data.coeff i) := by
        -- Proof comment: once the block has started, the predictable coefficient is measurable
        -- at time `t` by filtration monotonicity.
        exact ((data.coeff_measurable i).stronglyMeasurable).mono
          (ℱ.mono (le_of_lt hstart_lt))
      have hRight_sm :
          StronglyMeasurable[ℱ t] (W (min (data.times i.succ) t)) :=
        hW_str.stronglyMeasurable_le (min_le_right _ _)
      have hLeft_sm :
          StronglyMeasurable[ℱ t] (W (min (data.times i.castSucc) t)) := by
        have hmin_left : min (data.times i.castSucc) t = data.times i.castSucc :=
          min_eq_left (le_of_lt hstart_lt)
        simpa [hmin_left] using hW_str.stronglyMeasurable_le (le_of_lt hstart_lt)
      -- Proof comment: the active block term is a product of the predictable coefficient with a
      -- difference of Brownian marginals already observable by time `t`.
      simpa using hCoeff_sm.mul (hRight_sm.sub hLeft_sm)
  -- Proof comment: the stopped integral is a finite sum of block terms that are all strongly
  -- measurable at time `t`.
  simpa [MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral_apply] using
    (Finset.stronglyMeasurable_fun_sum (Finset.univ : Finset (Fin data.n)) hTerms)

/-- Helper for Theorem 25.4: the source-facing stopped Brownian elementary integral is strongly
adapted to the filtration. -/
private theorem brownianElementaryIntegral_stronglyAdapted
    {ℱ : TimeFiltration} {W : Process}
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    StronglyAdapted ℱ (MeasureTheory.brownianElementaryIntegral W H) := by
  classical
  rcases PredictableSimpleProcess.exists_representation H with ⟨data, hdata⟩
  -- Proof comment: transfer strong adaptedness from any chosen predictable-step representation
  -- computing the stopped integral.
  rw [MeasureTheory.brownianElementaryIntegral_spec W H hdata]
  exact predictableStepRepresentation_brownianElementaryIntegral_stronglyAdapted
      hW_adapted data

/-- Helper for Theorem 25.4: a representation-level stopped Brownian elementary integral has
almost surely continuous sample paths. -/
private theorem predictableStepRepresentation_brownianElementaryIntegral_hasAlmostSurelyContinuousPaths
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (data : PredictableStepRepresentation ℱ) :
    HasAlmostSurelyContinuousPaths μ
      (MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral data W) := by
  -- Proof comment: on almost every Brownian sample path, each truncated increment
  -- `t ↦ W (min a t) - W (min b t)` is continuous, and finite sums preserve continuity.
  filter_upwards [hW.continuous_paths] with ω hω
  have hTerms :
      ∀ i : Fin data.n,
        Continuous (fun t : NNReal ↦
          data.coeff i ω *
            (W (min (data.times i.succ) t) ω - W (min (data.times i.castSucc) t) ω)) := by
    intro i
    have hRight :
        Continuous (fun t : NNReal ↦ W (min (data.times i.succ) t) ω) :=
      hω.comp (continuous_const.min continuous_id)
    have hLeft :
        Continuous (fun t : NNReal ↦ W (min (data.times i.castSucc) t) ω) :=
      hω.comp (continuous_const.min continuous_id)
    exact continuous_const.mul (hRight.sub hLeft)
  simpa [HasAlmostSurelyContinuousPaths, processPath,
    MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral_apply] using
    (continuous_finset_sum (Finset.univ : Finset (Fin data.n)) fun i _ ↦ hTerms i)

/-- Helper for Theorem 25.4: the source-facing stopped Brownian elementary integral has almost
surely continuous sample paths. -/
private theorem brownianElementaryIntegral_hasAlmostSurelyContinuousPaths_aux
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (H : PredictableSimpleProcess ℱ) :
    HasAlmostSurelyContinuousPaths μ (MeasureTheory.brownianElementaryIntegral W H) := by
  classical
  rcases PredictableSimpleProcess.exists_representation H with ⟨data, hdata⟩
  -- Proof comment: transfer continuity from any chosen predictable-step representation computing
  -- the stopped integral.
  rw [MeasureTheory.brownianElementaryIntegral_spec W H hdata]
  exact predictableStepRepresentation_brownianElementaryIntegral_hasAlmostSurelyContinuousPaths
      hW data
/-- Helper for Theorem 25.4: a bounded coefficient multiplied by one Brownian increment is an
`L²(μ)` random variable. -/
private theorem bounded_mul_brownianIncrement_memLp
    {W : Process} {G : Ω → ℝ} {s u : NNReal}
    (hW : IsBrownianMotion μ W) (hsu : s ≤ u)
    (hG_sm : StronglyMeasurable G)
    (hG_bdd : ∃ C : ℝ, ∀ ω, |G ω| ≤ C) :
    MemLp (fun ω ↦ G ω * (W u ω - W s ω)) 2 μ := by
  let inc : Ω → ℝ := fun ω ↦ W u ω - W s ω
  have hInc_mem : MemLp inc 2 μ := brownianIncrement_memLp_two hW hsu
  have hTerm_sm : AEStronglyMeasurable (fun ω ↦ G ω * inc ω) μ := by
    -- Proof comment: the bounded coefficient and the Brownian increment are both measurable, so
    -- their product is measurable as well.
    exact hG_sm.aestronglyMeasurable.mul hInc_mem.aestronglyMeasurable
  rcases hG_bdd with ⟨C, hC⟩
  -- Proof comment: absorb the bounded coefficient into a deterministic multiple of the Brownian
  -- increment.
  let c : ℝ := |C|
  refine @MemLp.of_le_mul Ω ℝ ℝ mΩ 2 μ _ _ (fun ω ↦ G ω * inc ω) inc c
    hInc_mem hTerm_sm ?_
  filter_upwards with ω
  calc
    ‖G ω * inc ω‖ = ‖G ω‖ * ‖inc ω‖ := by
      rw [norm_mul]
    _ ≤ c * ‖inc ω‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      simpa [c, Real.norm_eq_abs] using le_trans (hC ω) (le_abs_self C)

/-- Helper for Theorem 25.4: conditioning a bounded `ℱ s`-measurable coefficient times a future
Brownian increment onto `ℱ s` kills that increment. -/
private theorem predictableCoeff_mul_brownianFutureIncrement_condExp_eq_zero
    {ℱ : TimeFiltration} {W : Process} {G : Ω → ℝ} {s u : NNReal}
    (hW : IsBrownianMotion μ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (hsu : s ≤ u)
    (hG_sm : StronglyMeasurable[ℱ s] G)
    (hG_bdd : ∃ C : ℝ, ∀ ω, |G ω| ≤ C) :
    μ[(fun ω ↦ G ω * (W u ω - W s ω)) | ℱ s] =ᵐ[μ] 0 := by
  let inc : Ω → ℝ := fun ω ↦ W u ω - W s ω
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  letI : IsFiniteMeasure μ := by
    infer_instance
  have hInc_meas : Measurable inc := by
    -- Proof comment: a Brownian increment is the difference of two measurable Brownian
    -- marginals.
    exact (hW.stronglyMeasurable u).measurable.sub (hW.stronglyMeasurable s).measurable
  have hInc_sm :
      StronglyMeasurable[MeasurableSpace.comap inc (borel ℝ)] inc :=
    (comap_measurable inc).stronglyMeasurable
  have hInc_indep :
      Indep (MeasurableSpace.comap inc (borel ℝ)) (ℱ s) μ := by
    -- Proof comment: the Brownian future increment is independent of the past sigma-algebra at
    -- time `s`.
    simpa [inc] using hW_indep hsu
  have hInc_int : Integrable inc μ := by
    -- Proof comment: Brownian increments lie in `L²(μ)`, hence in `L¹(μ)`.
    exact (brownianIncrement_memLp_two hW hsu).integrable (by norm_num)
  have hProd_int :
      Integrable (fun ω ↦ G ω * inc ω) μ := by
    have hG_sm_ambient : StronglyMeasurable G := by
      simpa using (hG_sm.mono (ℱ.le s))
    exact
      (bounded_mul_brownianIncrement_memLp hW hsu hG_sm_ambient hG_bdd).integrable
        (by norm_num)
  have hInc_condExp_zero :
      μ[inc | ℱ s] =ᵐ[μ] 0 := by
    have hInc_mean_zero : ∫ ω, inc ω ∂μ = 0 := by
      -- Proof comment: every Brownian increment has centered Gaussian law.
      simpa [inc] using (brownianIncrement_hasLaw hW hsu).integral_eq
    refine (MeasureTheory.condExp_indep_eq
      hInc_meas.comap_le
      (ℱ.le _)
      hInc_sm
      hInc_indep).trans ?_
    exact Filter.Eventually.of_forall fun _ ↦ hInc_mean_zero
  rcases hG_bdd with ⟨C, hC⟩
  have hPull :
      μ[(fun ω ↦ G ω * inc ω) | ℱ s] =ᵐ[μ] G * μ[inc | ℱ s] := by
    -- Proof comment: pull the `ℱ s`-measurable coefficient out of the conditional expectation.
    refine condExp_stronglyMeasurable_mul_of_bound (ℱ.le s) hG_sm hInc_int |C| ?_
    filter_upwards with ω
    simpa [Real.norm_eq_abs] using le_trans (hC ω) (le_abs_self C)
  -- Proof comment: after the pull-out step, the centered future increment collapses to zero.
  calc
    μ[(fun ω ↦ G ω * inc ω) | ℱ s] =ᵐ[μ] G * μ[inc | ℱ s] := hPull
    _ =ᵐ[μ] G * 0 := by
          filter_upwards [hInc_condExp_zero] with ω hω
          simp [hω]
    _ =ᵐ[μ] 0 := by
          simp

/-- Helper for Theorem 25.4: conditioning one terminal representation block onto `ℱ t` truncates
that block at time `t`. -/
private theorem predictableStepRepresentation_incrementTerm_condExp_eq_truncation
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (data : PredictableStepRepresentation ℱ) (i : Fin data.n) (t : NNReal) :
    μ[(fun ω ↦
      data.coeff i ω * (W (data.times i.succ) ω - W (data.times i.castSucc) ω)) | ℱ t] =ᵐ[μ]
      (fun ω ↦
        data.coeff i ω *
          (W (min (data.times i.succ) t) ω - W (min (data.times i.castSucc) t) ω)) := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  letI : IsFiniteMeasure μ := by
    infer_instance
  let start : NNReal := data.times i.castSucc
  let stop : NNReal := data.times i.succ
  let terminalTerm : Ω → ℝ := fun ω ↦ data.coeff i ω * (W stop ω - W start ω)
  let truncatedTerm : Ω → ℝ := fun ω ↦
    data.coeff i ω * (W (min stop t) ω - W (min start t) ω)
  have hStartStop : start ≤ stop := by
    -- Proof comment: consecutive partition times are ordered by strict monotonicity.
    simpa [start, stop] using le_of_lt (data.times_strictMono i.castSucc_lt_succ)
  by_cases ht_start : t ≤ start
  · have hZero :
        μ[terminalTerm | ℱ t] =ᵐ[μ] 0 := by
      -- Proof comment: before the block starts, the whole terminal block has zero conditional
      -- expectation.
      simpa [terminalTerm, start, stop] using
        predictableStepRepresentation_incrementTerm_condExp_eq_zero_of_le_start
          hW hW_indep data i ht_start
    have hTruncZero : truncatedTerm = 0 := by
      -- Proof comment: before `start`, both truncation endpoints collapse to `t`.
      funext ω
      simp [truncatedTerm, min_eq_right ht_start, min_eq_right (le_trans ht_start hStartStop)]
    calc
      μ[terminalTerm | ℱ t] =ᵐ[μ] 0 := hZero
      _ =ᵐ[μ] truncatedTerm := Filter.EventuallyEq.of_eq hTruncZero.symm
  by_cases hstop_t : stop ≤ t
  · have hW_str : StronglyAdapted ℱ W := hW_adapted.stronglyAdapted
    have hCoeff_sm :
        StronglyMeasurable[ℱ t] (data.coeff i) := by
      -- Proof comment: once the block has ended, its predictable coefficient is already
      -- measurable at time `t`.
      exact ((data.coeff_measurable i).stronglyMeasurable).mono
        (ℱ.mono (le_trans hStartStop hstop_t))
    have hRight_sm : StronglyMeasurable[ℱ t] (W stop) :=
      hW_str.stronglyMeasurable_le hstop_t
    have hLeft_sm : StronglyMeasurable[ℱ t] (W start) :=
      hW_str.stronglyMeasurable_le (le_trans hStartStop hstop_t)
    have hTerm_int : Integrable terminalTerm μ := by
      -- Proof comment: one terminal block is square-integrable, hence integrable.
      simpa [terminalTerm, start, stop] using
        (predictableStepCoefficient_mul_brownianIncrement_memLp
          hW data i).integrable (by norm_num)
    have hCond :
        μ[terminalTerm | ℱ t] =ᵐ[μ] terminalTerm := by
      -- Proof comment: after the block has ended, the whole terminal block is already
      -- `ℱ t`-measurable.
      exact Filter.EventuallyEq.of_eq <|
        condExp_of_stronglyMeasurable (ℱ.le t) (hCoeff_sm.mul (hRight_sm.sub hLeft_sm))
          hTerm_int
    have hTruncEq : terminalTerm = truncatedTerm := by
      -- Proof comment: once `t` lies after the block endpoint, truncation does nothing.
      funext ω
      simp [terminalTerm, truncatedTerm, min_eq_left hstop_t,
        min_eq_left (le_trans hStartStop hstop_t)]
    calc
      μ[terminalTerm | ℱ t] =ᵐ[μ] terminalTerm := hCond
      _ =ᵐ[μ] truncatedTerm := Filter.EventuallyEq.of_eq hTruncEq
  have hstart_t : start < t := lt_of_not_ge ht_start
  have ht_stop : t < stop := lt_of_not_ge hstop_t
  let pastTerm : Ω → ℝ := fun ω ↦ data.coeff i ω * (W t ω - W start ω)
  let futureTerm : Ω → ℝ := fun ω ↦ data.coeff i ω * (W stop ω - W t ω)
  have hW_str : StronglyAdapted ℱ W := hW_adapted.stronglyAdapted
  have hCoeff_sm_t :
      StronglyMeasurable[ℱ t] (data.coeff i) := by
    -- Proof comment: in the middle-block case, the block has already started by time `t`.
    exact ((data.coeff_measurable i).stronglyMeasurable).mono (ℱ.mono (le_of_lt hstart_t))
  have hCoeff_sm_ambient : StronglyMeasurable (data.coeff i) := by
    simpa using (hCoeff_sm_t.mono (ℱ.le t))
  have hPast_sm :
      StronglyMeasurable[ℱ t] pastTerm := by
    -- Proof comment: the past piece only involves values of `W` up to time `t`, so it is
    -- already `ℱ t`-measurable.
    exact hCoeff_sm_t.mul
      ((hW_str.stronglyMeasurable_le le_rfl).sub
        (hW_str.stronglyMeasurable_le (le_of_lt hstart_t)))
  have hPast_int : Integrable pastTerm μ := by
    -- Proof comment: the past piece is a bounded coefficient times the Brownian increment over
    -- `[start,t]`.
    exact
      (bounded_mul_brownianIncrement_memLp
        hW (le_of_lt hstart_t) hCoeff_sm_ambient (data.coeff_bounded i)).integrable
        (by norm_num)
  have hFuture_int : Integrable futureTerm μ := by
    -- Proof comment: the future piece is the same bounded coefficient multiplied by the
    -- Brownian increment over `[t,stop]`.
    exact
      (bounded_mul_brownianIncrement_memLp
        hW (le_of_lt ht_stop) hCoeff_sm_ambient (data.coeff_bounded i)).integrable
        (by norm_num)
  have hFuture_zero :
      μ[futureTerm | ℱ t] =ᵐ[μ] 0 := by
    -- Proof comment: only the future Brownian increment remains after subtracting the truncated
    -- block, so conditioning at time `t` kills it.
    simpa [futureTerm, stop] using
      predictableCoeff_mul_brownianFutureIncrement_condExp_eq_zero
        hW hW_indep (le_of_lt ht_stop) hCoeff_sm_t (data.coeff_bounded i)
  have hSplit :
      terminalTerm = fun ω ↦ pastTerm ω + futureTerm ω := by
    -- Proof comment: split the terminal block increment at time `t`.
    funext ω
    dsimp [terminalTerm, pastTerm, futureTerm, start, stop]
    ring
  have hPastEq : pastTerm = truncatedTerm := by
    -- Proof comment: in the middle-block case, truncation keeps `start` and replaces `stop` by
    -- `t`.
    funext ω
    simp [pastTerm, truncatedTerm, min_eq_right (le_of_lt ht_stop),
      min_eq_left (le_of_lt hstart_t)]
  calc
    μ[terminalTerm | ℱ t] =ᵐ[μ] μ[(fun ω ↦ pastTerm ω + futureTerm ω) | ℱ t] := by
      exact condExp_congr_ae (Filter.EventuallyEq.of_eq hSplit)
    _ =ᵐ[μ] μ[pastTerm | ℱ t] + μ[futureTerm | ℱ t] := by
      exact condExp_add hPast_int hFuture_int (ℱ t)
    _ =ᵐ[μ] pastTerm + 0 := by
      refine (Filter.EventuallyEq.of_eq <|
        condExp_of_stronglyMeasurable (ℱ.le t) hPast_sm hPast_int).add hFuture_zero
    _ =ᵐ[μ] pastTerm := by
      simp
    _ =ᵐ[μ] truncatedTerm := Filter.EventuallyEq.of_eq hPastEq

/-- Helper for Theorem 25.4: each stopped representation-level Brownian integral is the
conditional expectation of its terminal value. -/
private theorem predictableStepRepresentation_brownianElementaryIntegral_condExp_terminal
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (data : PredictableStepRepresentation ℱ) (t : NNReal) :
    MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral data W t =ᵐ[μ]
      μ[MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity data W |
        ℱ t] := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  letI : IsFiniteMeasure μ := by
    infer_instance
  let terminalTerm : Fin data.n → Ω → ℝ := fun i ω ↦
    data.coeff i ω * (W (data.times i.succ) ω - W (data.times i.castSucc) ω)
  have hTerm_int :
      ∀ i ∈ (Finset.univ : Finset (Fin data.n)), Integrable (terminalTerm i) μ := by
    intro i _
    -- Proof comment: each terminal block is square-integrable by the one-block `L²` lemma.
    simpa [terminalTerm] using
      (predictableStepCoefficient_mul_brownianIncrement_memLp
        hW data i).integrable (by norm_num)
  -- Proof comment: expand the terminal sum, condition blockwise, and recognize the stopped
  -- representation formula at time `t`.
  refine (calc
    μ[MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity data W |
        ℱ t] =ᵐ[μ]
      μ[∑ i : Fin data.n, terminalTerm i | ℱ t] := by
        exact condExp_congr_ae <|
          show
            MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity data W
              =ᵐ[μ] (fun ω ↦ ∑ i : Fin data.n, terminalTerm i ω) from
            Filter.EventuallyEq.of_eq
              (MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity_apply
                data W)
    _ =ᵐ[μ] ∑ i : Fin data.n, μ[terminalTerm i | ℱ t] := by
          simpa [terminalTerm] using condExp_finset_sum hTerm_int (ℱ t)
    _ =ᵐ[μ]
        ∑ i : Fin data.n,
          (fun ω ↦
            data.coeff i ω *
              (W (min (data.times i.succ) t) ω - W (min (data.times i.castSucc) t) ω)) := by
            exact eventuallyEq_sum fun i _ ↦
              predictableStepRepresentation_incrementTerm_condExp_eq_truncation
                   hW hW_adapted hW_indep data i t
    _ =ᵐ[μ] MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral data W t := by
          exact Filter.EventuallyEq.of_eq <| by
            funext ω
            rfl
    ).symm

/-- Helper for Theorem 25.4: each stopped Brownian elementary integral is the conditional
expectation of the terminal Brownian elementary integral. -/
private theorem brownianElementaryIntegral_condExp_terminal
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcess ℱ) (t : NNReal) :
    MeasureTheory.brownianElementaryIntegral W H t =ᵐ[μ]
      μ[MeasureTheory.brownianElementaryIntegralAtInfinity W H | ℱ t] := by
  classical
  rcases PredictableSimpleProcess.exists_representation H with ⟨data, hdata⟩
  -- Proof comment: transport the representation-level conditional-expectation identity back to
  -- the source-facing predictable simple process.
  calc
    MeasureTheory.brownianElementaryIntegral W H t
        =ᵐ[μ] MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral data W t := by
          exact Filter.EventuallyEq.of_eq (MeasureTheory.brownianElementaryIntegral_spec W H hdata)
    _ =ᵐ[μ]
        μ[MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity data W |
          ℱ t] := by
            exact predictableStepRepresentation_brownianElementaryIntegral_condExp_terminal
                 hW hW_adapted hW_indep data t
    _ =ᵐ[μ] μ[MeasureTheory.brownianElementaryIntegralAtInfinity W H | ℱ t] := by
          exact condExp_congr_ae <|
            show
              MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
                  data W =ᵐ[μ]
                MeasureTheory.brownianElementaryIntegralAtInfinity W H from
              Filter.EventuallyEq.of_eq
                (MeasureTheory.brownianElementaryIntegralAtInfinity_spec W H hdata).symm

/-- Helper for Theorem 25.4: the source-facing terminal Brownian elementary integral satisfies the
textbook `L²` norm identity. -/
private theorem brownianElementaryIntegralAtInfinity_norm_eq_inline
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcess ℱ) :
    eLpNorm (brownianElementaryIntegralAtInfinity W H) 2 μ =
      ENNReal.ofReal
        (letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
         predictableSimpleProcessNorm μ H) := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let hIntegralMem : MemLp (brownianElementaryIntegralAtInfinity W H) 2 μ :=
    brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H
  have hNormSq :
      ‖hIntegralMem.toLp (brownianElementaryIntegralAtInfinity W H)‖ ^ 2 =
        predictableSimpleProcessNormSq μ H := by
    -- Proof comment: the `L²` norm square of the terminal integral is its second moment, which
    -- the Itô isometry identifies with the textbook predictable-simple-process norm square.
    calc
      ‖hIntegralMem.toLp (brownianElementaryIntegralAtInfinity W H)‖ ^ 2
          = ∫ ω, (brownianElementaryIntegralAtInfinity W H ω) ^ 2 ∂μ := by
              exact toLpNormSq_eq_integral_sq hIntegralMem
      _ = predictableSimpleProcessNormSq μ H := by
            exact brownianElementaryIntegralAtInfinity_sq_integral_eq_predictableSimpleProcessNormSq
              hW hW_adapted hW_indep H
  have hNorm :
      ‖hIntegralMem.toLp (brownianElementaryIntegralAtInfinity W H)‖ =
        predictableSimpleProcessNorm μ H := by
    -- Proof comment: both sides are nonnegative, so the square identity upgrades to the norm
    -- identity directly.
    have hNormTarget :
        (predictableSimpleProcessNorm μ H) ^ 2 = predictableSimpleProcessNormSq μ H := by
      rw [predictableSimpleProcessNorm, predictableSimpleProcessNormSq, Real.sq_sqrt]
      positivity
    refine (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 ?_
    calc
      ‖hIntegralMem.toLp (brownianElementaryIntegralAtInfinity W H)‖ ^ 2
          = predictableSimpleProcessNormSq μ H := hNormSq
      _ = (predictableSimpleProcessNorm μ H) ^ 2 := hNormTarget.symm
  calc
    eLpNorm (brownianElementaryIntegralAtInfinity W H) 2 μ
        = ‖hIntegralMem.toLp (brownianElementaryIntegralAtInfinity W H)‖ₑ := by
            symm
            exact Lp.enorm_toLp hIntegralMem
    _ = ENNReal.ofReal ‖hIntegralMem.toLp (brownianElementaryIntegralAtInfinity W H)‖ := by
          rw [← ofReal_norm_eq_enorm]
    _ = ENNReal.ofReal (predictableSimpleProcessNorm μ H) := by
          rw [hNorm]

/-- Helper for Theorem 25.4: the stopped Brownian elementary integral is a martingale because it
is the conditional-expectation martingale of its terminal value. -/
private theorem brownianElementaryIntegral_martingale_aux
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcess ℱ) :
    Martingale (brownianElementaryIntegral W H) ℱ μ := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  letI : IsFiniteMeasure μ := by
    infer_instance
  let terminal : Ω → ℝ := brownianElementaryIntegralAtInfinity W H
  -- Proof comment: use the earlier strong-adaptedness owner for measurability, then identify
  -- each stopped value with the conditional expectation of the fixed terminal random variable and
  -- apply the tower property.
  refine ⟨brownianElementaryIntegral_stronglyAdapted hW_adapted H, ?_⟩
  intro s t hst
  calc
    μ[brownianElementaryIntegral W H t | ℱ s] =ᵐ[μ] μ[μ[terminal | ℱ t] | ℱ s] := by
      exact condExp_congr_ae (brownianElementaryIntegral_condExp_terminal
        hW hW_adapted hW_indep H t)
    _ =ᵐ[μ] μ[terminal | ℱ s] := by
      exact condExp_condExp_of_le (ℱ.mono hst) (ℱ.le t)
    _ =ᵐ[μ] brownianElementaryIntegral W H s := by
      exact (brownianElementaryIntegral_condExp_terminal hW hW_adapted hW_indep H s).symm

/-- Helper for Theorem 25.4: each stopped Brownian elementary integral slice has `L²` norm
bounded by the terminal Brownian elementary integral. -/
private theorem brownianElementaryIntegral_eLpNorm_le_terminal
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcess ℱ) (t : NNReal) :
    eLpNorm (brownianElementaryIntegral W H t) 2 μ ≤
      eLpNorm (brownianElementaryIntegralAtInfinity W H) 2 μ := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let terminal : Ω → ℝ := brownianElementaryIntegralAtInfinity W H
  have hterminal_mem : MemLp terminal 2 μ :=
    brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H
  -- Proof comment: rewrite the stopped slice as a conditional expectation of the terminal value
  -- and apply the `L²` contraction of conditional expectation.
  calc
    eLpNorm (brownianElementaryIntegral W H t) 2 μ = eLpNorm (μ[terminal | ℱ t]) 2 μ := by
      exact eLpNorm_congr_ae (brownianElementaryIntegral_condExp_terminal
        hW hW_adapted hW_indep H t)
    _ ≤ eLpNorm terminal 2 μ :=
      MeasureTheory.condExp_eLpNorm_le hterminal_mem (ℱ.le t)

/-- Helper for Theorem 25.4: the stopped Brownian elementary integral process is a continuous
`L²`-bounded martingale. -/
private theorem brownianElementaryIntegral_l2BoundedContinuousMartingale_aux
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcess ℱ) :
    Martingale (brownianElementaryIntegral W H) ℱ μ ∧
      HasAlmostSurelyContinuousPaths μ (brownianElementaryIntegral W H) ∧
      ∃ C : ℝ≥0, ∀ t : NNReal, eLpNorm (brownianElementaryIntegral W H t) 2 μ ≤ (C : ℝ≥0∞) := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let terminal : Ω → ℝ := brownianElementaryIntegralAtInfinity W H
  have hterminal_mem : MemLp terminal 2 μ :=
    brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H
  have hterminal_ne_top : eLpNorm terminal 2 μ ≠ ∞ := hterminal_mem.eLpNorm_ne_top
  let C : ℝ≥0 := ⟨(eLpNorm terminal 2 μ).toReal, ENNReal.toReal_nonneg⟩
  have hC : eLpNorm terminal 2 μ = (C : ℝ≥0∞) := by
    simpa [C] using (ENNReal.coe_toNNReal hterminal_ne_top).symm
  refine ⟨brownianElementaryIntegral_martingale_aux hW hW_adapted hW_indep H,
    brownianElementaryIntegral_hasAlmostSurelyContinuousPaths_aux hW H, ?_⟩
  -- Proof comment: take the deterministic `L²` norm of the terminal value as the uniform bound
  -- constant and combine the terminal-conditional-expectation identity with `L²` contraction.
  refine ⟨C, ?_⟩
  intro t
  calc
    eLpNorm (brownianElementaryIntegral W H t) 2 μ ≤ eLpNorm terminal 2 μ :=
      brownianElementaryIntegral_eLpNorm_le_terminal hW hW_adapted hW_indep H t
    _ = (C : ℝ≥0∞) := hC
-- Semantic recall note: `lean_leansearch` only surfaced generic linear-isometry/integral owners,
-- so the Brownian-specific first clause stays project-local with canonical owner
-- `predictableSimpleProcessL2 ℱ μ →ₗᵢ[ℝ] Lp ℝ 2 μ`; the public `add`/`smul`/`norm_eq`
-- companions below keep the textbook source-facing map visible on predictable simple processes.
-- Proof sketch: apply the linear isometry above to the canonical `L²(μ ⊗ dt)`
-- class of `H` and rewrite both sides back to the source-facing formulas from Definitions 25.2
-- and 25.3.
/-- Theorem 25.4: the source terminal Brownian elementary integral is linear and isometric on
predictable simple integrands, and for every predictable simple process the stopped Brownian
elementary integral is a continuous `𝓕`-martingale that is uniformly bounded in `L²(μ)`. The
canonical owner `brownianElementaryIntegralAtInfinityLinearIsometry` packages the same linear
isometry on `predictableSimpleProcessL2 ℱ μ`, while the labeled theorem keeps the source-facing
additivity, homogeneity, and norm-identity formulation. In this project,
`IsBrownianMotion μ W` only remembers the law-side Brownian data, so the source
Brownian/filtration setup is formalized by adding the explicit filtration-side
increment-independence premise for `W`. -/
theorem brownianElementaryIntegral_isometry_and_isL2BoundedContinuousMartingale
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ) :
    (∀ H K : PredictableSimpleProcess ℱ,
      brownianElementaryIntegralAtInfinity W (H + K) =
        brownianElementaryIntegralAtInfinity W H +
          brownianElementaryIntegralAtInfinity W K) ∧
      (∀ (a : ℝ) (H : PredictableSimpleProcess ℱ),
        brownianElementaryIntegralAtInfinity W (a • H) =
          a • brownianElementaryIntegralAtInfinity W H) ∧
      (∀ H : PredictableSimpleProcess ℱ,
        eLpNorm (brownianElementaryIntegralAtInfinity W H) 2 μ =
          ENNReal.ofReal
            (letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
             predictableSimpleProcessNorm μ H)) ∧
      ∀ H : PredictableSimpleProcess ℱ,
        Martingale (brownianElementaryIntegral W H) ℱ μ ∧
          HasAlmostSurelyContinuousPaths μ (brownianElementaryIntegral W H) ∧
          ∃ C : ℝ≥0,
            ∀ t : NNReal, eLpNorm (brownianElementaryIntegral W H t) 2 μ ≤ (C : ℝ≥0∞) := by
  -- Proof comment: the first two clauses are the already-proved source-facing linearity owners,
  -- the third clause is the norm identity companion proved just above, and the final clause is
  -- the packaged martingale/continuity/`L²`-boundedness helper.
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro H K
    exact brownianElementaryIntegralAtInfinity_add H K
  · intro a H
    exact brownianElementaryIntegralAtInfinity_smul a H
  · intro H
    exact brownianElementaryIntegralAtInfinity_norm_eq_inline hW hW_adapted hW_indep H
  · intro H
    exact brownianElementaryIntegral_l2BoundedContinuousMartingale_aux
      hW hW_adapted hW_indep H
/-- A source-facing norm-identity companion to the Brownian elementary integral linear isometry:
the terminal Brownian elementary integral from
Definition 25.3 preserves the textbook `L²(μ ⊗ dt)` norm from Definition 25.2 on predictable
simple processes. In this project, `IsBrownianMotion μ W` only remembers the law-side Brownian
data, so the source Brownian/filtration setup is formalized by adding the explicit filtration-side
increment-independence premise for `W`. -/
theorem brownianElementaryIntegralAtInfinity_norm_eq
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcess ℱ) :
    eLpNorm (brownianElementaryIntegralAtInfinity W H) 2 μ =
      ENNReal.ofReal
        (letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
         predictableSimpleProcessNorm μ H) := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let hIntegralMem : MemLp (brownianElementaryIntegralAtInfinity W H) 2 μ :=
    brownianElementaryIntegralAtInfinity_memLp  hW hW_adapted H
  have hNormSq :
      ‖hIntegralMem.toLp (brownianElementaryIntegralAtInfinity W H)‖ ^ 2 =
        predictableSimpleProcessNormSq μ H := by
    -- Proof comment: the `L²` norm square of the terminal integral is exactly its second moment,
    -- and the just-proved Itô isometry identifies that second moment with the textbook norm
    -- square.
    calc
      ‖hIntegralMem.toLp (brownianElementaryIntegralAtInfinity W H)‖ ^ 2
          = ∫ ω, (brownianElementaryIntegralAtInfinity W H ω) ^ 2 ∂μ := by
              exact toLpNormSq_eq_integral_sq hIntegralMem
      _ = predictableSimpleProcessNormSq μ H := by
            exact brownianElementaryIntegralAtInfinity_sq_integral_eq_predictableSimpleProcessNormSq
              hW hW_adapted hW_indep H
  have hNorm :
      ‖hIntegralMem.toLp (brownianElementaryIntegralAtInfinity W H)‖ =
        predictableSimpleProcessNorm μ H := by
    -- Proof comment: both sides are nonnegative, so the square identity upgrades directly to a
    -- norm identity.
    have hNormTarget :
        (predictableSimpleProcessNorm μ H) ^ 2 = predictableSimpleProcessNormSq μ H := by
      rw [predictableSimpleProcessNorm, predictableSimpleProcessNormSq, Real.sq_sqrt]
      positivity
    refine (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 ?_
    calc
      ‖hIntegralMem.toLp (brownianElementaryIntegralAtInfinity W H)‖ ^ 2
          = predictableSimpleProcessNormSq μ H := hNormSq
      _ = (predictableSimpleProcessNorm μ H) ^ 2 := hNormTarget.symm
  calc
    eLpNorm (brownianElementaryIntegralAtInfinity W H) 2 μ
        = ‖hIntegralMem.toLp (brownianElementaryIntegralAtInfinity W H)‖ₑ := by
            symm
            exact Lp.enorm_toLp hIntegralMem
    _ = ENNReal.ofReal ‖hIntegralMem.toLp (brownianElementaryIntegralAtInfinity W H)‖ := by
          rw [← ofReal_norm_eq_enorm]
    _ = ENNReal.ofReal (predictableSimpleProcessNorm μ H) := by
          rw [hNorm]
-- Proof sketch: for a predictable simple integrand `H`, the stopped Brownian elementary integral
-- is the usual Brownian Itô martingale; the Itô isometry gives the uniform `L²` bound, and the
-- Brownian sample-path continuity passes through the finite increment formula defining the
-- integral.
/-- Companion to Theorem 25.4: for every predictable simple process `H`, the stopped Brownian
elementary integral process is a continuous `𝓕`-martingale that is uniformly bounded in
`L²(μ)`, provided the Brownian motion is adapted to `𝓕` and every increment `W t - W s` with
`s ≤ t` is independent of `𝓕 s`. -/
theorem brownianElementaryIntegral_isL2BoundedContinuousMartingale
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcess ℱ) :
    Martingale (brownianElementaryIntegral W H) ℱ μ ∧
      HasAlmostSurelyContinuousPaths μ (brownianElementaryIntegral W H) ∧
      ∃ C : ℝ≥0, ∀ t : NNReal, eLpNorm (brownianElementaryIntegral W H t) 2 μ ≤ (C : ℝ≥0∞) := by
  -- Proof comment: the public companion simply unpacks the second clause of Theorem 25.4 at the
  -- chosen predictable simple integrand.
  exact
    (brownianElementaryIntegral_isometry_and_isL2BoundedContinuousMartingale
        hW hW_adapted hW_indep).2.2.2 H
/-- The stopped Brownian elementary integral of a predictable simple process is a martingale. -/
theorem brownianElementaryIntegral_martingale
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcess ℱ) :
    Martingale (brownianElementaryIntegral W H) ℱ μ := by
  -- Proof comment: this is the martingale component of the bundled companion theorem above.
  exact (brownianElementaryIntegral_isL2BoundedContinuousMartingale
      hW hW_adapted hW_indep H).1
/-- The stopped Brownian elementary integral of a predictable simple process has almost surely
continuous sample paths. -/
theorem brownianElementaryIntegral_hasAlmostSurelyContinuousPaths
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcess ℱ) :
    HasAlmostSurelyContinuousPaths μ (brownianElementaryIntegral W H) := by
  -- Proof comment: this is the pathwise continuity component of the bundled companion theorem.
  exact (brownianElementaryIntegral_isL2BoundedContinuousMartingale
      hW hW_adapted hW_indep H).2.1
/-- The stopped Brownian elementary integral of a predictable simple process is uniformly bounded
in `L²(μ)` over time. -/
theorem brownianElementaryIntegral_l2_bounded
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (hW_indep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcess ℱ) :
    ∃ C : ℝ≥0, ∀ t : NNReal, eLpNorm (brownianElementaryIntegral W H t) 2 μ ≤ (C : ℝ≥0∞) := by
  -- Proof comment: this is the uniform `L²` bound component of the bundled companion theorem.
  exact (brownianElementaryIntegral_isL2BoundedContinuousMartingale
      hW hW_adapted hW_indep H).2.2
end Setup

end ProbabilityTheory

end
