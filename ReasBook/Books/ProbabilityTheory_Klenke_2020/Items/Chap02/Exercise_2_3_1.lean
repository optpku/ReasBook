/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Example_2_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The `n`th partial sum of an integer-valued sequence of increments, using the first `n`
coordinates `X 0, …, X (n - 1)`. -/
def random_walk_partial_sum (X : ℕ → Ω → ℤ) (n : ℕ) : Ω → ℤ :=
  fun ω ↦ Finset.sum (Finset.range n) fun i ↦ X i ω

-- Proof sketch: a finite sum of measurable coordinate maps is measurable.
/-- Each finite random-walk partial sum is measurable when the increments are measurable. -/
theorem measurable_random_walk_partial_sum (X : ℕ → Ω → ℤ) (hX_meas : ∀ n, Measurable (X n))
    (n : ℕ) : Measurable (random_walk_partial_sum X n) := by
  simpa [random_walk_partial_sum] using
    Finset.measurable_sum (Finset.range n) fun i _ ↦ hX_meas i

-- Proof sketch: unfold `random_walk_partial_sum` and evaluate the empty finite sum.
/-- The zeroth partial sum of the random walk is identically zero. -/
theorem random_walk_partial_sum_zero {Ω : Type u} (X : ℕ → Ω → ℤ) :
    random_walk_partial_sum X 0 = fun _ : Ω ↦ 0 := by
  ext ω
  simp [random_walk_partial_sum]

/-- Helper for Exercise 2.3.1: adding `k` further increments after time `n` splits the partial
sum into its length-`n` prefix plus the length-`k` tail walk started at `n`. -/
theorem random_walk_partial_sum_add (X : ℕ → Ω → ℤ) (n k : ℕ) (ω : Ω) :
    random_walk_partial_sum X (n + k) ω =
      random_walk_partial_sum X n ω +
        random_walk_partial_sum (fun j ω' ↦ X (n + j) ω') k ω := by
  -- Split the finite sum at the time `n`, then rewrite the tail by reindexing.
  simp [random_walk_partial_sum, Finset.sum_range_add, add_comm, add_left_comm, add_assoc]

/-- Helper for Exercise 2.3.1: consecutive partial sums differ by the next increment. -/
theorem random_walk_partial_sum_succ_sub (X : ℕ → Ω → ℤ) (n : ℕ) (ω : Ω) :
    random_walk_partial_sum X (n + 1) ω - random_walk_partial_sum X n ω = X n ω := by
  -- The new partial sum adds exactly the `n`th step.
  simp [random_walk_partial_sum, Finset.sum_range_succ]

/-- Helper for Exercise 2.3.1: after casting to `ℝ`, consecutive partial sums still differ by the
next increment. -/
theorem random_walk_partial_sum_real_succ_sub (X : ℕ → Ω → ℤ) (n : ℕ) (ω : Ω) :
    ((random_walk_partial_sum X (n + 1) ω : ℤ) : ℝ) -
        ((random_walk_partial_sum X n ω : ℤ) : ℝ) =
      ((X n ω : ℤ) : ℝ) := by
  exact_mod_cast random_walk_partial_sum_succ_sub X n ω

/-- Helper for Exercise 2.3.1: the real-cast increments are measurable. -/
theorem measurable_stepReal (X : ℕ → Ω → ℤ) (hX_meas : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (fun ω ↦ ((X n ω : ℤ) : ℝ)) := by
  -- This is just composition with the measurable cast `ℤ → ℝ`.
  fun_prop

/-- Helper for Exercise 2.3.1: singleton cylinder events inherit independence from the coordinate
independence of the integer-valued increments. -/
theorem iIndepSet_preimage_singleton_of_iIndepFun (μ : Measure Ω) (Y : ℕ → Ω → ℤ)
    (hY_meas : ∀ n, Measurable (Y n)) (hY_indep : iIndepFun Y μ) (z : ℤ) :
    iIndepSet (fun n ↦ (Y n) ⁻¹' ({z} : Set ℤ)) μ := by
  -- The singleton-cylinder product formula is exactly the finite-event independence criterion.
  refine (ProbabilityTheory.iIndepSet_iff_meas_biInter ?_).2 ?_
  · intro i
    exact (hY_meas i) (measurableSet_singleton z)
  · intro s
    simpa using hY_indep.measure_inter_preimage_eq_mul s
      (fun _ _ ↦ measurableSet_singleton z)

/-- Helper for Exercise 2.3.1: each fair-sign increment takes only the values `-1` and `1`
almost surely. -/
theorem ae_eq_negOne_or_eq_one_of_fairSigns (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℤ) (hX_meas : ∀ n, Measurable (X n))
    (hX_neg : ∀ n : ℕ, μ ((X n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (hX_pos : ∀ n : ℕ, μ ((X n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (n : ℕ) :
    ∀ᵐ ω ∂μ, X n ω = (-1 : ℤ) ∨ X n ω = 1 := by
  let A : Set Ω := (X n) ⁻¹' {(-1 : ℤ)}
  let B : Set Ω := (X n) ⁻¹' {(1 : ℤ)}
  have hA_meas : MeasurableSet A := by
    simpa [A] using (hX_meas n) (measurableSet_singleton (-1 : ℤ))
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hX_meas n) (measurableSet_singleton (1 : ℤ))
  have hAB_disj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro ω hωA hωB
    simp only [A, B, Set.mem_preimage, Set.mem_singleton_iff] at hωA hωB
    omega
  have h_union : μ (A ∪ B) = 1 := by
    calc
      μ (A ∪ B) = μ A + μ B := by
        simpa [A, B] using measure_union hAB_disj hB_meas
      _ = (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ := by rw [hX_neg n, hX_pos n]
      _ = 1 := by
        simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (ENNReal.add_halves (1 : ℝ≥0∞))
  have h_compl : μ ((A ∪ B)ᶜ) = 0 := by
    have h_fin : μ (A ∪ B) ≠ ∞ := by rw [h_union]; simp
    simpa [h_union, IsProbabilityMeasure.measure_univ] using
      measure_compl (hA_meas.union hB_meas) h_fin
  have h_ae_union : ∀ᵐ ω ∂μ, ω ∈ A ∪ B := by
    rw [ae_iff]
    simpa using h_compl
  filter_upwards [h_ae_union] with ω hω
  simpa [A, B] using hω

/-- Helper for Exercise 2.3.1: each real-valued increment is integrable because it is almost surely
bounded by `1` in absolute value. -/
theorem integrable_stepReal_of_fairSigns (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℤ) (hX_meas : ∀ n, Measurable (X n))
    (hX_neg : ∀ n : ℕ, μ ((X n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (hX_pos : ∀ n : ℕ, μ ((X n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (n : ℕ) :
    Integrable (fun ω ↦ ((X n ω : ℤ) : ℝ)) μ := by
  have h_ae_bound :
      ∀ᵐ ω ∂μ, ‖((X n ω : ℤ) : ℝ)‖ ≤ 1 := by
    filter_upwards
      [ae_eq_negOne_or_eq_one_of_fairSigns (μ := μ) (X := X) hX_meas hX_neg hX_pos n]
      with ω hω
    rcases hω with hω | hω <;> simp [hω]
  -- A measurable real function dominated by an integrable constant is integrable.
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ h_ae_bound
  exact (measurable_stepReal X hX_meas n).aestronglyMeasurable

/-- Helper for Exercise 2.3.1: the fair-sign increments have mean zero after casting to `ℝ`. -/
theorem integral_stepReal_eq_zero_of_fairSigns (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℤ) (hX_meas : ∀ n, Measurable (X n))
    (hX_neg : ∀ n : ℕ, μ ((X n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (hX_pos : ∀ n : ℕ, μ ((X n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (n : ℕ) :
    ∫ ω, ((X n ω : ℤ) : ℝ) ∂μ = 0 := by
  let A : Set Ω := (X n) ⁻¹' {(-1 : ℤ)}
  let B : Set Ω := (X n) ⁻¹' {(1 : ℤ)}
  have hA_meas : MeasurableSet A := by
    simpa [A] using (hX_meas n) (measurableSet_singleton (-1 : ℤ))
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hX_meas n) (measurableSet_singleton (1 : ℤ))
  have h_repr :
      (fun ω ↦ ((X n ω : ℤ) : ℝ)) =ᵐ[μ]
        fun ω ↦ A.indicator (fun _ ↦ (-1 : ℝ)) ω + B.indicator (fun _ ↦ (1 : ℝ)) ω := by
    filter_upwards
      [ae_eq_negOne_or_eq_one_of_fairSigns (μ := μ) (X := X) hX_meas hX_neg hX_pos n] with ω hω
    rcases hω with hω | hω
    · simp [A, B, hω]
    · simp [A, B, hω]
  -- Replace the increment by the two indicator pieces and evaluate the resulting integrals.
  calc
    ∫ ω, ((X n ω : ℤ) : ℝ) ∂μ =
        ∫ ω, (A.indicator (fun _ ↦ (-1 : ℝ)) ω + B.indicator (fun _ ↦ (1 : ℝ)) ω) ∂μ := by
          refine integral_congr_ae h_repr
    _ = ∫ ω, A.indicator (fun _ ↦ (-1 : ℝ)) ω ∂μ
          + ∫ ω, B.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
            rw [integral_add]
            · exact (integrable_const (-1 : ℝ)).indicator hA_meas
            · exact (integrable_const (1 : ℝ)).indicator hB_meas
    _ = μ.real A * (-1 : ℝ) + μ.real B * (1 : ℝ) := by
          rw [integral_indicator_const (-1 : ℝ) hA_meas, integral_indicator_const (1 : ℝ) hB_meas]
          simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    _ = (((2 : ℝ≥0∞)⁻¹).toReal) * (-1 : ℝ) + (((2 : ℝ≥0∞)⁻¹).toReal) * (1 : ℝ) := by
          rw [Measure.real_def, Measure.real_def, hX_neg n, hX_pos n]
    _ = 0 := by norm_num

/-- Helper for Exercise 2.3.1: the shifted fair-sign increment sequence still takes the value `1`
infinitely often almost surely, so it does not converge to `0`. -/
theorem ae_not_tendsto_zero_stepReal_tail_of_independent_fairSigns (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℤ) (hX_meas : ∀ n, Measurable (X n))
    (h_indep : iIndepFun X μ)
    (hX_pos : ∀ n : ℕ, μ ((X n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹) :
    ∀ᵐ ω ∂μ, ¬ Tendsto (fun n ↦ ((X (n + 1) ω : ℤ) : ℝ)) atTop (nhds 0) := by
  let Y : ℕ → Ω → ℤ := fun n ω ↦ X (n + 1) ω
  let A : ℕ → Set Ω := fun n ↦ (Y n) ⁻¹' ({(1 : ℤ)} : Set ℤ)
  have hY_meas : ∀ n, Measurable (Y n) := by
    intro n
    simpa [Y] using hX_meas (n + 1)
  have hY_indep : iIndepFun Y μ := by
    simpa [Y] using h_indep.precomp Nat.succ_injective
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    simpa [A] using hY_meas n (measurableSet_singleton (1 : ℤ))
  have hA_indep : iIndepSet A μ :=
    iIndepSet_preimage_singleton_of_iIndepFun μ Y hY_meas hY_indep 1
  have hA_sum : (∑' n, μ (A n)) = ∞ := by
    simp [A, Y, hX_pos, ENNReal.tsum_const_eq_top_of_ne_zero]
  have hA_limsup : μ (limsup A atTop) = 1 :=
    borelCantelli_measure_limsup_atTop_eq_one μ A hA_meas hA_indep hA_sum
  have hA_full : ∀ᵐ ω ∂μ, ω ∈ limsup A atTop := by
    rw [ae_iff]
    have h_meas : MeasurableSet (limsup A atTop) := by
      rw [Filter.limsup_eq_iInf_iSup_of_nat]
      refine MeasurableSet.iInter ?_
      intro n
      refine MeasurableSet.iUnion ?_
      intro i
      refine MeasurableSet.iUnion ?_
      intro _
      simpa using hA_meas i
    have h_fin : μ (limsup A atTop) ≠ ∞ := by rw [hA_limsup]; simp
    simpa [hA_limsup, IsProbabilityMeasure.measure_univ] using measure_compl h_meas h_fin
  filter_upwards [hA_full] with ω hω hconv
  have hfreq_one : ∃ᶠ n in atTop, Y n ω = 1 := by
    simpa [A, mem_limsup_iff_frequently_mem] using hω
  have h_eventually_small :
      ∀ᶠ n in atTop, |((Y n ω : ℤ) : ℝ)| < (1 / 2 : ℝ) := by
    simpa [Real.dist_eq, Y] using
      hconv.eventually (Metric.ball_mem_nhds (0 : ℝ) (show 0 < (1 / 2 : ℝ) by norm_num))
  have h_eventually_ne_one : ∀ᶠ n in atTop, Y n ω ≠ 1 := by
    filter_upwards [h_eventually_small] with n hn hEq
    have : |(((1 : ℤ) : ℝ))| < (1 / 2 : ℝ) := by simpa [hEq] using hn
    norm_num at this
  exact hfreq_one h_eventually_ne_one

/-- Helper for Exercise 2.3.1: the real-valued partial sums of a fair-sign walk are almost surely
unbounded above. -/
theorem ae_not_bddAbove_range_randomWalkReal_of_independent_fairSigns (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℤ) (hX_meas : ∀ n, Measurable (X n))
    (h_indep : iIndepFun X μ)
    (hX_neg : ∀ n : ℕ, μ ((X n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (hX_pos : ∀ n : ℕ, μ ((X n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹) :
    ∀ᵐ ω ∂μ, ¬ BddAbove (Set.range fun n : ℕ => ((random_walk_partial_sum X n ω : ℤ) : ℝ)) := by
  let stepReal : ℕ → Ω → ℝ := fun n ω ↦ ((X n ω : ℤ) : ℝ)
  let walkReal : ℕ → Ω → ℝ := fun n ω ↦ ((random_walk_partial_sum X n ω : ℤ) : ℝ)
  let shiftedWalkReal : ℕ → Ω → ℝ := fun n ω ↦ walkReal (n + 1) ω
  let ℱ : Filtration ℕ ‹MeasurableSpace Ω› :=
    Filtration.natural stepReal (fun n ↦ (measurable_stepReal X hX_meas n).stronglyMeasurable)
  have hstep_indep : iIndepFun stepReal μ := by
    simpa [stepReal] using h_indep.comp (fun _ z ↦ (z : ℝ)) (fun _ ↦ by fun_prop)
  have hint_step : ∀ n, Integrable (stepReal n) μ := by
    intro n
    simpa [stepReal] using
      integrable_stepReal_of_fairSigns (μ := μ) (X := X) hX_meas hX_neg hX_pos n
  have hadp : StronglyAdapted ℱ shiftedWalkReal := by
    intro n
    have h_meas :
        Measurable[ℱ n] (shiftedWalkReal n) := by
      -- The shifted walk up to time `n` only depends on the coordinates `0, …, n`.
      simpa [shiftedWalkReal, walkReal, random_walk_partial_sum, stepReal] using
        (Finset.measurable_sum (Finset.range (n + 1))
          fun i hi ↦
            Measurable.of_comap_le <|
              le_iSup_of_le i <| le_iSup_of_le (Finset.mem_range_succ_iff.mp hi) le_rfl)
    exact h_meas.stronglyMeasurable
  have hint_walk : ∀ n, Integrable (shiftedWalkReal n) μ := by
    intro n
    simpa [shiftedWalkReal, walkReal, random_walk_partial_sum, stepReal] using
      integrable_finset_sum (Finset.range (n + 1)) fun i _ ↦ hint_step i
  have hcond : ∀ n, μ[shiftedWalkReal (n + 1) - shiftedWalkReal n | ℱ n] =ᵐ[μ] 0 := by
    intro n
    -- The next increment is independent of the past filtration and has mean `0`.
    have hdiff_eq :
        shiftedWalkReal (n + 1) - shiftedWalkReal n = stepReal (n + 1) := by
      ext ω
      change ((random_walk_partial_sum X (n + 1 + 1) ω : ℤ) : ℝ) -
          ((random_walk_partial_sum X (n + 1) ω : ℤ) : ℝ) = ((X (n + 1) ω : ℤ) : ℝ)
      simpa using random_walk_partial_sum_real_succ_sub X (n + 1) ω
    refine (condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦ congrFun hdiff_eq ω)).trans <|
      (ProbabilityTheory.iIndepFun.condExp_natural_ae_eq_of_lt
      (f := stepReal) (fun i ↦ (measurable_stepReal X hX_meas i).stronglyMeasurable)
      hstep_indep (Nat.lt_succ_self n)).trans ?_
    exact Filter.Eventually.of_forall fun ω ↦
      integral_stepReal_eq_zero_of_fairSigns (μ := μ) (X := X) hX_meas hX_neg hX_pos (n + 1)
  have hmart : Martingale shiftedWalkReal ℱ μ :=
    martingale_of_condExp_sub_eq_zero_nat hadp hint_walk hcond
  have hbdd_diff : ∀ᵐ ω ∂μ, ∀ i, |shiftedWalkReal (i + 1) ω - shiftedWalkReal i ω| ≤ 1 := by
    filter_upwards
      [ae_all_iff.2 fun i ↦
        ae_eq_negOne_or_eq_one_of_fairSigns (μ := μ) (X := X) hX_meas hX_neg hX_pos (i + 1)]
      with ω hω i
    have hdiff_eq :
        shiftedWalkReal (i + 1) ω - shiftedWalkReal i ω = ((X (i + 1) ω : ℤ) : ℝ) := by
      change ((random_walk_partial_sum X (i + 1 + 1) ω : ℤ) : ℝ) -
          ((random_walk_partial_sum X (i + 1) ω : ℤ) : ℝ) = ((X (i + 1) ω : ℤ) : ℝ)
      simpa using random_walk_partial_sum_real_succ_sub X (i + 1) ω
    rcases hω i with hEq | hEq
    · rw [hdiff_eq, hEq]
      norm_num
    · rw [hdiff_eq, hEq]
      norm_num
  have h_no_conv :
      ∀ᵐ ω ∂μ, ¬ ∃ c, Tendsto (fun n ↦ shiftedWalkReal n ω) atTop (nhds c) := by
    filter_upwards
      [ae_not_tendsto_zero_stepReal_tail_of_independent_fairSigns (μ := μ) (X := X)
        hX_meas h_indep hX_pos]
      with ω hω hconv
    rcases hconv with ⟨c, hconv⟩
    have htail : Tendsto (fun n ↦ shiftedWalkReal (n + 1) ω) atTop (nhds c) :=
      hconv.comp (tendsto_add_atTop_nat 1)
    have hdiff :
        Tendsto (fun n ↦ shiftedWalkReal (n + 1) ω - shiftedWalkReal n ω) atTop (nhds 0) := by
      simpa using htail.sub hconv
    have hdiff_fun :
        (fun n ↦ shiftedWalkReal (n + 1) ω - shiftedWalkReal n ω) =
          fun n ↦ stepReal (n + 1) ω := by
      funext n
      change ((random_walk_partial_sum X (n + 1 + 1) ω : ℤ) : ℝ) -
          ((random_walk_partial_sum X (n + 1) ω : ℤ) : ℝ) = ((X (n + 1) ω : ℤ) : ℝ)
      simpa using random_walk_partial_sum_real_succ_sub X (n + 1) ω
    have hstep : Tendsto (fun n ↦ stepReal (n + 1) ω) atTop (nhds 0) := by
      simpa [hdiff_fun] using hdiff
    exact hω hstep
  have hbdd_iff :
      ∀ᵐ ω ∂μ, BddAbove (Set.range fun n ↦ shiftedWalkReal n ω) ↔
        ∃ c, Tendsto (fun n ↦ shiftedWalkReal n ω) atTop (nhds c) :=
    hmart.submartingale.bddAbove_iff_exists_tendsto (R := 1) hbdd_diff
  have h_not_bddAbove_shifted :
      ∀ᵐ ω ∂μ, ¬ BddAbove (Set.range fun n ↦ shiftedWalkReal n ω) := by
    filter_upwards [hbdd_iff, h_no_conv] with ω hω hω'
    intro hbdd
    exact hω' (hω.mp hbdd)
  -- The unshifted range contains the shifted range, so lack of an upper bound propagates back.
  filter_upwards [h_not_bddAbove_shifted] with ω hω
  intro hbdd
  apply hω
  exact hbdd.mono <| by
    rintro y ⟨n, rfl⟩
    exact ⟨n + 1, rfl⟩

/-- Companion form of Exercise 2.3.1: almost surely, every integer level is crossed infinitely
often by the random-walk partial sums. This is the threshold-event reformulation of
`limsup S_n = ∞`. -/
theorem ae_infinite_partial_sum_ge_of_independent_fair_signs (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℤ) (hX_meas : ∀ n, Measurable (X n))
    (h_indep : iIndepFun X μ)
    (hX_neg : ∀ n : ℕ, μ ((X n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (hX_pos : ∀ n : ℕ, μ ((X n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹) :
    ∀ᵐ ω ∂μ, ∀ M : ℤ, Set.Infinite {n : ℕ | M ≤ random_walk_partial_sum X n ω} := by
  have h_tail_unbounded :
      ∀ N : ℕ, ∀ᵐ ω ∂μ,
        ¬ BddAbove (Set.range fun k : ℕ =>
          ((random_walk_partial_sum (fun j ω ↦ X (N + j) ω) k ω : ℤ) : ℝ)) := by
    intro N
    -- Every tail sequence is again an independent fair-sign family.
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      ae_not_bddAbove_range_randomWalkReal_of_independent_fairSigns
        (μ := μ) (X := fun j ω ↦ X (N + j) ω)
        (fun j ↦ hX_meas (N + j))
        (h_indep.precomp (by
          intro a b h
          exact Nat.add_left_cancel h))
        (fun j ↦ hX_neg (N + j))
        (fun j ↦ hX_pos (N + j))
  have h_all_tail_unbounded :
      ∀ᵐ ω ∂μ, ∀ N : ℕ,
        ¬ BddAbove (Set.range fun k : ℕ =>
          ((random_walk_partial_sum (fun j ω' ↦ X (N + j) ω') k ω : ℤ) : ℝ)) :=
    ae_all_iff.2 h_tail_unbounded
  filter_upwards [h_all_tail_unbounded] with ω hω
  intro M
  have hfreq : ∃ᶠ n in atTop, M ≤ random_walk_partial_sum X n ω := by
    rw [frequently_atTop]
    -- From any starting time `N`, the tail walk can climb above the translated threshold.
    intro N
    have hN := hω N
    rcases not_bddAbove_iff'.1 hN (M - random_walk_partial_sum X N ω : ℝ) with
      ⟨tailVal, ⟨k, hk⟩, hy⟩
    refine ⟨N + k, Nat.le_add_right N k, ?_⟩
    have hy' : (M : ℝ) < (random_walk_partial_sum X N ω : ℝ) + tailVal := by
      linarith
    have hsplit := random_walk_partial_sum_add X N k ω
    exact le_of_lt <| by
      rw [← hk] at hy'
      have hyInt :
          (M : ℝ) <
            ((random_walk_partial_sum X N ω +
              random_walk_partial_sum (fun j ω' ↦ X (N + j) ω') k ω : ℤ) : ℝ) := by
        simpa [Int.cast_add] using hy'
      have hyInt' :
          M < random_walk_partial_sum X N ω +
            random_walk_partial_sum (fun j ω' ↦ X (N + j) ω') k ω := by
        exact_mod_cast hyInt
      simpa [hsplit, add_comm, add_left_comm, add_assoc] using hyInt'
  exact (Nat.frequently_atTop_iff_infinite).1 hfreq

-- Proof sketch: upgrade the companion threshold statement to frequent threshold crossings and then
-- apply the order-theoretic characterization `EReal.eq_top_iff_forall_lt`.
/-- Exercise 2.3.1: if `(X n)` is an independent family of fair-sign integer-valued random
variables, then the random-walk partial sums satisfy `limsup S_n = ∞` almost surely. Here
`random_walk_partial_sum X n = X 0 + ⋯ + X (n - 1)`, so this is the canonical `0`-based version of
the textbook statement. -/
theorem ae_limsup_random_walk_partial_sum_eq_top_of_independent_fair_signs (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℤ) (hX_meas : ∀ n, Measurable (X n))
    (h_indep : iIndepFun X μ)
    (hX_neg : ∀ n : ℕ, μ ((X n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (hX_pos : ∀ n : ℕ, μ ((X n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹) :
    ∀ᵐ ω ∂μ, limsup (fun n ↦ (((random_walk_partial_sum X n ω : ℤ) : ℝ) : EReal)) atTop = ⊤ := by
  filter_upwards
    [ae_infinite_partial_sum_ge_of_independent_fair_signs (μ := μ) (X := X) hX_meas h_indep
      hX_neg hX_pos] with ω hω
  rw [EReal.eq_top_iff_forall_lt]
  intro N
  let M : ℤ := Int.ceil N + 1
  have hM_freq :
      ∃ᶠ n in atTop, ((((M : ℤ) : ℝ) : EReal)) ≤
        (((random_walk_partial_sum X n ω : ℤ) : ℝ) : EReal) := by
    rw [Nat.frequently_atTop_iff_infinite]
    refine (hω M).mono ?_
    intro n hn
    exact_mod_cast hn
  have hM_le :
      ((((M : ℤ) : ℝ) : EReal)) ≤
        limsup (fun n ↦ (((random_walk_partial_sum X n ω : ℤ) : ℝ) : EReal)) atTop :=
    (le_limsup_iff').2 fun z hz ↦ hM_freq.mono fun n hn ↦ le_trans hz.le hn
  have hNM : (N : EReal) < (((M : ℤ) : ℝ) : EReal) := by
    have hNM_real : N < (M : ℝ) := by
      calc
        N ≤ (Int.ceil N : ℝ) := by exact_mod_cast Int.le_ceil N
        _ < (Int.ceil N : ℝ) + 1 := by linarith
        _ = (M : ℝ) := by
          dsimp [M]
          norm_num
    exact_mod_cast hNM_real
  exact hNM.trans_le hM_le
