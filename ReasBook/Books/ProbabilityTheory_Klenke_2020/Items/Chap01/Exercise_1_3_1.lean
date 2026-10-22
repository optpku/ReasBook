/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set

open scoped ENNReal Topology

noncomputable section

/-- Helper for Exercise 1.3.1: the weighted atomic measure attached to the atoms `x n` and
weights `α n`. -/
private def weightedAtomicMeasure (x : ℕ → ℝ) (α : ℕ → NNReal) : Measure ℝ :=
  Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n))

/-- Helper for Exercise 1.3.1: the mass of a closed interval under the weighted atomic measure is
the corresponding weighted indicator sum. -/
private theorem weightedAtomicMeasure_Icc_eq_tsum_indicator
    (x : ℕ → ℝ) (α : ℕ → NNReal) (a b : ℝ) :
    weightedAtomicMeasure x α (Set.Icc a b) =
      ∑' n, if x n ∈ Set.Icc a b then (α n : ℝ≥0∞) else 0 := by
  -- Expand the sum measure and evaluate each weighted Dirac mass on the interval.
  rw [weightedAtomicMeasure, Measure.sum_apply _ measurableSet_Icc]
  refine tsum_congr fun n ↦ ?_
  by_cases hmem : x n ∈ Set.Icc a b
  · rw [Measure.smul_apply, Measure.dirac_apply]
    simp [hmem]
  · rw [Measure.smul_apply, Measure.dirac_apply]
    simp [hmem]

/-- Helper for Exercise 1.3.1: bounded summability of the weights forces finite mass on every
symmetric closed interval `[-K, K]`. -/
private theorem weightedAtomicMeasure_symmetricIcc_ltTop_of_boundedWeightSummable
    (x : ℕ → ℝ) (α : ℕ → NNReal)
    (hloc : ∀ K : ℝ, 0 < K → Summable (fun n ↦ if |x n| ≤ K then α n else 0))
    {K : ℝ} (hK : 0 < K) :
    weightedAtomicMeasure x α (Set.Icc (-K) K) < ∞ := by
  -- Rewrite the interval mass as a series and appeal to the given bounded summability hypothesis.
  rw [weightedAtomicMeasure_Icc_eq_tsum_indicator x α (-K) K]
  have hsummable : Summable (fun n ↦ if x n ∈ Set.Icc (-K) K then α n else 0) := by
    simpa [Set.mem_Icc, abs_le] using hloc K hK
  have htsum :
      (∑' n, (((if x n ∈ Set.Icc (-K) K then α n else 0 : NNReal) : ℝ≥0∞))) =
        ∑' n, if x n ∈ Set.Icc (-K) K then (α n : ℝ≥0∞) else 0 := by
    refine tsum_congr fun n ↦ ?_
    by_cases hmem : x n ∈ Set.Icc (-K) K <;> simp [hmem]
  exact lt_top_iff_ne_top.mpr <|
    by
      rw [← htsum]
      exact
        (show
          (∑' n, ((if x n ∈ Set.Icc (-K) K then α n else 0 : NNReal) : ℝ≥0∞)) ≠ ∞ from
            ENNReal.tsum_coe_ne_top_iff_summable.mpr hsummable)

/-- Helper for Exercise 1.3.1: bounded summability of the weights forces finite mass on every
bounded closed interval. -/
private theorem weightedAtomicMeasure_Icc_ltTop_of_boundedWeightSummable
    (x : ℕ → ℝ) (α : ℕ → NNReal)
    (hloc : ∀ K : ℝ, 0 < K → Summable (fun n ↦ if |x n| ≤ K then α n else 0))
    {a b : ℝ} :
    weightedAtomicMeasure x α (Set.Icc a b) < ∞ := by
  let K : ℝ := max |a| |b| + 1
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hsubset : Set.Icc a b ⊆ Set.Icc (-K) K := by
    intro y hy
    have habs : |y| ≤ max |a| |b| := abs_le_max_abs_abs hy.1 hy.2
    have hKy : |y| ≤ K := by
      dsimp [K]
      linarith
    simpa [Set.mem_Icc] using abs_le.mp hKy
  -- Compare the bounded interval to a slightly larger symmetric interval.
  exact lt_of_le_of_lt (measure_mono hsubset)
    (weightedAtomicMeasure_symmetricIcc_ltTop_of_boundedWeightSummable x α hloc hK)

-- Proof sketch: local finiteness of the weighted atomic measure is exactly finite mass on bounded
-- neighborhoods, and the interval-mass formula turns this into bounded summability of the weights.
/-- The weighted atomic measure `∑' n, α n δ_(x n)` on `ℝ` is locally finite exactly when the
total weight of the atoms in every bounded interval `[-K, K]` is finite. -/
theorem weightedDiracSum_isLocallyFiniteMeasure_iff_boundedWeightSummable
    (x : ℕ → ℝ) (α : ℕ → NNReal) :
    IsLocallyFiniteMeasure
        (Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n))) ↔
      ∀ K : ℝ, 0 < K → Summable (fun n ↦ if |x n| ≤ K then α n else 0) := by
  simpa [weightedAtomicMeasure] using
    (show IsLocallyFiniteMeasure (weightedAtomicMeasure x α) ↔
        ∀ K : ℝ, 0 < K → Summable (fun n ↦ if |x n| ≤ K then α n else 0) from by
      constructor
      · intro hμ K hK
        letI : IsLocallyFiniteMeasure (weightedAtomicMeasure x α) := hμ
        have hfinite : weightedAtomicMeasure x α (Set.Icc (-K) K) < ∞ := measure_Icc_lt_top
        rw [weightedAtomicMeasure_Icc_eq_tsum_indicator x α (-K) K] at hfinite
        have htsum :
            (∑' n, (((if x n ∈ Set.Icc (-K) K then α n else 0 : NNReal) : ℝ≥0∞))) =
              ∑' n, if x n ∈ Set.Icc (-K) K then (α n : ℝ≥0∞) else 0 := by
          refine tsum_congr fun n ↦ ?_
          by_cases hmem : x n ∈ Set.Icc (-K) K <;> simp [hmem]
        have hsummable :
            Summable (fun n ↦ if x n ∈ Set.Icc (-K) K then α n else 0) := by
          exact ENNReal.tsum_coe_ne_top_iff_summable.mp <|
            (show
              (∑' n, ((if x n ∈ Set.Icc (-K) K then α n else 0 : NNReal) : ℝ≥0∞)) ≠ ∞ from
                by rw [htsum]; simpa using (lt_top_iff_ne_top.mp hfinite))
        simpa [Set.mem_Icc, abs_le] using hsummable
      · intro hloc
        refine ⟨fun t ↦ ?_⟩
        refine ⟨Set.Icc (t - 1) (t + 1), ?_, ?_⟩
        · exact Icc_mem_nhds (by linarith) (by linarith)
        · exact weightedAtomicMeasure_Icc_ltTop_of_boundedWeightSummable x α hloc)

/-- Helper for Exercise 1.3.1: the anchored cumulative mass function associated to a locally
finite measure on `ℝ`. -/
private def anchoredLocallyFiniteMeasureFunction (μ : Measure ℝ) : ℝ → ℝ :=
  fun t ↦ if 0 ≤ t then μ.real (Set.Ioc 0 t) else -μ.real (Set.Ioc t 0)

/-- Helper for Exercise 1.3.1: the anchored cumulative mass function has interval increments given
by the underlying measure. -/
private theorem anchoredLocallyFiniteMeasureFunction_intervalFormula
    (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] {a b : ℝ} (hab : a ≤ b) :
    anchoredLocallyFiniteMeasureFunction μ b - anchoredLocallyFiniteMeasureFunction μ a =
      μ.real (Set.Ioc a b) := by
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := le_trans ha hab
    have hpre_ab : MeasurableSet (Set.Ioc a b) := measurableSet_Ioc
    have hne_0a : μ (Set.Ioc 0 a) ≠ ⊤ := measure_Ioc_lt_top.ne
    have hne_ab : μ (Set.Ioc a b) ≠ ⊤ := measure_Ioc_lt_top.ne
    have hunion : Set.Ioc 0 b = Set.Ioc 0 a ∪ Set.Ioc a b := by
      ext y
      constructor <;> intro hy
      · by_cases hya : y ≤ a
        · exact Or.inl ⟨hy.1, hya⟩
        · exact Or.inr ⟨lt_of_not_ge hya, hy.2⟩
      · rcases hy with hy | hy
        · exact ⟨hy.1, le_trans hy.2 hab⟩
        · exact ⟨lt_of_le_of_lt ha hy.1, hy.2⟩
    have hdisj : Disjoint (Set.Ioc 0 a) (Set.Ioc a b) := by
      rw [Set.disjoint_left]
      intro y hy0a hyab
      exact not_lt_of_ge hy0a.2 hyab.1
    have hadd :
        μ.real (Set.Ioc 0 b) = μ.real (Set.Ioc 0 a) + μ.real (Set.Ioc a b) := by
      rw [measureReal_def, measureReal_def, measureReal_def, hunion,
        measure_union hdisj hpre_ab, ENNReal.toReal_add hne_0a hne_ab]
    -- On the nonnegative side, the anchored mass splits at `a`.
    simp [anchoredLocallyFiniteMeasureFunction, ha, hb]
    linarith
  · by_cases hb : 0 ≤ b
    · have hpre_0b : MeasurableSet (Set.Ioc 0 b) := measurableSet_Ioc
      have hne_a0 : μ (Set.Ioc a 0) ≠ ⊤ := measure_Ioc_lt_top.ne
      have hne_0b : μ (Set.Ioc 0 b) ≠ ⊤ := measure_Ioc_lt_top.ne
      have hunion : Set.Ioc a b = Set.Ioc a 0 ∪ Set.Ioc 0 b := by
        ext y
        constructor <;> intro hy
        · by_cases hynonpos : y ≤ 0
          · exact Or.inl ⟨hy.1, hynonpos⟩
          · exact Or.inr ⟨lt_of_not_ge hynonpos, hy.2⟩
        · rcases hy with hy | hy
          · exact ⟨hy.1, le_trans hy.2 hb⟩
          · exact ⟨lt_trans (lt_of_not_ge ha) hy.1, hy.2⟩
      have hdisj : Disjoint (Set.Ioc a 0) (Set.Ioc 0 b) := by
        rw [Set.disjoint_left]
        intro y hya0 hy0b
        exact not_lt_of_ge hya0.2 hy0b.1
      have hadd :
          μ.real (Set.Ioc a b) = μ.real (Set.Ioc a 0) + μ.real (Set.Ioc 0 b) := by
        rw [measureReal_def, measureReal_def, measureReal_def, hunion,
          measure_union hdisj hpre_0b, ENNReal.toReal_add hne_a0 hne_0b]
      -- Crossing the anchor at `0` splits the interval into two disjoint pieces.
      simp [anchoredLocallyFiniteMeasureFunction, ha, hb]
      linarith
    · have hb' : b ≤ 0 := le_of_not_ge hb
      have hpre_b0 : MeasurableSet (Set.Ioc b 0) := measurableSet_Ioc
      have hne_ab : μ (Set.Ioc a b) ≠ ⊤ := measure_Ioc_lt_top.ne
      have hne_b0 : μ (Set.Ioc b 0) ≠ ⊤ := measure_Ioc_lt_top.ne
      have hunion : Set.Ioc a 0 = Set.Ioc a b ∪ Set.Ioc b 0 := by
        ext y
        constructor <;> intro hy
        · by_cases hyb : y ≤ b
          · exact Or.inl ⟨hy.1, hyb⟩
          · exact Or.inr ⟨lt_of_not_ge hyb, hy.2⟩
        · rcases hy with hy | hy
          · exact ⟨hy.1, le_trans hy.2 hb'⟩
          · exact ⟨lt_of_le_of_lt hab hy.1, hy.2⟩
      have hdisj : Disjoint (Set.Ioc a b) (Set.Ioc b 0) := by
        rw [Set.disjoint_left]
        intro y hyab hyb0
        exact not_lt_of_ge hyab.2 hyb0.1
      have hadd :
          μ.real (Set.Ioc a 0) = μ.real (Set.Ioc a b) + μ.real (Set.Ioc b 0) := by
        rw [measureReal_def, measureReal_def, measureReal_def, hunion,
          measure_union hdisj hpre_b0, ENNReal.toReal_add hne_ab hne_b0]
      -- On the negative side, the anchored mass splits at `b`.
      simp [anchoredLocallyFiniteMeasureFunction, ha, hb]
      linarith

/-- Helper for Exercise 1.3.1: the masses `μ (t, y]` tend to `0` when `y` decreases to `t`. -/
private theorem tendsto_measureReal_Ioc_nhdsGT
    (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] (t : ℝ) :
    Tendsto (fun y : ℝ ↦ μ.real (Set.Ioc t y)) (𝓝[>] t) (𝓝 0) := by
  have h_measure_sub :
      Tendsto (fun y : Set.Ioi t ↦ μ (Set.Ioc t (y : ℝ))) atBot
        (𝓝 (μ (⋂ y : Set.Ioi t, Set.Ioc t (y : ℝ)))) := by
    refine tendsto_measure_iInter_atBot (μ := μ)
      (fun _ ↦ measurableSet_Ioc.nullMeasurableSet) ?_ ?_
    · intro a b hab
      exact Set.Ioc_subset_Ioc_right hab
    · refine ⟨⟨t + 1, lt_add_of_pos_right t zero_lt_one⟩, measure_Ioc_lt_top.ne⟩
  have h_inter : (⋂ y : Set.Ioi t, Set.Ioc t (y : ℝ)) = (∅ : Set ℝ) := by
    ext z
    constructor
    · intro hz
      simp only [Set.mem_iInter, Set.mem_Ioc] at hz
      have htz : t < z := (hz ⟨t + 1, lt_add_of_pos_right t zero_lt_one⟩).1
      obtain ⟨y, hty, hyz⟩ := exists_between htz
      exact (not_le_of_gt hyz) (hz ⟨y, hty⟩).2
    · intro hz
      simp at hz
  rw [h_inter, measure_empty] at h_measure_sub
  have h_real_sub :
      Tendsto (fun y : Set.Ioi t ↦ μ.real (Set.Ioc t (y : ℝ))) atBot (𝓝 0) := by
    -- Passing from `μ` to `μ.real` turns the `ENNReal` limit `0` into the real limit `0`.
    simpa [measureReal_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h_measure_sub
  simpa using
    (tendsto_comp_coe_Ioi_atBot (f := fun y : ℝ ↦ μ.real (Set.Ioc t y)) (a := t)).1 h_real_sub

/-- Helper for Exercise 1.3.1: the anchored cumulative mass function is right-continuous. -/
private theorem anchoredLocallyFiniteMeasureFunction_tendsto_nhdsGT
    (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] (t : ℝ) :
    Tendsto (anchoredLocallyFiniteMeasureFunction μ) (𝓝[>] t)
      (𝓝 (anchoredLocallyFiniteMeasureFunction μ t)) := by
  have hdiff :
      (fun y : ℝ ↦
          anchoredLocallyFiniteMeasureFunction μ y -
            anchoredLocallyFiniteMeasureFunction μ t) =ᶠ[𝓝[>] t]
        (fun y ↦ μ.real (Set.Ioc t y)) := by
    -- On a right-neighborhood of `t`, the interval-increment formula identifies the difference.
    filter_upwards [Ioc_mem_nhdsGT (show t < t + 1 by linarith)] with y hy
    exact anchoredLocallyFiniteMeasureFunction_intervalFormula μ hy.1.le
  have hzero :
      Tendsto
        (fun y : ℝ ↦
          anchoredLocallyFiniteMeasureFunction μ y -
            anchoredLocallyFiniteMeasureFunction μ t)
        (𝓝[>] t) (𝓝 0) := by
    exact Tendsto.congr' hdiff.symm (tendsto_measureReal_Ioc_nhdsGT μ t)
  -- Add back the constant anchor value to recover continuity of the original function.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    hzero.add_const (anchoredLocallyFiniteMeasureFunction μ t)

/-- Helper for Exercise 1.3.1: the anchored cumulative mass function is monotone because its
increments are interval masses. -/
private theorem anchoredLocallyFiniteMeasureFunction_monotone
    (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    Monotone (anchoredLocallyFiniteMeasureFunction μ) := by
  intro a b hab
  rw [← sub_nonneg, anchoredLocallyFiniteMeasureFunction_intervalFormula μ hab]
  exact measureReal_nonneg

/-- Helper for Exercise 1.3.1: the Stieltjes function attached to a locally finite measure by
right-regularizing the anchored cumulative mass function. -/
private noncomputable def locallyFiniteMeasureStieltjesFunction
    (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] : StieltjesFunction ℝ :=
  (anchoredLocallyFiniteMeasureFunction_monotone μ).stieltjesFunction

/-- Helper for Exercise 1.3.1: the Stieltjes regularization agrees pointwise with the anchored
cumulative mass function because that function is already right-continuous. -/
private theorem locallyFiniteMeasureStieltjesFunction_apply
    (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] (t : ℝ) :
    locallyFiniteMeasureStieltjesFunction μ t = anchoredLocallyFiniteMeasureFunction μ t := by
  rw [locallyFiniteMeasureStieltjesFunction, Monotone.stieltjesFunction_eq]
  have h_neBot : (𝓝[>] t) ≠ ⊥ := (show (𝓝[>] t).NeBot from inferInstance).ne
  exact rightLim_eq_of_tendsto h_neBot (anchoredLocallyFiniteMeasureFunction_tendsto_nhdsGT μ t)

/-- Helper for Exercise 1.3.1: the Stieltjes measure of the anchored cumulative mass function
reconstructs the original locally finite measure. -/
private theorem locallyFiniteMeasureStieltjesFunction_measure_eq
    (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    (locallyFiniteMeasureStieltjesFunction μ).measure = μ := by
  apply Measure.ext_of_Ioc _ μ
  intro a b hab
  -- Compare the two measures on half-open intervals, where both have the same increment formula.
  rw [StieltjesFunction.measure_Ioc]
  rw [locallyFiniteMeasureStieltjesFunction_apply μ a,
    locallyFiniteMeasureStieltjesFunction_apply μ b,
    anchoredLocallyFiniteMeasureFunction_intervalFormula μ (le_of_lt hab)]
  simpa [measureReal_def] using ENNReal.ofReal_toReal (measure_Ioc_lt_top.ne : μ (Set.Ioc a b) ≠ ⊤)

/-- Helper for Exercise 1.3.1: every locally finite Borel measure on `ℝ` comes from a Stieltjes
function. -/
private theorem locallyFiniteMeasure_exists_stieltjesFunction
    (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    ∃ F : StieltjesFunction ℝ, F.measure = μ := by
  -- Package the anchored cumulative mass function and use the interval comparison above.
  exact ⟨locallyFiniteMeasureStieltjesFunction μ, locallyFiniteMeasureStieltjesFunction_measure_eq μ⟩

-- Proof sketch: the forward direction uses local finiteness of every Stieltjes measure and the
-- first theorem, while the reverse direction constructs a Stieltjes function from the locally
-- finite weighted atomic measure supplied by bounded summability.
/-- Exercise 1.3.1: The weighted atomic measure `∑' n, α n δ_(x n)` on `ℝ` is a
Lebesgue--Stieltjes measure if and only if the total weight of the atoms in every bounded set
`[-K, K]` is finite. -/
theorem weightedDiracSum_isLebesgueStieltjes_iff_boundedWeightSummable
    (x : ℕ → ℝ) (α : ℕ → NNReal) :
    (∃ F : StieltjesFunction ℝ,
      F.measure = Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n))) ↔
      ∀ K : ℝ, 0 < K → Summable (fun n ↦ if |x n| ≤ K then α n else 0) := by
  simpa [weightedAtomicMeasure] using
    (show (∃ F : StieltjesFunction ℝ, F.measure = weightedAtomicMeasure x α) ↔
        ∀ K : ℝ, 0 < K → Summable (fun n ↦ if |x n| ≤ K then α n else 0) from by
      constructor
      · intro hF
        rcases hF with ⟨F, hF⟩
        letI : IsLocallyFiniteMeasure (weightedAtomicMeasure x α) := by
          rw [← hF]
          infer_instance
        exact
          (weightedDiracSum_isLocallyFiniteMeasure_iff_boundedWeightSummable x α).1
            (show IsLocallyFiniteMeasure (weightedAtomicMeasure x α) by infer_instance)
      · intro hloc
        letI : IsLocallyFiniteMeasure (weightedAtomicMeasure x α) :=
          (weightedDiracSum_isLocallyFiniteMeasure_iff_boundedWeightSummable x α).2 hloc
        exact locallyFiniteMeasure_exists_stieltjesFunction (weightedAtomicMeasure x α))
