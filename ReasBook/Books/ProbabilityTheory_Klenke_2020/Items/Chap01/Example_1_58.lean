/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_30

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal Topology

noncomputable section

/-- The primitive `x ↦ ∫_0^x f(t) dt` attached to a real-valued density `f`. -/
def continuousDensityPrimitive (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ ∫ t in 0..x, f t ∂volume

-- Proof sketch: if `a ≤ b`, rewrite the difference of the two primitives as the interval
-- integral of `f` over `a..b` by the fundamental theorem of calculus, then use the pointwise
-- nonnegativity of `f` to conclude the difference is nonnegative.
theorem continuousDensityPrimitive_monotone (f : ℝ → ℝ) (hf : Continuous f)
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    Monotone (continuousDensityPrimitive f) := by
  intro a b hab
  -- Rewrite the increment of the primitive as the interval integral over `a..b`.
  have hdiff :
      continuousDensityPrimitive f b - continuousDensityPrimitive f a =
        ∫ x in a..b, f x ∂volume := by
    simpa [continuousDensityPrimitive] using
      intervalIntegral.integral_interval_sub_left (f := f) (μ := volume) (a := 0) (b := b) (c := a)
        (hf.intervalIntegrable 0 b) (hf.intervalIntegrable 0 a)
  -- The nonnegative density gives a nonnegative interval integral.
  rw [← sub_nonneg, hdiff]
  exact intervalIntegral.integral_nonneg_of_forall hab hf_nonneg

/- Example 1.58 (1): Item (i). The Stieltjes measure of the identity distribution function is the
Lebesgue measure on `ℝ`. -/
recall Real.volume_eq_stieltjes_id

-- Proof sketch: compare the two measures on half-open intervals `(a, b]`; the Stieltjes interval
-- formula gives `F b - F a`, and the fundamental theorem of calculus rewrites this as the
-- interval integral of `f`, which is exactly the `withDensity` interval formula from
-- Example 1.30(ix).
/-- Item (ii) of Example 1.58. The Lebesgue--Stieltjes measure of the canonical Stieltjes
function built from the primitive `x ↦ ∫ t in 0..x, f t ∂volume` of a continuous nonnegative
density `f` is the measure with density `f` with respect to Lebesgue measure. -/
theorem continuousDensityPrimitive_stieltjesMeasure_eq_withDensity (f : ℝ → ℝ)
    (hf : Continuous f) (hf_nonneg : ∀ x, 0 ≤ f x) :
    ((continuousDensityPrimitive_monotone f hf hf_nonneg).stieltjesFunction).measure =
      volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  let F := continuousDensityPrimitive f
  let hFmono : Monotone F := continuousDensityPrimitive_monotone f hf hf_nonneg
  have hFcontWithin : ∀ x : ℝ, ContinuousWithinAt F (Ici x) x := by
    intro x
    have hIcc : ContinuousWithinAt F (Icc x (x + 1)) x := by
      -- The primitive is continuous on each compact interval containing `x`.
      simpa [F, continuousDensityPrimitive] using
        (intervalIntegral.continuousWithinAt_primitive (μ := volume) (f := f) (a := 0) (b₀ := x)
          (b₁ := x)
          (b₂ := x + 1) (measure_singleton x)
          (hf.intervalIntegrable (min 0 x) (max 0 (x + 1))))
    exact (continuousWithinAt_Icc_iff_Ici (f := F) (a := x) (b := x + 1) (by linarith)).1 hIcc
  refine Measure.ext_of_Ioc _ _ fun a b hab ↦ ?_
  -- Evaluate the Stieltjes interval mass through the actual primitive values.
  rw [StieltjesFunction.measure_Ioc]
  rw [Monotone.stieltjesFunction_eq hFmono, ContinuousWithinAt.rightLim_eq (hFcontWithin b)]
  rw [Monotone.stieltjesFunction_eq hFmono, ContinuousWithinAt.rightLim_eq (hFcontWithin a)]
  have hdiff : F b - F a = ∫ x in a..b, f x ∂volume := by
    simpa [F, continuousDensityPrimitive] using
      intervalIntegral.integral_interval_sub_left (f := f) (μ := volume) (a := 0) (b := b) (c := a)
        (hf.intervalIntegrable 0 b) (hf.intervalIntegrable 0 a)
  rw [hdiff]
  simpa using (continuousDensity_measure_Ioc f hf hf_nonneg a b).symm

/-- Helper for Example 1.58: for a finite measure on `ℝ`, the cumulative mass on the rays `Iic x`
is monotone in `x`. -/
private theorem measureDistributionFunction_monotone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Monotone (fun x : ℝ ↦ μ.real (Iic x)) := by
  intro a b hab
  exact measureReal_mono (Iic_subset_Iic.mpr hab)

/-- Helper for Example 1.58: the finite-measure distribution function viewed as a Stieltjes
function. -/
private noncomputable def measureDistributionFunction (μ : Measure ℝ) [IsFiniteMeasure μ] :
    StieltjesFunction ℝ :=
  (measureDistributionFunction_monotone μ).stieltjesFunction

/-- Helper for Example 1.58: the cumulative mass function of a finite measure is right-continuous
on `ℝ`. -/
private theorem tendsto_measureReal_Iic_nhdsGT (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Tendsto (fun y : ℝ ↦ μ.real (Iic y)) (𝓝[>] x) (𝓝 (μ.real (Iic x))) := by
  have h_measure_sub :
      Tendsto (fun y : Ioi x => μ (Iic (y : ℝ))) atBot
        (𝓝 (μ (⋂ y : Ioi x, Iic (y : ℝ)))) := by
    refine tendsto_measure_iInter_atBot (μ := μ)
      (fun _ ↦ measurableSet_Iic.nullMeasurableSet) ?_ ?_
    · intro a b hab
      exact Iic_subset_Iic.mpr hab
    · refine ⟨⟨x + 1, lt_add_of_pos_right x zero_lt_one⟩, measure_ne_top μ _⟩
  have h_inter : (⋂ y : Ioi x, Iic (y : ℝ)) = Iic x := by
    ext z
    constructor
    · intro hz
      simp only [mem_iInter, mem_Iic] at hz ⊢
      by_contra hzx
      have hzx' : x < z := lt_of_not_ge hzx
      obtain ⟨y, hxy, hyz⟩ := exists_between hzx'
      exact not_le_of_gt hyz (hz ⟨y, hxy⟩)
    · intro hz
      simp only [mem_iInter, mem_Iic] at hz ⊢
      intro y
      exact hz.trans y.2.le
  have h_real_sub :
      Tendsto (fun y : Ioi x => μ.real (Iic (y : ℝ))) atBot
        (𝓝 (μ.real (Iic x))) := by
    rw [h_inter] at h_measure_sub
    simpa [measureReal_def] using
      (ENNReal.tendsto_toReal (measure_ne_top μ (Iic x))).comp h_measure_sub
  simpa using
    (tendsto_comp_coe_Ioi_atBot (f := fun y : ℝ ↦ μ.real (Iic y)) (a := x)).1 h_real_sub

/-- Helper for Example 1.58: the cumulative mass function of a finite measure tends to `0` at
`-∞`. -/
private theorem tendsto_measureReal_Iic_atBot (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (fun x : ℝ ↦ μ.real (Iic x)) atBot (𝓝 0) := by
  have h_measure :
      Tendsto (fun x : ℝ ↦ μ (Iic x)) atBot (𝓝 (μ (⋂ y : ℝ, Iic y))) := by
    refine tendsto_measure_iInter_atBot (μ := μ)
      (fun _ ↦ measurableSet_Iic.nullMeasurableSet) ?_ ?_
    · intro a b hab
      exact Iic_subset_Iic.mpr hab
    · exact ⟨0, measure_ne_top μ _⟩
  have h_inter : (⋂ y : ℝ, Iic y) = (∅ : Set ℝ) := by
    ext z
    constructor
    · intro hz
      simp only [mem_iInter, mem_Iic] at hz
      have h_lt : z - 1 < z := by linarith
      exact (not_le_of_gt h_lt) (hz (z - 1))
    · intro hz
      simp at hz
  rw [h_inter, measure_empty] at h_measure
  simpa [measureReal_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h_measure

/-- Helper for Example 1.58: the finite-measure distribution function evaluates to the cumulative
mass function `x ↦ μ.real (Iic x)`. -/
private theorem measureDistributionFunction_apply (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    measureDistributionFunction μ x = μ.real (Iic x) := by
  rw [measureDistributionFunction, Monotone.stieltjesFunction_eq]
  have h_neBot : (𝓝[>] x) ≠ ⊥ := (show (𝓝[>] x).NeBot from inferInstance).ne
  exact rightLim_eq_of_tendsto h_neBot (tendsto_measureReal_Iic_nhdsGT μ x)

/-- The atomic step function `x ↦ ∑ n αₙ 1_[xₙ,∞)(x)` attached to a summable family of
nonnegative weights. -/
def atomicDistributionStepFunction (x : ℕ → ℝ) (α : ℕ → NNReal) : ℝ → ℝ :=
  fun t ↦ ∑' n, (α n : ℝ) * Set.indicator (Set.Ici (x n)) (fun _ ↦ (1 : ℝ)) t

/-- Helper for Example 1.58: the weighted atomic measure `∑' n, α n δ_(x n)` has finite total
mass as soon as the weights are summable. -/
private theorem weightedAtomicMeasure_isFinite (x : ℕ → ℝ) (α : ℕ → NNReal)
    (hα : Summable α) :
    IsFiniteMeasure (Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n))) := by
  refine ⟨?_⟩
  -- Compute the total mass on `univ` by summing the weights.
  have hmass :
      (Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n))) Set.univ =
        ∑' n, (α n : ℝ≥0∞) := by
    rw [Measure.sum_apply _ MeasurableSet.univ]
    refine tsum_congr fun n ↦ ?_
    rw [Measure.smul_apply, Measure.dirac_apply]
    simp
  rw [hmass]
  exact lt_top_iff_ne_top.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mpr hα)

/-- Helper for Example 1.58: the explicit weighted step function agrees with the cumulative mass of
the weighted atomic measure on the rays `(-∞, t]`. -/
private theorem atomicDistributionStepFunction_eq_measureReal_Iic
    (x : ℕ → ℝ) (α : ℕ → NNReal) (t : ℝ) :
    atomicDistributionStepFunction x α t =
      (Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n))).real (Iic t) := by
  -- Expand both sides into the same weighted indicator series.
  have hmass :
      (Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n))) (Iic t) =
        ∑' n, if x n ≤ t then (α n : ℝ≥0∞) else 0 := by
    rw [Measure.sum_apply _ measurableSet_Iic]
    refine tsum_congr fun n ↦ ?_
    by_cases hxt : x n ≤ t
    · rw [Measure.smul_apply, Measure.dirac_apply]
      simp [hxt]
    · simp [Measure.smul_apply, hxt]
  rw [atomicDistributionStepFunction, Measure.real_def, hmass, ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun a ↦ ?_
    by_cases hxt : x a ≤ t
    · simp [hxt]
    · simp [hxt]
  · intro n
    by_cases hxt : x n ≤ t
    · simp [hxt]
    · simp [hxt]

-- Proof sketch: each summand `t ↦ α n * 1_[x n, ∞)(t)` is monotone because `α n ≥ 0`, and the
-- summability hypothesis allows passage from the termwise monotonicity to monotonicity of the
-- infinite series.
theorem atomicDistributionStepFunction_monotone (x : ℕ → ℝ) (α : ℕ → NNReal)
    (hα : Summable α) :
    Monotone (atomicDistributionStepFunction x α) := by
  let μ : Measure ℝ := Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n))
  letI : IsFiniteMeasure μ := weightedAtomicMeasure_isFinite x α hα
  intro a b hab
  -- Identify the step function with the cumulative mass function of `μ`.
  rw [atomicDistributionStepFunction_eq_measureReal_Iic x α a]
  rw [atomicDistributionStepFunction_eq_measureReal_Iic x α b]
  exact measureReal_mono (Iic_subset_Iic.mpr hab)

/-- Helper for Example 1.58: the finite-measure distribution function reconstructs the original
finite measure. -/
private theorem measureDistributionFunction_measure_eq (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (measureDistributionFunction μ).measure = μ := by
  have h_apply :
      (measureDistributionFunction μ : ℝ → ℝ) = fun x ↦ μ.real (Iic x) := by
    funext x
    exact measureDistributionFunction_apply μ x
  have h_atBot : Tendsto (measureDistributionFunction μ) atBot (𝓝 0) := by
    -- The finite-measure cdf vanishes at `-∞`.
    simpa [h_apply] using tendsto_measureReal_Iic_atBot μ
  -- Compare both measures on the generating rays `(-∞, a]`.
  apply (Measure.ext_of_Iic μ (measureDistributionFunction μ).measure fun a ↦ ?_).symm
  rw [StieltjesFunction.measure_Iic _ h_atBot, sub_zero, measureDistributionFunction_apply,
    ofReal_measureReal]

-- Proof sketch: evaluate the weighted Dirac sum and the Stieltjes measure on half-open intervals
-- `(a, b]`; both sides compute the total weight of the atoms in `(a, b]`, and uniqueness of the
-- Stieltjes measure then gives equality.
/-- Item (iii) of Example 1.58. The atomic step function
`x ↦ ∑' n, α n * 1_[x n,∞)(x)` is the distribution function of the weighted atomic measure
`∑' n, α n δ_(x n)`. -/
theorem atomicDistributionStepFunction_stieltjesMeasure_eq_sum_dirac
    (x : ℕ → ℝ) (α : ℕ → NNReal)
    (hα : Summable α) :
    ((atomicDistributionStepFunction_monotone x α hα).stieltjesFunction).measure =
      Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n)) := by
  let μ : Measure ℝ := Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n))
  letI : IsFiniteMeasure μ := weightedAtomicMeasure_isFinite x α hα
  have hfun : atomicDistributionStepFunction x α = measureDistributionFunction μ := by
    funext t
    rw [measureDistributionFunction_apply]
    exact atomicDistributionStepFunction_eq_measureReal_Iic x α t
  have hstieltjes :
      (atomicDistributionStepFunction_monotone x α hα).stieltjesFunction =
        measureDistributionFunction μ := by
    ext t
    -- Route correction: identify the right-limit regularization with the already right-continuous
    -- finite-measure distribution function.
    rw [Monotone.stieltjesFunction_eq (atomicDistributionStepFunction_monotone x α hα), hfun]
    exact ContinuousWithinAt.rightLim_eq ((measureDistributionFunction μ).right_continuous t)
  -- Once the two Stieltjes functions agree, the reconstruction theorem finishes the measure
  -- equality.
  rw [hstieltjes]
  exact measureDistributionFunction_measure_eq μ

-- Proof sketch: compute the total mass on `univ` by summing the Dirac masses and use the
-- summability of the nonnegative coefficients to show that this total mass is finite.
instance (x : ℕ → ℝ) (α : ℕ → NNReal) (hα : Summable α) :
    IsFiniteMeasure (Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n))) := by
  exact weightedAtomicMeasure_isFinite x α hα

-- Proof sketch: for the forward implication, construct the counting distribution function from the
-- locally finite sequence and verify that its Stieltjes measure is the given counting measure; for
-- the reverse implication, use the finiteness of the Stieltjes mass of bounded intervals to rule
-- out cluster points.
/-- Helper for Example 1.58: the counting Dirac sum is the pushforward of counting measure on `ℕ`
along the sequence `x`. -/
private theorem countingDiracSum_eq_map_count (x : ℕ → ℝ) :
    Measure.sum (fun n ↦ Measure.dirac (x n)) = (Measure.count : Measure ℕ).map x := by
  ext s hs
  have hpre : MeasurableSet (x ⁻¹' s) := (measurable_of_countable x) hs
  -- Rewrite both sides as the same counting series on the preimage of `s`.
  rw [Measure.sum_apply_of_countable]
  calc
    ∑' n, Measure.dirac (x n) s
      = ∑' n, (x ⁻¹' s).indicator (fun n ↦ (Measure.count : Measure ℕ) {n}) n := by
          refine tsum_congr fun n ↦ ?_
          by_cases hn : x n ∈ s
          · simp [Measure.dirac_apply_of_mem, hn]
          · simp [Measure.dirac_apply, hn]
    _ = (Measure.count : Measure ℕ) (x ⁻¹' s) := by
          simpa using
            (Measure.tsum_indicator_apply_singleton (μ := (Measure.count : Measure ℕ))
              (s := x ⁻¹' s) hpre)
    _ = ((Measure.count : Measure ℕ).map x) s := by
          symm
          rw [Measure.map_apply (measurable_of_countable x) hs]

/-- Helper for Example 1.58: if the sequence `x` has no cluster point, then every closed interval
contains only finitely many values of `x`. -/
private theorem finitePreimageIcc_of_noLimitPoint (x : ℕ → ℝ)
    (hno : ∀ y : ℝ, ¬ MapClusterPt y atTop x) {a b : ℝ} (_hab : a ≤ b) :
    {n : ℕ | x n ∈ Set.Icc a b}.Finite := by
  by_contra hfinite
  have hinfinite : {n : ℕ | x n ∈ Set.Icc a b}.Infinite :=
    Set.not_finite.mp hfinite
  have hfreq : ∃ᶠ n in atTop, x n ∈ Set.Icc a b :=
    (Nat.frequently_atTop_iff_infinite).2 hinfinite
  obtain ⟨y, hy, hcluster⟩ :=
    (isCompact_Icc.exists_mapClusterPt_of_frequently hfreq)
  exact hno y hcluster

/-- Helper for Example 1.58: bounded half-open intervals have finite counting mass under the
no-limit-point hypothesis. -/
private theorem countPreimageIoc_neTop_of_localFinite (x : ℕ → ℝ)
    (hloc : ∀ {a b : ℝ}, a ≤ b → {n : ℕ | x n ∈ Set.Icc a b}.Finite) {a b : ℝ}
    (hab : a ≤ b) :
    (Measure.count : Measure ℕ) (x ⁻¹' Set.Ioc a b) ≠ ⊤ := by
  have hfinite :
      {n : ℕ | x n ∈ Set.Ioc a b}.Finite := by
    refine (hloc hab).subset ?_
    intro n hn
    exact ⟨le_of_lt hn.1, hn.2⟩
  exact (Measure.count_apply_lt_top.mpr hfinite).ne

/-- Helper for Example 1.58: the anchored counting function attached to `x`, normalized so that
its increments over `(a, b]` count the atoms of `x` in that interval. -/
private def anchoredCountingFunction (x : ℕ → ℝ) : ℝ → ℝ :=
  fun t ↦
    if 0 ≤ t then
      (Measure.count : Measure ℕ).real (x ⁻¹' Set.Ioc 0 t)
    else
      -((Measure.count : Measure ℕ).real (x ⁻¹' Set.Ioc t 0))

/-- Helper for Example 1.58: the anchored counting function has the expected interval increment
formula on `(a, b]`. -/
private theorem anchoredCountingFunction_intervalFormula (x : ℕ → ℝ)
    (hloc : ∀ {a b : ℝ}, a ≤ b → {n : ℕ | x n ∈ Set.Icc a b}.Finite) {a b : ℝ}
    (hab : a ≤ b) :
    anchoredCountingFunction x b - anchoredCountingFunction x a =
      (Measure.count : Measure ℕ).real (x ⁻¹' Set.Ioc a b) := by
  let μ : Measure ℕ := Measure.count
  let mx : Measurable x := measurable_of_countable x
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := le_trans ha hab
    have hpre_ab : MeasurableSet (x ⁻¹' Set.Ioc a b) := mx measurableSet_Ioc
    have hne_0a : μ (x ⁻¹' Set.Ioc 0 a) ≠ ⊤ :=
      countPreimageIoc_neTop_of_localFinite x hloc ha
    have hne_ab : μ (x ⁻¹' Set.Ioc a b) ≠ ⊤ :=
      countPreimageIoc_neTop_of_localFinite x hloc hab
    have hunion :
        x ⁻¹' Set.Ioc 0 b = (x ⁻¹' Set.Ioc 0 a) ∪ (x ⁻¹' Set.Ioc a b) := by
      ext n
      constructor <;> intro hn
      · by_cases hna : x n ≤ a
        · exact Or.inl ⟨hn.1, hna⟩
        · exact Or.inr ⟨lt_of_not_ge hna, hn.2⟩
      · rcases hn with hn | hn
        · exact ⟨hn.1, le_trans hn.2 hab⟩
        · exact ⟨lt_of_le_of_lt ha hn.1, hn.2⟩
    have hdisj :
        Disjoint (x ⁻¹' Set.Ioc 0 a) (x ⁻¹' Set.Ioc a b) := by
      rw [Set.disjoint_left]
      intro n hn0a hnab
      exact not_lt_of_ge hn0a.2 hnab.1
    have hadd :
        μ.real (x ⁻¹' Set.Ioc 0 b) =
          μ.real (x ⁻¹' Set.Ioc 0 a) + μ.real (x ⁻¹' Set.Ioc a b) := by
      rw [measureReal_def, measureReal_def, measureReal_def, hunion, measure_union hdisj hpre_ab,
        ENNReal.toReal_add hne_0a hne_ab]
    -- On the nonnegative side, increments split at `a`.
    simp [anchoredCountingFunction, ha, hb]
    linarith
  · by_cases hb : 0 ≤ b
    · have hpre_0b : MeasurableSet (x ⁻¹' Set.Ioc 0 b) := mx measurableSet_Ioc
      have hne_a0 : μ (x ⁻¹' Set.Ioc a 0) ≠ ⊤ :=
        countPreimageIoc_neTop_of_localFinite x hloc (by linarith)
      have hne_0b : μ (x ⁻¹' Set.Ioc 0 b) ≠ ⊤ :=
        countPreimageIoc_neTop_of_localFinite x hloc hb
      have hunion :
          x ⁻¹' Set.Ioc a b = (x ⁻¹' Set.Ioc a 0) ∪ (x ⁻¹' Set.Ioc 0 b) := by
        ext n
        constructor <;> intro hn
        · by_cases hnonpos : x n ≤ 0
          · exact Or.inl ⟨hn.1, hnonpos⟩
          · exact Or.inr ⟨lt_of_not_ge hnonpos, hn.2⟩
        · rcases hn with hn | hn
          · exact ⟨hn.1, le_trans hn.2 hb⟩
          · exact ⟨lt_trans (lt_of_not_ge ha) hn.1, hn.2⟩
      have hdisj :
          Disjoint (x ⁻¹' Set.Ioc a 0) (x ⁻¹' Set.Ioc 0 b) := by
        rw [Set.disjoint_left]
        intro n hna0 hn0b
        exact not_lt_of_ge hna0.2 hn0b.1
      have hadd :
          μ.real (x ⁻¹' Set.Ioc a b) =
            μ.real (x ⁻¹' Set.Ioc a 0) + μ.real (x ⁻¹' Set.Ioc 0 b) := by
        rw [measureReal_def, measureReal_def, measureReal_def, hunion, measure_union hdisj hpre_0b,
          ENNReal.toReal_add hne_a0 hne_0b]
      -- Crossing the anchor at `0` splits the interval into two disjoint pieces.
      simp [anchoredCountingFunction, ha, hb]
      linarith
    · have hb' : b ≤ 0 := le_of_not_ge hb
      have hpre_b0 : MeasurableSet (x ⁻¹' Set.Ioc b 0) := mx measurableSet_Ioc
      have hne_ab : μ (x ⁻¹' Set.Ioc a b) ≠ ⊤ :=
        countPreimageIoc_neTop_of_localFinite x hloc hab
      have hne_b0 : μ (x ⁻¹' Set.Ioc b 0) ≠ ⊤ :=
        countPreimageIoc_neTop_of_localFinite x hloc hb'
      have hunion :
          x ⁻¹' Set.Ioc a 0 = (x ⁻¹' Set.Ioc a b) ∪ (x ⁻¹' Set.Ioc b 0) := by
        ext n
        constructor <;> intro hn
        · by_cases hnb : x n ≤ b
          · exact Or.inl ⟨hn.1, hnb⟩
          · exact Or.inr ⟨lt_of_not_ge hnb, hn.2⟩
        · rcases hn with hn | hn
          · exact ⟨hn.1, le_trans hn.2 hb'⟩
          · exact ⟨lt_of_le_of_lt hab hn.1, hn.2⟩
      have hdisj :
          Disjoint (x ⁻¹' Set.Ioc a b) (x ⁻¹' Set.Ioc b 0) := by
        rw [Set.disjoint_left]
        intro n hnab hnb0
        exact not_lt_of_ge hnab.2 hnb0.1
      have hadd :
          μ.real (x ⁻¹' Set.Ioc a 0) =
            μ.real (x ⁻¹' Set.Ioc a b) + μ.real (x ⁻¹' Set.Ioc b 0) := by
        rw [measureReal_def, measureReal_def, measureReal_def, hunion, measure_union hdisj hpre_b0,
          ENNReal.toReal_add hne_ab hne_b0]
      -- On the negative side, increments split at `b`.
      simp [anchoredCountingFunction, ha, hb]
      linarith

/-- Helper for Example 1.58: the anchored counting function is monotone once every bounded
interval contains only finitely many values of `x`. -/
private theorem anchoredCountingFunction_monotone (x : ℕ → ℝ)
    (hloc : ∀ {a b : ℝ}, a ≤ b → {n : ℕ | x n ∈ Set.Icc a b}.Finite) :
    Monotone (anchoredCountingFunction x) := by
  intro a b hab
  -- The interval increment is a nonnegative counting mass.
  rw [← sub_nonneg, anchoredCountingFunction_intervalFormula x hloc hab]
  exact measureReal_nonneg

/-- Helper for Example 1.58: a finite set contained in `(t, u]` leaves a right-neighborhood of
`t` inside `(t, u]` with no points of the set. -/
private theorem finiteSet_exists_rightGapWithin {s : Set ℝ} (hs : s.Finite) {t u : ℝ}
    (htu : t < u) (hsub : s ⊆ Set.Ioc t u) :
    ∃ ε > 0, ε < u - t ∧ ∀ y ∈ s, y ∉ Set.Ioc t (t + ε) := by
  classical
  by_cases hs_nonempty : s.Nonempty
  · let fs : Finset ℝ := hs.toFinset
    have hfs_nonempty : fs.Nonempty := by
      simpa [fs] using hs_nonempty
    let c : ℝ := fs.min' hfs_nonempty
    have hc_mem : c ∈ s := by
      simpa [fs] using (hs.mem_toFinset.mp (Finset.min'_mem fs hfs_nonempty))
    have htc : t < c := (hsub hc_mem).1
    have hc_lower : ∀ y ∈ s, c ≤ y := by
      intro y hy
      have hy_finset : y ∈ fs := hs.mem_toFinset.mpr hy
      exact Finset.min'_le fs y hy_finset
    let ε : ℝ := min ((u - t) / 2) ((c - t) / 2)
    refine ⟨ε, ?_, ?_, ?_⟩
    · have hhalf_ut : 0 < (u - t) / 2 := by linarith
      have hhalf_ct : 0 < (c - t) / 2 := by linarith
      exact lt_min hhalf_ut hhalf_ct
    · have hε : ε ≤ (u - t) / 2 := min_le_left _ _
      linarith
    · intro y hy hyIoc
      have hyc : c ≤ y := hc_lower y hy
      have hylt : y < c := by
        have hε : ε ≤ (c - t) / 2 := min_le_right _ _
        have hylt' : y ≤ t + ε := hyIoc.2
        have hylt'' : y < t + (c - t) / 2 := by
          linarith
        linarith
      exact not_lt_of_ge hyc hylt
  · refine ⟨(u - t) / 2, by linarith, by linarith, ?_⟩
    · intro y hy
      exact (hs_nonempty ⟨y, hy⟩).elim

/-- Helper for Example 1.58: the anchored counting function is eventually constant on a sufficiently
small right-neighborhood of each point. -/
private theorem anchoredCountingFunction_eventuallyEq_right (x : ℕ → ℝ)
    (hloc : ∀ {a b : ℝ}, a ≤ b → {n : ℕ | x n ∈ Set.Icc a b}.Finite) (t : ℝ) :
    ∃ ε > 0,
      Set.Icc t (t + ε) ∈ 𝓝[Set.Ici t] t ∧
        ∀ y ∈ Set.Icc t (t + ε), anchoredCountingFunction x y = anchoredCountingFunction x t := by
  by_cases ht : 0 ≤ t
  · let s : Set ℝ := x '' {n : ℕ | x n ∈ Set.Ioc t (t + 1)}
    have hs_finite : s.Finite := by
      refine (hloc (show t ≤ t + 1 by linarith)).subset ?_ |>.image x
      intro n hn
      exact ⟨le_of_lt hn.1, hn.2⟩
    have hs_subset : s ⊆ Set.Ioc t (t + 1) := by
      intro y hy
      rcases hy with ⟨n, hn, rfl⟩
      exact hn
    obtain ⟨ε, hεpos, hεlt, hgap⟩ :=
      finiteSet_exists_rightGapWithin hs_finite (show t < t + 1 by linarith) hs_subset
    refine ⟨ε, hεpos, ?_, ?_⟩
    have hmem : Set.Icc t (t + ε) ∈ 𝓝[Set.Ici t] t := by
      rw [mem_nhdsGE_iff_exists_Icc_subset]
      exact ⟨t + ε, by linarith, subset_rfl⟩
    · exact hmem
    · intro y hyIcc
      have hy_nonneg : 0 ≤ y := le_trans ht hyIcc.1
      have hempty : x ⁻¹' Set.Ioc t y = ∅ := by
        ext n
        constructor
        · intro hn
          have hx_image : x n ∈ s := by
            refine ⟨n, ?_, rfl⟩
            have hy_upper : y ≤ t + 1 := by linarith [hyIcc.2, hεlt]
            exact ⟨hn.1, le_trans hn.2 hy_upper⟩
          exact False.elim (hgap (x n) hx_image ⟨hn.1, by linarith [hn.2, hyIcc.2]⟩)
        · intro hn
          simp at hn
      have hunion :
          x ⁻¹' Set.Ioc 0 y = (x ⁻¹' Set.Ioc 0 t) ∪ (x ⁻¹' Set.Ioc t y) := by
        ext n
        constructor <;> intro hn
        · by_cases hnt : x n ≤ t
          · exact Or.inl ⟨hn.1, hnt⟩
          · exact Or.inr ⟨lt_of_not_ge hnt, hn.2⟩
        · rcases hn with hn | hn
          · exact ⟨hn.1, le_trans hn.2 hyIcc.1⟩
          · exact ⟨lt_of_le_of_lt ht hn.1, hn.2⟩
      -- With no atoms in `(t, y]`, the positive-side counting formula does not change.
      rw [anchoredCountingFunction, anchoredCountingFunction, if_pos hy_nonneg, if_pos ht]
      rw [hunion, hempty, union_empty]
  · have ht_neg : t < 0 := lt_of_not_ge ht
    let s : Set ℝ := x '' {n : ℕ | x n ∈ Set.Ioc t 0}
    have hs_finite : s.Finite := by
      refine (hloc (show t ≤ 0 by linarith)).subset ?_ |>.image x
      intro n hn
      exact ⟨le_of_lt hn.1, hn.2⟩
    have hs_subset : s ⊆ Set.Ioc t 0 := by
      intro y hy
      rcases hy with ⟨n, hn, rfl⟩
      exact hn
    obtain ⟨ε, hεpos, hεlt, hgap⟩ :=
      finiteSet_exists_rightGapWithin hs_finite ht_neg hs_subset
    refine ⟨ε, hεpos, ?_, ?_⟩
    have hmem : Set.Icc t (t + ε) ∈ 𝓝[Set.Ici t] t := by
      rw [mem_nhdsGE_iff_exists_Icc_subset]
      exact ⟨t + ε, by linarith, subset_rfl⟩
    · exact hmem
    · intro y hyIcc
      have hy_neg : y < 0 := by linarith [hyIcc.2, hεlt]
      have hempty : x ⁻¹' Set.Ioc t y = ∅ := by
        ext n
        constructor
        · intro hn
          have hx_image : x n ∈ s := by
            refine ⟨n, ?_, rfl⟩
            exact ⟨hn.1, le_trans hn.2 hy_neg.le⟩
          exact False.elim (hgap (x n) hx_image ⟨hn.1, by linarith [hn.2, hyIcc.2]⟩)
        · intro hn
          simp at hn
      have hunion :
          x ⁻¹' Set.Ioc t 0 = (x ⁻¹' Set.Ioc t y) ∪ (x ⁻¹' Set.Ioc y 0) := by
        ext n
        constructor <;> intro hn
        · by_cases hny : x n ≤ y
          · exact Or.inl ⟨hn.1, hny⟩
          · exact Or.inr ⟨lt_of_not_ge hny, hn.2⟩
        · rcases hn with hn | hn
          · exact ⟨hn.1, le_trans hn.2 hy_neg.le⟩
          · exact ⟨lt_of_le_of_lt hyIcc.1 hn.1, hn.2⟩
      -- With no atoms in `(t, y]`, the negative-side counting formula also stays fixed.
      rw [anchoredCountingFunction, anchoredCountingFunction, if_neg (show ¬ 0 ≤ y by linarith),
        if_neg ht]
      rw [hunion, hempty, empty_union]

/-- Helper for Example 1.58: the anchored counting function is right-continuous. -/
private theorem anchoredCountingFunction_continuousWithinAt_Ici (x : ℕ → ℝ)
    (hloc : ∀ {a b : ℝ}, a ≤ b → {n : ℕ | x n ∈ Set.Icc a b}.Finite) (t : ℝ) :
    ContinuousWithinAt (anchoredCountingFunction x) (Set.Ici t) t := by
  obtain ⟨ε, hεpos, hmem, hconst⟩ := anchoredCountingFunction_eventuallyEq_right x hloc t
  have hEq :
      anchoredCountingFunction x =ᶠ[𝓝[Set.Ici t] t]
        fun _ : ℝ ↦ anchoredCountingFunction x t := by
    refine Filter.mem_of_superset hmem ?_
    intro y hy
    exact hconst y hy
  -- Eventual constancy on a right-neighborhood gives right continuity.
  simpa [ContinuousWithinAt] using hEq.tendsto

/-- Helper for Example 1.58: the anchored counting function defines the Stieltjes function whose
measure realizes the counting Dirac sum. -/
private noncomputable def countingDiracStieltjesFunction (x : ℕ → ℝ)
    (hno : ∀ y : ℝ, ¬ MapClusterPt y atTop x) : StieltjesFunction ℝ :=
  { toFun := anchoredCountingFunction x
    mono' := anchoredCountingFunction_monotone x (finitePreimageIcc_of_noLimitPoint x hno)
    right_continuous' :=
      anchoredCountingFunction_continuousWithinAt_Ici x
        (finitePreimageIcc_of_noLimitPoint x hno) }

/-- Helper for Example 1.58: the anchored Stieltjes function evaluates to the anchored counting
function. -/
private theorem countingDiracStieltjesFunction_apply (x : ℕ → ℝ)
    (hno : ∀ y : ℝ, ¬ MapClusterPt y atTop x) (t : ℝ) :
    countingDiracStieltjesFunction x hno t = anchoredCountingFunction x t := rfl

/-- Helper for Example 1.58: the Stieltjes measure associated to the anchored counting function is
exactly the counting Dirac sum. -/
private theorem countingDiracStieltjesFunction_measure_eq_sum_dirac (x : ℕ → ℝ)
    (hno : ∀ y : ℝ, ¬ MapClusterPt y atTop x) :
    (countingDiracStieltjesFunction x hno).measure = Measure.sum (fun n ↦ Measure.dirac (x n)) := by
  let hloc : ∀ {a b : ℝ}, a ≤ b → {n : ℕ | x n ∈ Set.Icc a b}.Finite :=
    finitePreimageIcc_of_noLimitPoint x hno
  -- Route correction: compare both measures on `Ioc` intervals through the canonical counting
  -- bridge, instead of expanding the Dirac sum directly in the main theorem.
  apply (Measure.ext_of_Ioc' (countingDiracStieltjesFunction x hno).measure
    (Measure.sum (fun n ↦ Measure.dirac (x n))))
  · intro a b hab
    rw [StieltjesFunction.measure_Ioc]
    simp
  · intro a b hab
    rw [StieltjesFunction.measure_Ioc, countingDiracSum_eq_map_count,
      Measure.map_apply (measurable_of_countable x) measurableSet_Ioc]
    have hfinite :
        (Measure.count : Measure ℕ) (x ⁻¹' Set.Ioc a b) ≠ ⊤ :=
      countPreimageIoc_neTop_of_localFinite x hloc (le_of_lt hab)
    -- The Stieltjes interval mass is the finite counting mass of `(a, b]`.
    rw [countingDiracStieltjesFunction_apply, countingDiracStieltjesFunction_apply,
      anchoredCountingFunction_intervalFormula x hloc (le_of_lt hab)]
    simpa [measureReal_def] using ENNReal.ofReal_toReal hfinite

/-- Example 1.58 (4): Item (iv). The counting measure `∑' n, δ_(x n)` is a Lebesgue--Stieltjes
measure exactly when the sequence `(x n)` has no limit point, under the standing σ-finiteness
assumption on the counting measure. -/
theorem countingDiracSum_isLebesgueStieltjes_iff_noLimitPoint (x : ℕ → ℝ)
    (_hσ : SigmaFinite (Measure.sum fun n ↦ Measure.dirac (x n))) :
    (∃ F : StieltjesFunction ℝ, F.measure = Measure.sum (fun n ↦ Measure.dirac (x n))) ↔
      ∀ y : ℝ, ¬ MapClusterPt y atTop x := by
  constructor
  · intro hF y hy
    rcases hF with ⟨F, hF⟩
    have hfreq :
        ∃ᶠ n in atTop, x n ∈ Set.Ioo (y - 1) (y + 1) := by
      exact (mapClusterPt_iff_frequently.1 hy) (Set.Ioo (y - 1) (y + 1))
        (Ioo_mem_nhds (by linarith) (by linarith))
    have hinfIoo : {n : ℕ | x n ∈ Set.Ioo (y - 1) (y + 1)}.Infinite :=
      (Nat.frequently_atTop_iff_infinite).1 hfreq
    have hinfIoc : {n : ℕ | x n ∈ Set.Ioc (y - 1) (y + 1)}.Infinite := by
      refine hinfIoo.mono ?_
      intro n hn
      exact ⟨hn.1, hn.2.le⟩
    have htop :
        (Measure.sum (fun n ↦ Measure.dirac (x n))) (Set.Ioc (y - 1) (y + 1)) = ⊤ := by
      rw [countingDiracSum_eq_map_count, Measure.map_apply (measurable_of_countable x)
        measurableSet_Ioc, Measure.count_apply_eq_top]
      exact hinfIoc
    have hfinite :
        (Measure.sum (fun n ↦ Measure.dirac (x n))) (Set.Ioc (y - 1) (y + 1)) ≠ ⊤ := by
      rw [← hF, StieltjesFunction.measure_Ioc]
      simp
    exact hfinite htop
  · intro hno
    refine ⟨countingDiracStieltjesFunction x hno,
      countingDiracStieltjesFunction_measure_eq_sum_dirac x hno⟩

-- Proof sketch: derive the total mass from `StieltjesFunction.measure_univ`; the hypothesis says
-- that the difference between the right and left tails tends to `1`, so the total mass of `F` is
-- `1`, which is exactly the probability-measure condition.
/-- Helper for Example 1.58: if `F x - F (-x)` tends to `1`, then the total mass of `F.measure`
is exactly `1`. -/
private theorem measure_univ_eq_one_of_tendsto_sub_comp_neg (F : StieltjesFunction ℝ)
    (h : Tendsto (fun x ↦ F x - F (-x)) atTop (𝓝 1)) :
    F.measure Set.univ = 1 := by
  have hltTwo : ∀ᶠ x in atTop, F x - F (-x) < 2 := by
    exact h (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  rcases Filter.eventually_atTop.1 hltTwo with ⟨x₀, hx₀⟩
  let c : ℝ := max x₀ 0
  have h_bddAbove : BddAbove (Set.range F) := by
    refine ⟨max (F c) (F 0 + 2), ?_⟩
    rintro y ⟨x, rfl⟩
    by_cases hcx : c ≤ x
    · have hdiff : F x - F (-x) < 2 := hx₀ x (le_trans (le_max_left x₀ 0) hcx)
      have hc0 : (0 : ℝ) ≤ c := le_max_right x₀ 0
      have hnegx : -x ≤ 0 := by linarith
      have hFx : F x ≤ F 0 + 2 := by
        have hstep : F x < F (-x) + 2 := by linarith
        exact hstep.le.trans <| by simpa [add_comm] using add_le_add_right (F.mono hnegx) 2
      exact le_max_of_le_right hFx
    · exact le_max_of_le_left (F.mono (le_of_not_ge hcx))
  have h_bddBelow : BddBelow (Set.range F) := by
    refine ⟨min (F (-c)) (F 0 - 2), ?_⟩
    rintro y ⟨x, rfl⟩
    by_cases hxc : x ≤ -c
    · have hcx : c ≤ -x := by linarith
      have hdiff : F (-x) - F x < 2 := by
        simpa using hx₀ (-x) (le_trans (le_max_left x₀ 0) hcx)
      have hc0 : (0 : ℝ) ≤ c := le_max_right x₀ 0
      have h0le : 0 ≤ -x := by linarith
      have hFx : F 0 - 2 ≤ F x := by
        have h0 : F 0 ≤ F (-x) := F.mono h0le
        linarith
      exact (min_le_right _ _).trans hFx
    · have hcx : -c ≤ x := le_of_not_ge hxc
      exact (min_le_left _ _).trans (F.mono hcx)
  have h_top : Tendsto F atTop (𝓝 (sSup (Set.range F))) :=
    tendsto_atTop_ciSup F.mono h_bddAbove
  have h_bot : Tendsto F atBot (𝓝 (sInf (Set.range F))) :=
    tendsto_atBot_ciInf F.mono h_bddBelow
  have h_neg : Tendsto (fun x ↦ F (-x)) atTop (𝓝 (sInf (Set.range F))) :=
    h_bot.comp tendsto_neg_atTop_atBot
  have h_sub :
      Tendsto (fun x ↦ F x - F (-x)) atTop (𝓝 (sSup (Set.range F) - sInf (Set.range F))) :=
    h_top.sub h_neg
  have hs : sSup (Set.range F) - sInf (Set.range F) = 1 :=
    tendsto_nhds_unique h_sub h
  -- The total mass is the gap between the two endpoint limits.
  calc
    F.measure Set.univ = ENNReal.ofReal (sSup (Set.range F) - sInf (Set.range F)) := by
      simpa using StieltjesFunction.measure_univ F h_bot h_top
    _ = 1 := by rw [hs]; norm_num

/-- Item (v) of Example 1.58. If `F x - F (-x)` tends to `1` as `x → ∞`, then the associated
Lebesgue--Stieltjes measure is a probability measure. -/
theorem stieltjesMeasure_isProbability_of_tendsto_sub_comp_neg (F : StieltjesFunction ℝ)
    (h : Tendsto (fun x ↦ F x - F (-x)) atTop (𝓝 1)) :
    IsProbabilityMeasure F.measure := by
  -- Route correction: the symmetric increment determines the total mass directly, but not the two
  -- endpoint limits separately.
  rw [isProbabilityMeasure_iff]
  exact measure_univ_eq_one_of_tendsto_sub_comp_neg F h

end
