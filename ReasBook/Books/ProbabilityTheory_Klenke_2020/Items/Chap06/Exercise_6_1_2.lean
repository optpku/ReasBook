/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

/-- The Lebesgue measure restricted to `(0, 1]`, used for the typewriter example. -/
def typewriterMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc (0 : ℝ) 1)

/-- The dyadic interval supporting the `n`-th term of the typewriter sequence. -/
private def typewriterSupport (n : ℕ) : Set ℝ :=
  let m := Nat.log2 (n + 1)
  let k := n + 1 - 2 ^ m
  Set.Ioc ((k : ℝ) / (2 : ℝ) ^ m) (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m)

/-- The typewriter sequence on `(0, 1]`, viewed as indicator functions of dyadic intervals. -/
def typewriterSequence (n : ℕ) : ℝ → ℝ :=
  (typewriterSupport n).indicator (fun _ ↦ (1 : ℝ))

/-- Helper for Exercise 6.1.2: every typewriter support is a measurable half-open interval. -/
private theorem typewriterSupport_measurable (n : ℕ) :
    MeasurableSet (typewriterSupport n) := by
  -- Unfold once: the support is literally a real `Ioc` interval.
  unfold typewriterSupport
  exact measurableSet_Ioc

/-- Helper for Exercise 6.1.2: each dyadic support interval stays inside `(0, 1]`. -/
private theorem typewriterSupport_subset_unitInterval (n : ℕ) :
    typewriterSupport n ⊆ Set.Ioc (0 : ℝ) 1 := by
  let m := Nat.log2 (n + 1)
  let k := n + 1 - 2 ^ m
  have hpow_le : 2 ^ m ≤ n + 1 := by
    dsimp [m]
    simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)
  have hk_lt : k < 2 ^ m := by
    dsimp [k]
    have hlt : n + 1 < 2 ^ (m + 1) := by
      dsimp [m]
      simpa [Nat.log2_eq_log_two] using
        Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (n + 1)
    omega
  intro x hx
  have hx' :
      x ∈ Set.Ioc ((k : ℝ) / (2 : ℝ) ^ m) (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) := by
    simpa [typewriterSupport, m, k] using hx
  rcases hx' with ⟨hx_left, hx_right⟩
  refine ⟨?_, ?_⟩
  · -- The left endpoint is nonnegative, so membership forces `x > 0`.
    have hleft_nonneg : (0 : ℝ) ≤ (k : ℝ) / (2 : ℝ) ^ m := by positivity
    exact lt_of_le_of_lt hleft_nonneg hx_left
  · -- The right endpoint is at most `1`, so membership forces `x ≤ 1`.
    have hk_succ_le : k + 1 ≤ 2 ^ m := Nat.succ_le_of_lt hk_lt
    have hright_le_one : (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) ≤ 1 := by
      have hk_real : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ m := by
        exact_mod_cast hk_succ_le
      have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
      exact (div_le_iff₀ hpow_pos).2 (by simpa using hk_real)
    exact hx_right.trans hright_le_one

/-- Helper for Exercise 6.1.2: the restricted measure of a typewriter support is its dyadic
length. -/
private theorem typewriterSupport_measure (n : ℕ) :
    typewriterMeasure (typewriterSupport n) =
      ENNReal.ofReal (1 / (2 : ℝ) ^ Nat.log2 (n + 1)) := by
  let m := Nat.log2 (n + 1)
  let k := n + 1 - 2 ^ m
  have hsupport :
      typewriterSupport n =
        Set.Ioc ((k : ℝ) / (2 : ℝ) ^ m) (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) := by
    simp [typewriterSupport, m, k]
  have hsubset :
      Set.Ioc ((k : ℝ) / (2 : ℝ) ^ m) (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) ⊆
        Set.Ioc (0 : ℝ) 1 := by
    simpa [hsupport] using typewriterSupport_subset_unitInterval n
  have hlength :
      ((((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) - ((k : ℝ) / (2 : ℝ) ^ m))
        = 1 / (2 : ℝ) ^ m := by
    field_simp [pow_ne_zero m (show (2 : ℝ) ≠ 0 by norm_num)]
    norm_num
  -- Reduce the restricted measure to the plain interval length.
  rw [hsupport, typewriterMeasure, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr hsubset, Real.volume_Ioc]
  simpa [m, k] using congrArg ENNReal.ofReal hlength

/-- Helper for Exercise 6.1.2: the `L¹` norm of a typewriter term is exactly the length of its
support interval. -/
private theorem typewriterSequence_eLpNorm (n : ℕ) :
    eLpNorm (typewriterSequence n) 1 typewriterMeasure =
      ENNReal.ofReal (1 / (2 : ℝ) ^ Nat.log2 (n + 1)) := by
  have hs : MeasurableSet (typewriterSupport n) := typewriterSupport_measurable n
  -- The indicator takes only the value `1`, so the seminorm is the support measure.
  rw [typewriterSequence, eLpNorm_indicator_const hs one_ne_zero ENNReal.one_ne_top,
    typewriterSupport_measure]
  simp

/-- Helper for Exercise 6.1.2: the `k`-th interval on level `m` occurs at index `2^m - 1 + k`. -/
private theorem typewriterSupport_eq_levelInterval {m k : ℕ} (hk : k < 2 ^ m) :
    typewriterSupport ((2 ^ m - 1) + k) =
      Set.Ioc ((k : ℝ) / (2 : ℝ) ^ m) (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) := by
  have hpow_pos : 0 < 2 ^ m := by positivity
  have hlog : Nat.log2 (((2 ^ m - 1) + k) + 1) = m := by
    rw [Nat.log2_eq_log_two]
    refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_
    · omega
    · have hlt : ((2 ^ m - 1) + k) + 1 < 2 ^ m + 2 ^ m := by
        omega
      simpa [pow_succ', two_mul, add_comm, add_left_comm, add_assoc] using hlt
  have hsub : (((2 ^ m - 1) + k) + 1) - 2 ^ m = k := by
    omega
  -- Route correction: normalize the index so `log2` reads off the chosen dyadic level.
  simp [typewriterSupport, hlog, hsub]

/-- Helper for Exercise 6.1.2: every `x ∈ (0,1]` lies in exactly one dyadic interval on each
level. -/
private theorem exists_typewriterIntervalAtLevel {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) (m : ℕ) :
    ∃ k : ℕ,
      k < 2 ^ m ∧
        x ∈ Set.Ioc ((k : ℝ) / (2 : ℝ) ^ m) (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) := by
  let c : ℕ := Nat.ceil (x * (2 : ℝ) ^ m)
  let k : ℕ := c - 1
  have hx_pos : 0 < x := hx.1
  have hx_le_one : x ≤ 1 := hx.2
  have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
  have hc_pos : 0 < c := by
    dsimp [c]
    apply Nat.ceil_pos.mpr
    positivity
  have hc_le : c ≤ 2 ^ m := by
    dsimp [c]
    refine Nat.ceil_le.2 ?_
    calc
      x * (2 : ℝ) ^ m ≤ 1 * (2 : ℝ) ^ m := by gcongr
      _ = ((2 ^ m : ℕ) : ℝ) := by simp
  have hk_lt : k < 2 ^ m := by
    dsimp [k]
    omega
  have hk_lt_ceil_nat : k < c := by
    dsimp [k]
    omega
  have hleft_num : (k : ℝ) < x * (2 : ℝ) ^ m := by
    exact Nat.lt_ceil.1 hk_lt_ceil_nat
  have hright_num : x * (2 : ℝ) ^ m ≤ c := by
    dsimp [c]
    simpa using (Nat.le_ceil (x * (2 : ℝ) ^ m))
  have hk_succ : k + 1 = c := by
    dsimp [k]
    omega
  refine ⟨k, hk_lt, ?_⟩
  constructor
  · -- Dividing the lower estimate by a positive power of `2` places `x` above the left endpoint.
    exact (div_lt_iff₀ hpow_pos).2 (by simpa [mul_comm] using hleft_num)
  · -- Dividing the upper estimate by the same positive factor places `x` below the right endpoint.
    have hright : x ≤ (c : ℝ) / (2 : ℝ) ^ m := by
      exact (le_div_iff₀ hpow_pos).2 (by simpa [mul_comm] using hright_num)
    simpa [hk_succ] using hright

/-- Helper for Exercise 6.1.2: every point of `(0,1]` belongs to infinitely many typewriter
supports. -/
private theorem typewriterSupport_frequentlyMem {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ᶠ n in atTop, x ∈ typewriterSupport n := by
  rw [Nat.frequently_atTop_iff_infinite]
  rw [Set.infinite_iff_exists_gt]
  intro N
  let m := Nat.log2 (N + 1) + 1
  obtain ⟨k, hk_lt, hk_mem⟩ := exists_typewriterIntervalAtLevel hx m
  refine ⟨((2 ^ m - 1) + k : ℕ), ?_, ?_⟩
  · simpa [typewriterSupport_eq_levelInterval hk_lt] using hk_mem
  · have hpow_pos : 0 < 2 ^ m := by positivity
    have hlt : N + 1 < 2 ^ m := by
      dsimp [m]
      simpa [Nat.log2_eq_log_two] using
        Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (N + 1)
    omega

/-- Helper for Exercise 6.1.2: on `(0,1]`, the typewriter sequence is not eventually zero, so it
cannot converge to `0`. -/
private theorem typewriterSequence_notTendstoZeroAt {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ¬ Tendsto (fun n ↦ typewriterSequence n x) atTop (𝓝 (0 : ℝ)) := by
  intro h
  have h' :
      Tendsto
        (fun n ↦ (typewriterSupport n).indicator (fun _ ↦ (1 : ℝ)) x)
        atTop
        (𝓝 ((∅ : Set ℝ).indicator (fun _ ↦ (1 : ℝ)) x)) := by
    simpa [typewriterSequence] using h
  have h_eventually :
      ∀ᶠ n in atTop, x ∈ typewriterSupport n ↔ x ∈ (∅ : Set ℝ) := by
    exact
      (tendsto_indicator_const_apply_iff_eventually (L := atTop)
        (A := (∅ : Set ℝ)) (As := typewriterSupport) (b := (1 : ℝ)) x).1 h'
  have h_not_mem : ∀ᶠ n in atTop, x ∉ typewriterSupport n := by
    simpa using h_eventually
  exact typewriterSupport_frequentlyMem hx h_not_mem

-- Proof sketch: the support of `typewriterSequence n` is a bounded measurable interval inside
-- `(0, 1]`, so its indicator is measurable and has finite integral against `typewriterMeasure`.
/-- Each term of the typewriter sequence is integrable on `(0, 1]`. -/
private theorem typewriterSequence_integrable (n : ℕ) :
    Integrable (typewriterSequence n) typewriterMeasure := by
  have hs : MeasurableSet (typewriterSupport n) := typewriterSupport_measurable n
  -- Integrability reduces to finite measure of the support interval.
  rw [typewriterSequence, integrable_indicator_iff hs]
  refine integrableOn_const ?_
  rw [typewriterSupport_measure]
  simp

-- Proof sketch: compute the `L¹` norm of `typewriterSequence n` as the length of its dyadic
-- support, which tends to `0`, while every point of `(0, 1]` lies in exactly one dyadic interval
-- at each generation, so the pointwise values oscillate between `0` and `1` and fail to converge.
/-- The typewriter sequence converges to `0` in mean (`L¹`) on `(0, 1]`. -/
private theorem typewriterSequence_tendstoInMean :
    TendstoInMean typewriterMeasure typewriterSequence 0 := by
  refine (tendstoInMean_iff).2 ?_
  refine ⟨typewriterSequence_integrable, ?_, ?_⟩
  · exact ⟨aestronglyMeasurable_zero, hasFiniteIntegral_zero _ _⟩
  have hbound :
      ∀ n, (1 : ℝ) / (2 : ℝ) ^ Nat.log2 (n + 1) ≤ 2 / (((n + 1 : ℕ) : ℝ)) := by
    intro n
    have hpow : (0 : ℝ) < (2 : ℝ) ^ Nat.log2 (n + 1) := by positivity
    have hle :
        ((n + 1 : ℝ) / 2) ≤ (2 : ℝ) ^ Nat.log2 (n + 1) := by
      have hlt_nat : n + 1 < 2 ^ (Nat.log2 (n + 1) + 1) := by
        simpa [Nat.log2_eq_log_two] using
          Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (n + 1)
      have hlt_real : (n + 1 : ℝ) < (2 : ℝ) ^ (Nat.log2 (n + 1) + 1) := by
        exact_mod_cast hlt_nat
      rw [pow_succ', mul_comm] at hlt_real
      have : ((n + 1 : ℝ) / 2) < (2 : ℝ) ^ Nat.log2 (n + 1) := by
        exact (div_lt_iff₀ (show (0 : ℝ) < 2 by norm_num)).2
          (by simpa [mul_comm] using hlt_real)
      exact this.le
    calc
      1 / (2 : ℝ) ^ Nat.log2 (n + 1) ≤ 1 / ((n + 1 : ℝ) / 2) := by
        exact one_div_le_one_div_of_le (by positivity) hle
      _ = 2 / (((n + 1 : ℕ) : ℝ)) := by
        field_simp [Nat.cast_add, Nat.cast_one]
        norm_num [Nat.cast_add, Nat.cast_one]
  have h_rhs :
      Tendsto (fun n : ℕ ↦ (2 : ℝ) / (((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    convert ((tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp (tendsto_add_atTop_nat 1)) using 1
  have h_real :
      Tendsto (fun n ↦ (1 : ℝ) / (2 : ℝ) ^ Nat.log2 (n + 1)) atTop (𝓝 0) := by
    have h_nonneg : ∀ n, (0 : ℝ) ≤ (1 : ℝ) / (2 : ℝ) ^ Nat.log2 (n + 1) := by
      intro n
      positivity
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_rhs h_nonneg ?_
    intro n
    exact hbound n
  -- Transport the real estimate through `ENNReal.ofReal`.
  simpa [typewriterSequence_eLpNorm] using ENNReal.tendsto_ofReal h_real

/-- The typewriter sequence does not converge to `0` almost everywhere on `(0, 1]`. -/
private theorem typewriterSequence_not_tendstoAlmostEverywhere :
    ¬ ∀ᵐ ω ∂typewriterMeasure, Tendsto (fun n ↦ typewriterSequence n ω) atTop (𝓝 (0 : ℝ)) := by
  intro h_ae
  have h_bad_null :
      typewriterMeasure
        {ω : ℝ | ¬ Tendsto (fun n ↦ typewriterSequence n ω) atTop (𝓝 (0 : ℝ))} = 0 := by
    simpa [ae_iff] using h_ae
  have hsubset :
      Set.Ioc (0 : ℝ) 1 ⊆
        {ω : ℝ | ¬ Tendsto (fun n ↦ typewriterSequence n ω) atTop (𝓝 (0 : ℝ))} := by
    intro x hx
    exact typewriterSequence_notTendstoZeroAt hx
  have h_unit_null : typewriterMeasure (Set.Ioc (0 : ℝ) 1) = 0 :=
    measure_mono_null hsubset h_bad_null
  have h_unit_measure : typewriterMeasure (Set.Ioc (0 : ℝ) 1) = 1 := by
    -- The restricted measure of the whole unit interval is just its Lebesgue length.
    rw [typewriterMeasure, Measure.restrict_apply measurableSet_Ioc, Set.inter_self,
      Real.volume_Ioc]
    norm_num
  rw [h_unit_measure] at h_unit_null
  exact one_ne_zero h_unit_null

/-- Exercise 6.1.2 (1): the typewriter sequence converges to `0` in mean (`L¹`) but does not
converge to `0` almost everywhere. -/
theorem typewriter_sequence_converges_inL1_not_ae :
    TendstoInMean typewriterMeasure typewriterSequence 0 ∧
      ¬ ∀ᵐ ω ∂typewriterMeasure, Tendsto (fun n ↦ typewriterSequence n ω) atTop (𝓝 (0 : ℝ)) :=
  ⟨typewriterSequence_tendstoInMean, typewriterSequence_not_tendstoAlmostEverywhere⟩

/-- The indicator functions of the unit intervals translated to the right along the real line. -/
def escapingIndicatorSequence (n : ℕ) : ℝ → ℝ :=
  (Set.Icc (n : ℝ) (n + 1)).indicator (fun _ ↦ (1 : ℝ))

/-- Helper for Exercise 6.1.2: the `L¹` norm of each translated unit-interval indicator is `1`. -/
private theorem escapingIndicatorSequence_eLpNorm (n : ℕ) :
    eLpNorm (escapingIndicatorSequence n) 1 (volume : Measure ℝ) = 1 := by
  -- The translated interval always has Lebesgue measure `1`.
  rw [escapingIndicatorSequence,
    eLpNorm_indicator_const measurableSet_Icc one_ne_zero ENNReal.one_ne_top, Real.volume_Icc]
  norm_num

/-- Helper for Exercise 6.1.2: fixed points eventually lie to the left of all translated unit
intervals. -/
private theorem escapingIndicatorSequence_tendstoZeroAt (x : ℝ) :
    Tendsto (fun n ↦ escapingIndicatorSequence n x) atTop (𝓝 (0 : ℝ)) := by
  have h_eventually : ∀ᶠ n : ℕ in atTop, x < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop x
  have h_zero : ∀ᶠ n in atTop, escapingIndicatorSequence n x = 0 := by
    filter_upwards [h_eventually] with n hn
    have hx_not_mem : x ∉ Set.Icc (n : ℝ) (n + 1) := by
      exact fun hx_mem ↦ (not_le_of_gt hn) hx_mem.1
    simp [escapingIndicatorSequence, hx_not_mem]
  -- Eventually the sequence is constantly zero at the chosen point.
  exact tendsto_nhds_of_eventually_eq h_zero

-- Proof sketch: each translated unit interval is measurable and has finite Lebesgue measure, so
-- its indicator function is Lebesgue integrable.
/-- Each translated interval indicator is integrable with respect to Lebesgue measure. -/
private theorem escapingIndicatorSequence_integrable (n : ℕ) :
    Integrable (escapingIndicatorSequence n) (volume : Measure ℝ) := by
  -- Integrability again reduces to finite measure of the support interval.
  rw [escapingIndicatorSequence, integrable_indicator_iff measurableSet_Icc]
  refine integrableOn_const ?_
  rw [Real.volume_Icc]
  simp

-- Proof sketch: for each fixed `x : ℝ`, the intervals `[n, n + 1]` eventually lie to the right of
-- `x`, so the sequence is eventually `0` at `x`; however every term has `L¹` norm equal to `1`,
-- so the sequence cannot converge to `0` in `L¹`.
/-- The translated unit-interval indicators converge to `0` almost everywhere. -/
private theorem escapingIndicatorSequence_tendstoAlmostEverywhere :
    ∀ᵐ ω ∂volume, Tendsto (fun n ↦ escapingIndicatorSequence n ω) atTop (𝓝 (0 : ℝ)) := by
  -- The pointwise limit is already eventually constant, so the a.e. statement is immediate.
  exact ae_of_all _ escapingIndicatorSequence_tendstoZeroAt

/-- The translated unit-interval indicators do not converge to `0` in mean (`L¹`). -/
private theorem escapingIndicatorSequence_not_tendstoInMean :
    ¬ TendstoInMean volume escapingIndicatorSequence 0 := by
  intro h_mean
  have h_norm_eq_one :
      ∀ n, eLpNorm (escapingIndicatorSequence n - 0) 1 (volume : Measure ℝ) = 1 := by
    intro n
    simpa using escapingIndicatorSequence_eLpNorm n
  have h_const :
      Tendsto
        (fun n ↦ eLpNorm (escapingIndicatorSequence n - 0) 1 (volume : Measure ℝ))
        atTop (𝓝 (1 : ℝ≥0∞)) := by
    have h_eq :
        (fun n ↦ eLpNorm (escapingIndicatorSequence n - 0) 1 (volume : Measure ℝ)) =
          fun _ : ℕ ↦ (1 : ℝ≥0∞) := by
      funext n
      exact h_norm_eq_one n
    rw [h_eq]
    exact tendsto_const_nhds
  have h_zero :
      Tendsto
        (fun n ↦ eLpNorm (escapingIndicatorSequence n - 0) 1 (volume : Measure ℝ))
        atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa using h_mean.tendsto_eLpNorm
  exact one_ne_zero (tendsto_nhds_unique h_const h_zero)

/-- Exercise 6.1.2 (2): the translated unit-interval indicators converge to `0` almost
everywhere but do not converge to `0` in mean (`L¹`). -/
theorem escaping_indicator_sequence_tendsto_ae_not_inL1 :
    (∀ᵐ ω ∂volume, Tendsto (fun n ↦ escapingIndicatorSequence n ω) atTop (𝓝 (0 : ℝ))) ∧
      ¬ TendstoInMean volume escapingIndicatorSequence 0 :=
  ⟨escapingIndicatorSequence_tendstoAlmostEverywhere,
    escapingIndicatorSequence_not_tendstoInMean⟩

end
