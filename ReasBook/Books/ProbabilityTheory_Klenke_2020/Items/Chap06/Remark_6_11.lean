/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Remark_6_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [NormedAddCommGroup E]

-- Proof sketch: fix a finite-measure set `A` and apply the canonical finite-measure
-- `L¹`-to-in-measure implication to the restricted measure `μ.restrict A`; this is the local
-- textbook notion packaged by `TendstoInMeasureOnFiniteMeasureSets`.
/-- Mean (`L¹`) convergence implies local convergence in `μ`-measure on finite-measure sets. -/
theorem tendstoInMeasureOnFiniteMeasureSets_of_tendstoInMean
    (μ : Measure Ω) {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h_mean : TendstoInMean μ fSeq f) :
    TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  have h_measSeq : ∀ n, AEStronglyMeasurable (fSeq n) μ :=
    fun n ↦ (h_mean.memLpSeq n).aestronglyMeasurable
  have h_meas : AEStronglyMeasurable f μ := h_mean.memLp.aestronglyMeasurable
  have h_tendsto_eLpNorm :
      Tendsto (fun n ↦ eLpNorm (fSeq n - f) 1 μ) atTop (𝓝 0) := by
    exact h_mean.tendsto_eLpNorm
  intro A hA_fin
  haveI : IsFiniteMeasure (μ.restrict A) :=
    isFiniteMeasure_restrict.2 (ne_of_lt hA_fin)
  have h_mean_restrict :
      Tendsto (fun n ↦ eLpNorm (fSeq n - f) 1 (μ.restrict A)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_tendsto_eLpNorm
      (fun n ↦ zero_le _) ?_
    intro n
    exact eLpNorm_restrict_le (fSeq n - f) 1 μ A
  exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun n ↦ (h_measSeq n).restrict) h_meas.restrict h_mean_restrict

-- Proof sketch: split on the disjunction and apply the canonical theorem for each branch:
-- the previous theorem for mean convergence, and
-- `tendstoInMeasureOnFiniteMeasureSets_of_tendsto_ae`
-- for almost-everywhere convergence.
/-- Consequence for Remark 6.11: mean (`L¹`) convergence and
almost-everywhere convergence are each sufficient for local convergence
in `μ`-measure on finite-measure sets. -/
theorem tendstoInMeasureOnFiniteMeasureSets_of_tendstoInMean_or_tendstoAlmostEverywhere
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h_meas : ∀ n, AEStronglyMeasurable (fSeq n) μ)
    (h : TendstoInMean μ fSeq f ∨
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))) :
    TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  exact h.elim
    (tendstoInMeasureOnFiniteMeasureSets_of_tendstoInMean μ)
    (fun h_ae ↦ tendstoInMeasureOnFiniteMeasureSets_of_tendsto_ae μ h_meas h_ae)

namespace Remark611Counterexamples

/-- Helper for Remark 6.11: the typewriter counterexample is measured on Lebesgue measure
restricted to `(0, 1]`. -/
def typewriterMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc (0 : ℝ) 1)

/-- Helper for Remark 6.11: the `n`-th typewriter term is supported on a dyadic half-open
interval. -/
private def typewriterSupport (n : ℕ) : Set ℝ :=
  let m := Nat.log2 (n + 1)
  let k := n + 1 - 2 ^ m
  Set.Ioc ((k : ℝ) / (2 : ℝ) ^ m) (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m)

/-- Helper for Remark 6.11: the typewriter sequence is the indicator of the dyadic support
interval. -/
def typewriterSequence (n : ℕ) : ℝ → ℝ :=
  (typewriterSupport n).indicator (fun _ ↦ (1 : ℝ))

/-- Helper for Remark 6.11: every typewriter support is measurable. -/
private theorem typewriterSupport_measurable (n : ℕ) :
    MeasurableSet (typewriterSupport n) := by
  unfold typewriterSupport
  exact measurableSet_Ioc

/-- Helper for Remark 6.11: each dyadic support interval stays inside `(0, 1]`. -/
private theorem typewriterSupport_subset_unitInterval (n : ℕ) :
    typewriterSupport n ⊆ Set.Ioc (0 : ℝ) 1 := by
  let m := Nat.log2 (n + 1)
  let k := n + 1 - 2 ^ m
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
  · have hleft_nonneg : (0 : ℝ) ≤ (k : ℝ) / (2 : ℝ) ^ m := by positivity
    exact lt_of_le_of_lt hleft_nonneg hx_left
  · have hk_succ_le : k + 1 ≤ 2 ^ m := Nat.succ_le_of_lt hk_lt
    have hk_real : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ m := by
      exact_mod_cast hk_succ_le
    have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
    have hright_le_one : (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) ≤ 1 := by
      exact (div_le_iff₀ hpow_pos).2 (by simpa using hk_real)
    exact hx_right.trans hright_le_one

/-- Helper for Remark 6.11: the restricted measure of a typewriter support is its dyadic
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
      ((((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) - ((k : ℝ) / (2 : ℝ) ^ m)) =
        1 / (2 : ℝ) ^ m := by
    field_simp [pow_ne_zero m (show (2 : ℝ) ≠ 0 by norm_num)]
    norm_num
  rw [typewriterMeasure, hsupport, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr hsubset, Real.volume_Ioc]
  simpa [m] using congrArg ENNReal.ofReal hlength

/-- Helper for Remark 6.11: the `L¹` norm of a typewriter term is exactly the measure of its
support interval. -/
private theorem typewriterSequence_eLpNorm (n : ℕ) :
    eLpNorm (typewriterSequence n) 1 typewriterMeasure =
      ENNReal.ofReal (1 / (2 : ℝ) ^ Nat.log2 (n + 1)) := by
  have hs : MeasurableSet (typewriterSupport n) := typewriterSupport_measurable n
  have hnorm :
      (fun x ↦ ‖typewriterSequence n x‖ₑ) =
        (typewriterSupport n).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ typewriterSupport n
    · simp [typewriterSequence, hx]
    · simp [typewriterSequence, hx]
  rw [eLpNorm_one_eq_lintegral_enorm, hnorm]
  calc
    ∫⁻ x, (typewriterSupport n).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂typewriterMeasure
      = typewriterMeasure (typewriterSupport n) := by
        simpa using (lintegral_indicator_one (μ := typewriterMeasure) hs)
    _ = ENNReal.ofReal (1 / (2 : ℝ) ^ Nat.log2 (n + 1)) := typewriterSupport_measure n

/-- Helper for Remark 6.11: the `k`-th interval on level `m` occurs at index `2 ^ m - 1 + k`. -/
private theorem typewriterSupport_eq_levelInterval {m k : ℕ} (hk : k < 2 ^ m) :
    typewriterSupport ((2 ^ m - 1) + k) =
      Set.Ioc ((k : ℝ) / (2 : ℝ) ^ m) (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) := by
  have hlog : Nat.log2 (((2 ^ m - 1) + k) + 1) = m := by
    rw [Nat.log2_eq_log_two]
    refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_
    · omega
    · have hlt : ((2 ^ m - 1) + k) + 1 < 2 ^ m + 2 ^ m := by
        omega
      simpa [pow_succ', two_mul, add_assoc, add_left_comm, add_comm] using hlt
  have hsub : (((2 ^ m - 1) + k) + 1) - 2 ^ m = k := by
    omega
  simp [typewriterSupport, hlog, hsub]

/-- Helper for Remark 6.11: every `x ∈ (0, 1]` lies in a dyadic interval on each level. -/
private theorem exists_typewriterIntervalAtLevel {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) (m : ℕ) :
    ∃ k : ℕ, k < 2 ^ m ∧
      x ∈ Set.Ioc ((k : ℝ) / (2 : ℝ) ^ m) (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) := by
  let c : ℕ := Nat.ceil (x * (2 : ℝ) ^ m)
  let k : ℕ := c - 1
  have hx_pos : 0 < x := hx.1
  have hx_le_one : x ≤ 1 := hx.2
  have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Nat.ceil_pos.mpr (by positivity)
  have hc_le : c ≤ 2 ^ m := by
    dsimp [c]
    refine Nat.ceil_le.2 ?_
    have : x * (2 : ℝ) ^ m ≤ (2 : ℝ) ^ m := by
      nlinarith [hx_le_one, hpow_pos]
    simpa using this
  have hk_lt : k < 2 ^ m := by
    dsimp [k]
    omega
  have hk_lt_ceil : k < c := by
    dsimp [k]
    omega
  have hleft_num : (k : ℝ) < x * (2 : ℝ) ^ m := by
    dsimp [c] at hk_lt_ceil
    exact Nat.lt_ceil.1 hk_lt_ceil
  have hright_num : x * (2 : ℝ) ^ m ≤ c := by
    dsimp [c]
    simpa using (Nat.le_ceil (x * (2 : ℝ) ^ m))
  have hk_succ : k + 1 = c := by
    dsimp [k]
    omega
  refine ⟨k, hk_lt, ?_⟩
  constructor
  · exact (div_lt_iff₀ hpow_pos).2 (by simpa [mul_comm] using hleft_num)
  · have hright : x ≤ (c : ℝ) / (2 : ℝ) ^ m := by
      exact (le_div_iff₀ hpow_pos).2 (by simpa [mul_comm] using hright_num)
    simpa [hk_succ] using hright

/-- Helper for Remark 6.11: every point of `(0, 1]` belongs to infinitely many typewriter
supports. -/
private theorem typewriterSupport_frequentlyMem {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ᶠ n in atTop, x ∈ typewriterSupport n := by
  rw [Nat.frequently_atTop_iff_infinite]
  rw [Set.infinite_iff_exists_gt]
  intro N
  let m := Nat.log2 (N + 1) + 1
  obtain ⟨k, hk_lt, hk_mem⟩ := exists_typewriterIntervalAtLevel hx m
  refine ⟨(2 ^ m - 1) + k, ?_, ?_⟩
  · simpa [typewriterSupport_eq_levelInterval hk_lt] using hk_mem
  · have hlt : N + 1 < 2 ^ m := by
      dsimp [m]
      simpa [Nat.log2_eq_log_two] using
        Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (N + 1)
    omega

/-- Helper for Remark 6.11: on `(0, 1]`, the typewriter sequence is not eventually zero, hence it
cannot converge to `0`. -/
private theorem typewriterSequence_notTendstoZeroAt {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ¬ Tendsto (fun n ↦ typewriterSequence n x) atTop (𝓝 (0 : ℝ)) := by
  intro h
  have h_small : ∀ᶠ n in atTop, typewriterSequence n x ∈ Metric.ball (0 : ℝ) (1 / 2) := by
    exact h (Metric.ball_mem_nhds (0 : ℝ) (by norm_num))
  have h_not_mem : ∀ᶠ n in atTop, x ∉ typewriterSupport n := by
    filter_upwards [h_small] with n hn
    intro hx_mem
    have h_eq : typewriterSequence n x = 1 := by
      simp [typewriterSequence, hx_mem]
    have h_ball : (1 : ℝ) ∈ Metric.ball (0 : ℝ) (1 / 2) := by
      simpa [h_eq] using hn
    have : ¬ (1 : ℝ) ∈ Metric.ball (0 : ℝ) (1 / 2) := by
      norm_num [Metric.mem_ball]
    exact this h_ball
  exact (typewriterSupport_frequentlyMem hx) h_not_mem

/-- Helper for Remark 6.11: each typewriter term is integrable on `(0, 1]`. -/
private theorem typewriterSequence_integrable (n : ℕ) :
    Integrable (typewriterSequence n) typewriterMeasure := by
  have hs : MeasurableSet (typewriterSupport n) := typewriterSupport_measurable n
  rw [typewriterSequence, integrable_indicator_iff hs]
  refine integrableOn_const ?_
  rw [typewriterSupport_measure]
  simp

/-- Helper for Remark 6.11: the typewriter sequence converges to `0` in mean on `(0, 1]`. -/
private theorem typewriterSequence_tendstoInMean :
    TendstoInMean typewriterMeasure typewriterSequence 0 := by
  refine (tendstoInMean_iff).2 ?_
  refine ⟨typewriterSequence_integrable, ?_, ?_⟩
  · exact integrable_zero (α := ℝ) (ε' := ℝ) typewriterMeasure
  · have hbound :
        ∀ n, (1 : ℝ) / (2 : ℝ) ^ Nat.log2 (n + 1) ≤ 2 / (n + 1 : ℝ) := by
      intro n
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
        _ = 2 / (n + 1 : ℝ) := by
          field_simp
    have h_rhs : Tendsto (fun n : ℕ ↦ (2 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) := by
      convert
        (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp (tendsto_add_atTop_nat 1) using 1
      ext n
      norm_num [Nat.cast_add]
    have h_real :
        Tendsto (fun n : ℕ ↦ (1 : ℝ) / (2 : ℝ) ^ Nat.log2 (n + 1)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_rhs
        (fun n ↦ by positivity) ?_
      intro n
      exact hbound n
    have h_enn :
        Tendsto
          (fun n : ℕ ↦ ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ Nat.log2 (n + 1)))
          atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h_real
    simpa [typewriterSequence_eLpNorm] using h_enn

/-- Helper for Remark 6.11: the typewriter sequence does not converge almost everywhere to
`0`. -/
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
    rw [typewriterMeasure, Measure.restrict_apply measurableSet_Ioc, Set.inter_self,
      Real.volume_Ioc]
    norm_num
  have : (1 : ℝ≥0∞) = 0 := by
    rw [h_unit_measure] at h_unit_null
    exact h_unit_null
  exact one_ne_zero this

/-- Helper for Remark 6.11: the typewriter sequence is the standard counterexample with `L¹`
convergence but no almost-everywhere convergence. -/
theorem typewriter_sequence_converges_inL1_not_ae :
    TendstoInMean typewriterMeasure typewriterSequence 0 ∧
      ¬ ∀ᵐ ω ∂typewriterMeasure, Tendsto (fun n ↦ typewriterSequence n ω) atTop (𝓝 (0 : ℝ)) := by
  exact ⟨typewriterSequence_tendstoInMean, typewriterSequence_not_tendstoAlmostEverywhere⟩

/-- Helper for Remark 6.11: the escaping interval indicators are the indicators of the translated
unit intervals `[n, n + 1]`. -/
def escapingIndicatorSequence (n : ℕ) : ℝ → ℝ :=
  (Set.Icc (n : ℝ) (n + 1)).indicator (fun _ ↦ (1 : ℝ))

/-- Helper for Remark 6.11: the `L¹` norm of each translated unit-interval indicator is `1`. -/
private theorem escapingIndicatorSequence_eLpNorm (n : ℕ) :
    eLpNorm (escapingIndicatorSequence n) 1 (volume : Measure ℝ) = 1 := by
  have hnorm :
      (fun x ↦ ‖escapingIndicatorSequence n x‖ₑ) =
        (Set.Icc (n : ℝ) (n + 1)).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (n : ℝ) (n + 1)
    · simp [escapingIndicatorSequence, hx]
    · simp [escapingIndicatorSequence, hx]
  rw [eLpNorm_one_eq_lintegral_enorm, hnorm]
  calc
    ∫⁻ x, (Set.Icc (n : ℝ) (n + 1)).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂volume
      = volume (Set.Icc (n : ℝ) (n + 1)) := by
        exact lintegral_indicator_one (μ := volume) measurableSet_Icc
    _ = ENNReal.ofReal (↑n + 1 - ↑n) := by rw [Real.volume_Icc]
    _ = 1 := by norm_num

/-- Helper for Remark 6.11: each fixed point eventually lies to the left of the escaping unit
intervals. -/
private theorem escapingIndicatorSequence_tendstoZeroAt (x : ℝ) :
    Tendsto (fun n ↦ escapingIndicatorSequence n x) atTop (𝓝 (0 : ℝ)) := by
  have h_eventually : ∀ᶠ n : ℕ in atTop, x < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop x
  have h_zero : ∀ᶠ n in atTop, escapingIndicatorSequence n x = 0 := by
    filter_upwards [h_eventually] with n hn
    have hx_not_mem : x ∉ Set.Icc (n : ℝ) (n + 1) := by
      intro hx_mem
      exact (not_lt_of_ge hx_mem.1) hn
    simp [escapingIndicatorSequence, hx_not_mem]
  have h_eq :
      (fun n ↦ escapingIndicatorSequence n x) =ᶠ[atTop] fun _ : ℕ ↦ (0 : ℝ) := by
    filter_upwards [h_zero] with n hn
    exact hn
  exact tendsto_const_nhds.congr' h_eq.symm

/-- Helper for Remark 6.11: the translated interval indicators converge almost everywhere to
`0`. -/
private theorem escapingIndicatorSequence_tendstoAlmostEverywhere :
    ∀ᵐ ω ∂volume, Tendsto (fun n ↦ escapingIndicatorSequence n ω) atTop (𝓝 (0 : ℝ)) := by
  exact ae_of_all _ escapingIndicatorSequence_tendstoZeroAt

/-- Helper for Remark 6.11: the translated interval indicators do not converge to `0` in
mean. -/
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
        (fun n ↦ eLpNorm (escapingIndicatorSequence n - 0) 1 (volume : Measure ℝ)) =ᶠ[atTop]
          fun _ : ℕ ↦ (1 : ℝ≥0∞) :=
      Filter.Eventually.of_forall h_norm_eq_one
    exact tendsto_const_nhds.congr' h_eq.symm
  have h_zero :
      Tendsto
        (fun n ↦ eLpNorm (escapingIndicatorSequence n - 0) 1 (volume : Measure ℝ))
        atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa using h_mean.tendsto_eLpNorm
  exact one_ne_zero (tendsto_nhds_unique h_const h_zero)

/-- Helper for Remark 6.11: the escaping interval indicators are the standard counterexample with
almost-everywhere convergence but no `L¹` convergence. -/
theorem escaping_indicator_sequence_tendsto_ae_not_inL1 :
    (∀ᵐ ω ∂volume, Tendsto (fun n ↦ escapingIndicatorSequence n ω) atTop (𝓝 (0 : ℝ))) ∧
      ¬ TendstoInMean volume escapingIndicatorSequence 0 := by
  exact ⟨escapingIndicatorSequence_tendstoAlmostEverywhere,
    escapingIndicatorSequence_not_tendstoInMean⟩

end Remark611Counterexamples

open Remark611Counterexamples

/-- Remark 6.11 (counterexample): the typewriter sequence converges in mean, hence also in local
`μ`-measure, but it does not converge almost everywhere. Thus neither mean convergence nor local
convergence in measure implies almost-everywhere convergence in general. -/
theorem typewriterSequence_tendstoInMeasureOnFiniteMeasureSets_not_tendstoAlmostEverywhere :
    TendstoInMeasureOnFiniteMeasureSets typewriterMeasure typewriterSequence 0 ∧
      ¬ ∀ᵐ ω ∂typewriterMeasure, Tendsto (fun n ↦ typewriterSequence n ω) atTop (𝓝 (0 : ℝ)) := by
  -- Reuse the imported Exercise 6.1.2 counterexample and transport its `L¹` half.
  rcases typewriter_sequence_converges_inL1_not_ae with ⟨h_mean, h_not_ae⟩
  refine ⟨?_, h_not_ae⟩
  -- Mean convergence implies local convergence in measure on finite-measure sets.
  exact tendstoInMeasureOnFiniteMeasureSets_of_tendstoInMean typewriterMeasure h_mean

/- Exercise 6.1.2 (1): the typewriter sequence is the chapter's source-facing counterexample
showing that mean convergence does not imply almost-everywhere convergence. -/
recall typewriter_sequence_converges_inL1_not_ae

/-- Helper for Remark 6.11: each translated unit-interval indicator is
`AEStronglyMeasurable` for Lebesgue measure. -/
private theorem escapingIndicatorSequence_aestronglyMeasurable (n : ℕ) :
    AEStronglyMeasurable (escapingIndicatorSequence n) (volume : Measure ℝ) := by
  -- The sequence terms are measurable indicators of measurable intervals.
  have h_meas : Measurable (escapingIndicatorSequence n) := by
    simpa [escapingIndicatorSequence] using
      (Measurable.indicator measurable_const measurableSet_Icc :
        Measurable ((Set.Icc (n : ℝ) (n + 1)).indicator (fun _ ↦ (1 : ℝ))))
  -- Measurability upgrades to almost-everywhere strong measurability.
  exact h_meas.aestronglyMeasurable

/-- Counterexample for Remark 6.11: the escaping interval indicators converge almost everywhere,
hence also in local Lebesgue measure, but they do not converge in mean. Thus neither
almost-everywhere convergence nor local convergence in measure implies mean convergence in
general. -/
theorem escapingIndicatorSequence_tendstoInMeasureOnFiniteMeasureSets_not_tendstoInMean :
    TendstoInMeasureOnFiniteMeasureSets volume escapingIndicatorSequence 0 ∧
      ¬ TendstoInMean volume escapingIndicatorSequence 0 := by
  -- Reuse the imported Exercise 6.1.2 counterexample and transport its a.e. half.
  rcases escaping_indicator_sequence_tendsto_ae_not_inL1 with ⟨h_ae, h_not_mean⟩
  refine ⟨?_, h_not_mean⟩
  -- Almost-everywhere convergence plus measurability implies local convergence in measure.
  exact tendstoInMeasureOnFiniteMeasureSets_of_tendsto_ae volume
    escapingIndicatorSequence_aestronglyMeasurable h_ae

/- Exercise 6.1.2 (2): the escaping interval indicators are the chapter's source-facing
counterexample showing that almost-everywhere convergence does not imply mean convergence. -/
recall escaping_indicator_sequence_tendsto_ae_not_inL1

end
