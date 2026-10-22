/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_2
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Decomposition.Exhaustion
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open scoped ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

-- `lean_leansearch` recalled `MeasureTheory.ae_of_forall_measure_lt_top_ae_restrict` as the
-- canonical sigma-finite globalization helper. Chapter 6, Section 6.1 works under the standing
-- assumption that `(Ω, 𝒜, μ)` is sigma-finite, so the public clauses `(ii)` and `(iii)` keep that
-- hypothesis explicit while still using the textbook finite-measure-test-set formulation.
-- In this import set, `lpNorm` is real-valued, so the textbook finiteness hypothesis in clause
-- `(i)` is expressed by `Summable`.

/-- Helper: a summable nonnegative real series remains summable after applying `x ↦ x ^ q` for
any exponent `q ≥ 1`. -/
private lemma summableRpowOfSummable
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hSum : Summable a) {q : ℝ} (hq : 1 ≤ q) :
    Summable (fun n ↦ a n ^ q) := by
  have hZero : Tendsto a atTop (𝓝 0) := hSum.tendsto_atTop_zero
  have hEventuallyLtOne : ∀ᶠ n in atTop, a n < 1 := by
    exact hZero (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  rcases eventually_atTop.1 hEventuallyLtOne with ⟨N, hN⟩
  have hTail : Summable (fun n ↦ a (n + N)) :=
    (_root_.summable_nat_add_iff N).2 hSum
  have hTailLe : ∀ n, a (n + N) ^ q ≤ a (n + N) := by
    intro n
    exact Real.rpow_le_self_of_le_one (ha _) (le_of_lt (hN _ (Nat.le_add_left N n))) hq
  have hTailRpow : Summable (fun n ↦ a (n + N) ^ q) :=
    Summable.of_nonneg_of_le
      (fun n ↦ Real.rpow_nonneg (ha _) _)
      hTailLe
      hTail
  exact (_root_.summable_nat_add_iff N).1 hTailRpow

/-- Helper: on a finite slice, summable deviation-event measures force pointwise convergence almost
everywhere. -/
private lemma aeTendsto_of_summableRestrictDistEvents
    {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E]
    {μ : Measure Ω} {A : Set Ω} {fSeq : ℕ → Ω → E} {f : Ω → E}
    (hA : MeasurableSet A) (_hA_fin : μ A < ∞)
    (hMeasSeq : ∀ n, Measurable (fSeq n))
    (hMeas : Measurable f)
    (hSeries : ∀ ε : ℝ, 0 < ε →
      (∑' n, μ (A ∩ {ω | ε < dist (f ω) (fSeq n ω)})) < ∞) :
    ∀ᵐ ω ∂μ.restrict A, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := by
  have hThresholds :
      ∀ᵐ ω ∂μ.restrict A, ∀ k : ℕ, ∀ᶠ n in atTop,
        dist (fSeq n ω) (f ω) ≤ (1 : ℝ) / (k + 1) := by
    rw [ae_all_iff]
    intro k
    let ε : ℝ := (1 : ℝ) / (k + 1)
    have hε : 0 < ε := by positivity
    let bad : ℕ → Set Ω := fun n ↦ {ω | ε < dist (f ω) (fSeq n ω)}
    have hBad_meas : ∀ n, MeasurableSet (bad n) := by
      intro n
      simpa [bad] using measurableSet_lt measurable_const (hMeas.dist (hMeasSeq n))
    have hBad_ae :
        ∀ᵐ ω ∂μ.restrict A, ∀ᶠ n in atTop, ω ∉ bad n := by
      have hBad_ne_top : (∑' n, (μ.restrict A) (bad n)) ≠ ∞ := by
        simpa [bad, ε, Measure.restrict_apply, hA, hBad_meas, Set.inter_assoc, Set.inter_comm,
          Set.inter_left_comm] using (ne_of_lt (hSeries ε hε))
      simpa [bad] using (ae_eventually_notMem hBad_ne_top : ∀ᵐ ω ∂μ.restrict A, _)
    -- Proof comment: Borel-Cantelli eliminates each geometric error threshold separately.
    filter_upwards [hBad_ae] with ω hω
    exact hω.mono fun n hn ↦ by
      have hNot : ¬ ε < dist (f ω) (fSeq n ω) := by
        simpa [bad] using hn
      simpa [ε, dist_comm] using (le_of_not_gt hNot)
  -- Proof comment: the geometric thresholds `1 / (k + 1)` form a countable neighborhood basis
  -- at `0`, so the threshold-wise eventual bounds give metric convergence.
  filter_upwards [hThresholds] with ω hω
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  rcases eventually_atTop.1 (hω k) with ⟨N, hN⟩
  exact ⟨N, fun n hn ↦ lt_of_le_of_lt (hN n hn) hk⟩

/-- Helper: summable deviation-event measures on every finite slice globalize to almost-everywhere
pointwise convergence. -/
private lemma aeTendsto_of_summableDistEvents
    {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E]
    {μ : Measure Ω} [SigmaFinite μ] {fSeq : ℕ → Ω → E} {f : Ω → E}
    (hMeasSeq : ∀ n, Measurable (fSeq n))
    (hMeas : Measurable f)
    (hSeries : ∀ A : Set Ω, MeasurableSet A → μ A < ∞ →
      ∀ ε : ℝ, 0 < ε →
        (∑' n, μ (A ∩ {ω | ε < dist (f ω) (fSeq n ω)})) < ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := by
  refine ae_of_forall_measure_lt_top_ae_restrict (fun ω ↦
    Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))) ?_
  intro A hA hA_fin
  exact aeTendsto_of_summableRestrictDistEvents hA hA_fin hMeasSeq hMeas (hSeries A hA hA_fin)

/-- Helper: on a finite slice, summable bad increment events force the sequence to be pointwise
Cauchy almost everywhere. -/
private lemma aeCauchySeq_of_summableRestrictStepEvents
    {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E]
    {μ : Measure Ω} {A : Set Ω} {fSeq : ℕ → Ω → E} (εSeq : ℕ → NNReal)
    (_hA : MeasurableSet A) (_hA_fin : μ A < ∞)
    (hMeasSeq : ∀ n, Measurable (fSeq n))
    (hSummable : Summable (fun n ↦ (εSeq n : ℝ)))
    (hSeries :
      (∑' n, μ (A ∩ {ω | (εSeq n : ℝ) < dist (fSeq n ω) (fSeq (n + 1) ω)})) < ∞) :
    ∀ᵐ ω ∂μ.restrict A, CauchySeq (fun n ↦ fSeq n ω) := by
  let bad : ℕ → Set Ω := fun n ↦
    {ω | (εSeq n : ℝ) < dist (fSeq n ω) (fSeq (n + 1) ω)}
  have hBad_ae :
      ∀ᵐ ω ∂μ.restrict A, ∀ᶠ n in atTop, ω ∉ bad n := by
    have hBad_meas : ∀ n, MeasurableSet (bad n) := by
      intro n
      simpa [bad] using
        measurableSet_lt measurable_const ((hMeasSeq n).dist (hMeasSeq (n + 1)))
    have hBad_ne_top : (∑' n, (μ.restrict A) (bad n)) ≠ ∞ := by
      simpa [bad, Measure.restrict_apply, hBad_meas, Set.inter_assoc, Set.inter_comm,
        Set.inter_left_comm] using (ne_of_lt hSeries)
    simpa [bad] using (ae_eventually_notMem hBad_ne_top : ∀ᵐ ω ∂μ.restrict A, _)
  filter_upwards [hBad_ae] with ω hω
  rcases eventually_atTop.1 hω with ⟨N, hN⟩
  have hTail :
      ∀ n,
        dist (fSeq (n + N) ω) (fSeq (n.succ + N) ω) ≤ εSeq (n + N) := by
    intro n
    have hNot : ω ∉ bad (n + N) := hN (n + N) (Nat.le_add_left N n)
    exact le_of_not_gt <| by
      simpa [bad, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hNot
  have hTailSummable : Summable (fun n ↦ (εSeq (n + N) : ℝ)) :=
    (_root_.summable_nat_add_iff N).2 hSummable
  have hTailCauchy : CauchySeq (fun n ↦ fSeq (n + N) ω) :=
    cauchySeq_of_dist_le_of_summable _ hTail hTailSummable
  -- Proof comment: once one tail is Cauchy, the whole sequence is Cauchy.
  exact (cauchySeq_shift N).1 hTailCauchy

/-- Helper: summable bad increment events on every finite slice globalize to an almost-everywhere
Cauchy property. -/
private lemma aeCauchySeq_of_summableStepEvents
    {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E]
    {μ : Measure Ω} [SigmaFinite μ] {fSeq : ℕ → Ω → E} (εSeq : ℕ → NNReal)
    (hMeasSeq : ∀ n, Measurable (fSeq n))
    (hSummable : Summable (fun n ↦ (εSeq n : ℝ)))
    (hSeries : ∀ A : Set Ω, MeasurableSet A → μ A < ∞ →
      (∑' n, μ (A ∩ {ω | (εSeq n : ℝ) < dist (fSeq n ω) (fSeq (n + 1) ω)})) < ∞) :
    ∀ᵐ ω ∂μ, CauchySeq (fun n ↦ fSeq n ω) := by
  refine ae_of_forall_measure_lt_top_ae_restrict (fun ω ↦ CauchySeq (fun n ↦ fSeq n ω)) ?_
  intro A hA hA_fin
  exact aeCauchySeq_of_summableRestrictStepEvents εSeq hA hA_fin hMeasSeq hSummable
    (hSeries A hA hA_fin)

/-- Helper: almost-everywhere pointwise Cauchy sequences admit an almost-everywhere pointwise limit
in a complete metric space. -/
private lemma existsAeLimit_of_aeCauchySeq
    {E : Type v} [MetricSpace E] [CompleteSpace E]
    {μ : Measure Ω} {fSeq : ℕ → Ω → E}
    (hCauchy : ∀ᵐ ω ∂μ, CauchySeq (fun n ↦ fSeq n ω)) :
    ∃ f : Ω → E, ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := by
  classical
  let f : Ω → E := fun ω ↦
    if hω : CauchySeq (fun n ↦ fSeq n ω) then
      Classical.choose (cauchySeq_tendsto_of_complete hω)
    else
      fSeq 0 ω
  refine ⟨f, ?_⟩
  -- Proof comment: pick the pointwise limit on the Cauchy set and keep an arbitrary fallback
  -- value on the null complement.
  filter_upwards [hCauchy] with ω hω
  simpa [f, hω] using Classical.choose_spec (cauchySeq_tendsto_of_complete hω)

/-- Helper for fast convergence: summable `Lᵖ` deviations imply summable real bad-event measures at
a fixed threshold. -/
private lemma summableDeviationEventMeasuresOfSummableLpNorm
    (μ : Measure Ω) {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞)
    (hMemLpSeq : ∀ n, MemLp (fSeq n) p μ) (hMemLp : MemLp f p μ)
    (hLpSummable : Summable (fun n ↦ lpNorm (fSeq n - f) p μ))
    {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n ↦ (μ {ω | ε ≤ |fSeq n ω - f ω|}).toReal) := by
  have hp_ne_zero : p ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hp_toReal : 1 ≤ p.toReal := by
    simpa using (ENNReal.toReal_mono hp_ne_top hp)
  have hLpPowSummable :
      Summable (fun n ↦ lpNorm (fSeq n - f) p μ ^ p.toReal) :=
    summableRpowOfSummable (fun n ↦ lpNorm_nonneg) hLpSummable hp_toReal
  have hScaledSummable :
      Summable (fun n ↦ ε⁻¹ ^ p.toReal * (lpNorm (fSeq n - f) p μ ^ p.toReal)) := by
    simpa [mul_comm] using hLpPowSummable.mul_left (ε⁻¹ ^ p.toReal)
  refine Summable.of_nonneg_of_le (fun n ↦ ENNReal.toReal_nonneg) ?_ hScaledSummable
  intro n
  let g : Ω → ℝ := fun ω ↦ fSeq n ω - f ω
  have hMemLpSub : MemLp g p μ := (hMemLpSeq n).sub hMemLp
  have hMeasureLeEnorm :
      μ {ω | ENNReal.ofReal ε ≤ ‖g ω‖ₑ} ≤
        (ENNReal.ofReal ε)⁻¹ ^ p.toReal * eLpNorm g p μ ^ p.toReal := by
    exact meas_ge_le_mul_pow_eLpNorm_enorm μ hp_ne_zero hp_ne_top
      hMemLpSub.aestronglyMeasurable (by positivity) (by simp)
  have hMeasureLe :
      μ {ω | ε ≤ |g ω|} ≤
        (ENNReal.ofReal ε)⁻¹ ^ p.toReal * eLpNorm g p μ ^ p.toReal := by
    -- Proof comment: Chebyshev-Markov controls the bad-event measure by the `Lᵖ` mass of the
    -- deviation `g = fₙ - f`.
    convert hMeasureLeEnorm using 6
    rename_i x
    rw [show ‖fSeq n x - f x‖ₑ = ENNReal.ofReal |fSeq n x - f x| by
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]]
    exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg (fSeq n x - f x))).symm
  have hRight_ne_top :
      ((ENNReal.ofReal ε)⁻¹ ^ p.toReal * eLpNorm g p μ ^ p.toReal) ≠ ∞ := by
    finiteness
  have hScaleToReal :
      (((ENNReal.ofReal ε)⁻¹ ^ p.toReal).toReal) = ε⁻¹ ^ p.toReal := by
    calc
      (((ENNReal.ofReal ε)⁻¹ ^ p.toReal).toReal)
          = (((ENNReal.ofReal ε)⁻¹).toReal) ^ p.toReal := by
            simpa using
              (ENNReal.toReal_rpow ((ENNReal.ofReal ε)⁻¹) (p.toReal)).symm
      _ = ε⁻¹ ^ p.toReal := by
        rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hε.le]
  have hNormToReal :
      ((eLpNorm g p μ) ^ p.toReal).toReal = lpNorm g p μ ^ p.toReal := by
    calc
      ((eLpNorm g p μ) ^ p.toReal).toReal = (eLpNorm g p μ).toReal ^ p.toReal := by
        simpa using
          (ENNReal.toReal_rpow (eLpNorm g p μ) (p.toReal)).symm
      _ = lpNorm g p μ ^ p.toReal := by
        rw [toReal_eLpNorm hMemLpSub.aestronglyMeasurable]
  -- Proof comment: convert the ENNReal bound to a real-valued comparison so summability can be
  -- handled by `Summable.of_nonneg_of_le`.
  calc
    (μ {ω | ε ≤ |g ω|}).toReal
        ≤ (((ENNReal.ofReal ε)⁻¹ ^ p.toReal) *
            (eLpNorm g p μ ^ p.toReal)).toReal :=
      ENNReal.toReal_mono hRight_ne_top hMeasureLe
    _ = (((ENNReal.ofReal ε)⁻¹ ^ p.toReal).toReal) *
          ((eLpNorm g p μ ^ p.toReal).toReal) := by
      rw [ENNReal.toReal_mul]
    _ = ε⁻¹ ^ p.toReal * lpNorm g p μ ^ p.toReal := by
      rw [hScaleToReal, hNormToReal]

/-- Helper for Theorem 6.12: summable `Lᵖ` deviations give a finite ENNReal series of bad-event
measures at a fixed threshold. -/
private lemma tsumDeviationEventMeasures_ne_top_ofSummableLpNorm
    (μ : Measure Ω) {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞)
    (hMemLpSeq : ∀ n, MemLp (fSeq n) p μ) (hMemLp : MemLp f p μ)
    (hLpSummable : Summable (fun n ↦ lpNorm (fSeq n - f) p μ))
    {ε : ℝ} (hε : 0 < ε) :
    (∑' n, μ {ω | ε ≤ |fSeq n ω - f ω|}) ≠ ∞ := by
  let bad : ℕ → Set Ω := fun n ↦ {ω | ε ≤ |fSeq n ω - f ω|}
  have hSummable :
      Summable (fun n ↦ (μ (bad n)).toReal) := by
    simpa [bad] using
      summableDeviationEventMeasuresOfSummableLpNorm μ hp hp_ne_top hMemLpSeq hMemLp
        hLpSummable hε
  have hBad_eq : ∀ n, μ (bad n) = ENNReal.ofReal ((μ (bad n)).toReal) := by
    intro n
    let g : Ω → ℝ := fun ω ↦ fSeq n ω - f ω
    have hp_ne_zero : p ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
    have hMemLpSub : MemLp g p μ := by
      simpa [g] using (hMemLpSeq n).sub hMemLp
    have hMeasureLeEnorm :
        μ {ω | ENNReal.ofReal ε ≤ ‖g ω‖ₑ} ≤
          (ENNReal.ofReal ε)⁻¹ ^ p.toReal * eLpNorm g p μ ^ p.toReal := by
      exact meas_ge_le_mul_pow_eLpNorm_enorm μ hp_ne_zero hp_ne_top
        hMemLpSub.aestronglyMeasurable (by positivity) (by simp)
    have hEnormEq : ∀ ω, ‖g ω‖ₑ = ENNReal.ofReal |g ω| := by
      intro ω
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    have hBad_eq_set : {ω | ENNReal.ofReal ε ≤ ‖g ω‖ₑ} = bad n := by
      ext ω
      simp only [bad, g, Set.mem_setOf_eq]
      rw [hEnormEq ω]
      exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg (g ω))
    have hMeasureLe :
        μ (bad n) ≤
          (ENNReal.ofReal ε)⁻¹ ^ p.toReal * eLpNorm g p μ ^ p.toReal := by
      rw [← hBad_eq_set]
      exact hMeasureLeEnorm
    have hRight_ne_top :
        ((ENNReal.ofReal ε)⁻¹ ^ p.toReal * eLpNorm g p μ ^ p.toReal) ≠ ∞ := by
      finiteness
    have hBad_lt_top : μ (bad n) < ∞ := by
      exact lt_of_le_of_lt hMeasureLe (lt_top_iff_ne_top.2 hRight_ne_top)
    -- Proof comment: each bad-event measure is finite because Chebyshev-Markov bounds it by a
    -- finite `Lᵖ` quantity, so `ENNReal.ofReal (toReal ...)` recovers the original measure.
    rw [ENNReal.ofReal_toReal hBad_lt_top.ne]
  -- Proof comment: convert the already summable real-valued bad-event series to an ENNReal series
  -- and then rewrite each term back to the original measure.
  have hSeriesEq :
      (fun n ↦ μ (bad n)) = fun n ↦ ENNReal.ofReal ((μ (bad n)).toReal) := by
    funext n
    exact hBad_eq n
  rw [hSeriesEq]
  exact hSummable.tsum_ofReal_ne_top

/-!
### Theorem 6.12

Fast convergence.
-/

/-- Helper for Theorem 6.12: clause `(i)` says that if the `Lᵖ`-deviations from `f` are summable,
then `fSeq n`
converges to `f` `μ`-almost everywhere. -/
theorem fast_convergence_i (μ : Measure Ω) {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ}
    {p : ℝ≥0∞}
    (hMeasSeq : ∀ n, Measurable (fSeq n)) (hMeas : Measurable f) (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (hMemLpSeq : ∀ n, MemLp (fSeq n) p μ) (hMemLp : MemLp f p μ)
    (hSummable : Summable (fun n ↦ lpNorm (fSeq n - f) p μ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := by
  let _ := hMeasSeq
  let _ := hMeas
  have hThresholds :
      ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ᶠ n in atTop,
        dist (fSeq n ω) (f ω) ≤ (1 : ℝ) / (k + 1) := by
    rw [ae_all_iff]
    intro k
    let ε : ℝ := (1 : ℝ) / (k + 1)
    have hε : 0 < ε := by
      positivity
    let bad : ℕ → Set Ω := fun n ↦ {ω | ε ≤ |fSeq n ω - f ω|}
    have hBad_ae : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ bad n := by
      have hBad_ne_top : (∑' n, μ (bad n)) ≠ ∞ := by
        simpa [bad, ε] using
          tsumDeviationEventMeasures_ne_top_ofSummableLpNorm μ hp hp_ne_top hMemLpSeq
            hMemLp hSummable hε
      simpa [bad] using (ae_eventually_notMem hBad_ne_top : ∀ᵐ ω ∂μ, _)
    -- Proof comment: Borel-Cantelli removes each geometric error threshold, leaving eventual
    -- control of the distance by `1 / (k + 1)` for every fixed `k`.
    filter_upwards [hBad_ae] with ω hω
    exact hω.mono fun n hn ↦ by
      have hNot : ¬ ε ≤ |fSeq n ω - f ω| := by
        simpa [bad] using hn
      have hLtAbs : |fSeq n ω - f ω| < ε := lt_of_not_ge hNot
      simpa [Real.dist_eq, ε] using hLtAbs.le
  -- Proof comment: the geometric thresholds form a countable neighborhood basis at `0`, so the
  -- thresholdwise eventual bounds assemble into metric convergence.
  filter_upwards [hThresholds] with ω hω
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  rcases eventually_atTop.1 (hω k) with ⟨N, hN⟩
  exact ⟨N, fun n hn ↦ lt_of_le_of_lt (hN n hn) hk⟩

/-- Helper for Theorem 6.12: clause `(ii)` upgrades the finite-slice summability criterion for
deviation-event measures to almost-everywhere convergence. -/
theorem fast_convergence_ii (μ : Measure Ω)
    {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] [SigmaFinite μ] {fSeq : ℕ → Ω → E} {f : Ω → E}
    (hMeasSeq : ∀ n, Measurable (fSeq n)) (hMeas : Measurable f)
    (hSeries : ∀ A : Set Ω, MeasurableSet A → μ A < ∞ →
      ∀ ε : ℝ, 0 < ε →
        (∑' n, μ (A ∩ {ω | ε < dist (f ω) (fSeq n ω)})) < ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := by
  -- Proof comment: clause `(ii)` is exactly the globalization helper already established on finite
  -- measurable slices.
  exact aeTendsto_of_summableDistEvents hMeasSeq hMeas hSeries

/-- Helper for Theorem 6.12: clause `(iii)` turns summable step-event measures into an
almost-everywhere pointwise limit in the complete target space. -/
theorem fast_convergence_iii (μ : Measure Ω)
    {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E] [SigmaFinite μ] {fSeq : ℕ → Ω → E}
    (εSeq : ℕ → NNReal) (hMeasSeq : ∀ n, Measurable (fSeq n))
    (hSummable : Summable (fun n ↦ (εSeq n : ℝ)))
    (hSeries : ∀ A : Set Ω, MeasurableSet A → μ A < ∞ →
      (∑' n, μ (A ∩ {ω | (εSeq n : ℝ) < dist (fSeq n ω) (fSeq (n + 1) ω)})) < ∞) :
    ∃ f : Ω → E, ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := by
  have hCauchy : ∀ᵐ ω ∂μ, CauchySeq (fun n ↦ fSeq n ω) :=
    aeCauchySeq_of_summableStepEvents εSeq hMeasSeq hSummable hSeries
  -- Proof comment: once the step events give an almost-everywhere Cauchy property, completeness
  -- upgrades it to an almost-everywhere pointwise limit.
  exact existsAeLimit_of_aeCauchySeq hCauchy

/-- Helper for Theorem 6.12: the almost-everywhere limit from clause `(iii)` can be chosen
measurable. -/
theorem fast_convergence_iii_measurable (μ : Measure Ω)
    {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E] [SigmaFinite μ] {fSeq : ℕ → Ω → E}
    (εSeq : ℕ → NNReal) (hMeasSeq : ∀ n, Measurable (fSeq n))
    (hSummable : Summable (fun n ↦ (εSeq n : ℝ)))
    (hSeries : ∀ A : Set Ω, MeasurableSet A → μ A < ∞ →
      (∑' n, μ (A ∩ {ω | (εSeq n : ℝ) < dist (fSeq n ω) (fSeq (n + 1) ω)})) < ∞) :
    ∃ f : Ω → E, Measurable f ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := by
  have hCauchy : ∀ᵐ ω ∂μ, CauchySeq (fun n ↦ fSeq n ω) :=
    aeCauchySeq_of_summableStepEvents εSeq hMeasSeq hSummable hSeries
  have hAeLimit :
      ∀ᵐ ω ∂μ, ∃ l : E, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 l) := by
    -- Proof comment: completeness turns the almost-everywhere Cauchy property into an almost-
    -- everywhere existence of pointwise limits.
    filter_upwards [hCauchy] with ω hω
    exact cauchySeq_tendsto_of_complete hω
  have hAEMeasSeq : ∀ n, AEMeasurable (fSeq n) μ := fun n ↦ (hMeasSeq n).aemeasurable
  -- Proof comment: use the measurable-limit theorem to choose the almost-everywhere limit in a
  -- measurable way.
  exact measurable_limit_of_tendsto_metrizable_ae hAEMeasSeq hAeLimit

/-- Theorem 6.12. Clause `(i)` is the real-valued summable-`Lᵖ` criterion,
clause `(ii)` is the summable deviation-event criterion on finite-measure slices, and clause
`(iii)` is the complete-space summable-increments criterion with a measurable almost-everywhere
limit. -/
theorem fast_convergence :
    (∀ (μ : Measure Ω) {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ} {p : ℝ≥0∞},
      (∀ n, Measurable (fSeq n)) → Measurable f → 1 ≤ p → p ≠ ∞ →
      (∀ n, MemLp (fSeq n) p μ) → MemLp f p μ →
      Summable (fun n ↦ lpNorm (fSeq n - f) p μ) →
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))) ∧
    (∀ (μ : Measure Ω) [SigmaFinite μ] {E : Type v} [MetricSpace E] [MeasurableSpace E]
        [BorelSpace E] [TopologicalSpace.SeparableSpace E] {fSeq : ℕ → Ω → E} {f : Ω → E},
      (∀ n, Measurable (fSeq n)) → Measurable f →
      (∀ A : Set Ω, MeasurableSet A → μ A < ∞ →
        ∀ ε : ℝ, 0 < ε →
          (∑' n, μ (A ∩ {ω | ε < dist (f ω) (fSeq n ω)})) < ∞) →
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))) ∧
    (∀ (μ : Measure Ω) [SigmaFinite μ] {E : Type v} [MetricSpace E] [MeasurableSpace E]
        [BorelSpace E] [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
        {fSeq : ℕ → Ω → E} (εSeq : ℕ → NNReal),
      (∀ n, Measurable (fSeq n)) →
      Summable (fun n ↦ (εSeq n : ℝ)) →
      (∀ A : Set Ω, MeasurableSet A → μ A < ∞ →
        (∑' n, μ (A ∩ {ω | (εSeq n : ℝ) < dist (fSeq n ω) (fSeq (n + 1) ω)})) < ∞) →
      ∃ f : Ω → E, Measurable f ∧
        ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ fSeq f p hMeasSeq hMeas hp hp_ne_top hMemLpSeq hMemLp hSummable
    -- Proof comment: clause `(i)` is exactly the previously established real-valued helper.
    exact fast_convergence_i μ hMeasSeq hMeas hp hp_ne_top hMemLpSeq hMemLp hSummable
  · intro μ _ E _ _ _ _ fSeq f hMeasSeq hMeas hSeries
    -- Proof comment: clause `(ii)` is just the finite-slice globalization helper.
    exact fast_convergence_ii μ hMeasSeq hMeas hSeries
  · intro μ _ E _ _ _ _ _ fSeq εSeq hMeasSeq hSummable hSeries
    -- Proof comment: clause `(iii)` packages the measurable limit produced by completeness.
    exact fast_convergence_iii_measurable μ εSeq hMeasSeq hSummable hSeries
