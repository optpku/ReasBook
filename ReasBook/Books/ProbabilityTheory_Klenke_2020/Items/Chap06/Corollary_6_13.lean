/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Remark_6_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open scoped ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MetricSpace E]

/-- Helper for Corollary 6.13: from local convergence in measure along a fixed subsequence, one can
extract a further strict subsubsequence whose `n`th term is already controlled on the `n`th
sigma-finite spanning set by the geometric error bound `2⁻ⁿ`. -/
private lemma exists_strictMono_subsubsequence_with_spanningSet_deviation_bounds
    (μ : Measure Ω) {fSeq : ℕ → Ω → E} {f : Ω → E} [SigmaFinite μ]
    {ns : ℕ → ℕ}
    (h_local : TendstoInMeasureOnFiniteMeasureSets μ (fun k ↦ fSeq (ns k)) f) :
    ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
      ∀ n,
        (μ.restrict (spanningSets μ n))
          {ω | (1 : ℝ) / (n + 1) ≤ dist (f ω) (fSeq (ns (ns' n)) ω)}
          ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
  have h_eventually :
      ∀ n, ∃ N, ∀ m ≥ N,
        (μ.restrict (spanningSets μ n))
          {ω | (1 : ℝ) / (n + 1) ≤ dist (f ω) (fSeq (ns m) ω)}
          ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    -- On each finite exhaustion set, convergence in measure makes the deviation measures small.
    have h_restrict :=
      h_local (spanningSets μ n) (measure_spanningSets_lt_top μ n)
    rw [tendstoInMeasure_iff_dist] at h_restrict
    have h_small := h_restrict ((1 : ℝ) / (n + 1)) (by positivity)
    rw [ENNReal.tendsto_atTop_zero] at h_small
    simpa [dist_comm] using h_small ((2⁻¹ : ℝ≥0∞) ^ n) (ENNReal.pow_pos (by simp) _)
  classical
  choose N hN using h_eventually
  let ns' : ℕ → ℕ := Nat.rec (N 0) fun n m ↦ max (m + 1) (N (n + 1))
  have hns'_zero : ns' 0 = N 0 := by
    simp [ns']
  have hns'_succ_eq : ∀ n, ns' (n + 1) = max (ns' n + 1) (N (n + 1)) := by
    intro n
    simp [ns']
  have hns'_succ : ∀ n, ns' n < ns' (n + 1) := by
    intro n
    rw [hns'_succ_eq]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
  have hns' : StrictMono ns' :=
    strictMono_nat_of_lt_succ hns'_succ
  have hN_le : ∀ n, N n ≤ ns' n := by
    intro n
    cases n with
    | zero =>
        simp [hns'_zero]
    | succ n =>
        rw [hns'_succ_eq]
        exact Nat.le_max_right _ _
  refine ⟨ns', hns', ?_⟩
  intro n
  exact hN n (ns' n) (hN_le n)

/-- Helper for Corollary 6.13: if the `n`th term of a sequence is controlled on the `n`th
spanning set by the geometric deviation bound `2⁻ⁿ`, then the sequence converges almost
everywhere on every fixed spanning set. -/
private lemma tendsto_ae_restrict_spanningSet_of_deviation_bounds
    (μ : Measure Ω) {g : ℕ → Ω → E} {f : Ω → E} [SigmaFinite μ]
    (N : ℕ)
    (h_bound : ∀ n,
      (μ.restrict (spanningSets μ n))
        {ω | (1 : ℝ) / (n + 1) ≤ dist (f ω) (g n ω)}
        ≤ (2⁻¹ : ℝ≥0∞) ^ n) :
    ∀ᵐ ω ∂μ.restrict (spanningSets μ N), Tendsto (fun n ↦ g n ω) atTop (𝓝 (f ω)) := by
  let ν := μ.restrict (spanningSets μ N)
  let S : ℕ → Set Ω := fun n ↦
    if n < N then univ else {ω | (1 : ℝ) / (n + 1) ≤ dist (f ω) (g n ω)}
  have hν_univ_lt_top : ν univ < ∞ := by
    simpa [ν, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using
      measure_spanningSets_lt_top μ N
  have hS_le : ∀ n, ν (S n) ≤ (if n < N then ν univ else 0) + ((2⁻¹ : ℝ≥0∞) ^ n) := by
    intro n
    by_cases hn : n < N
    · simp [S, ν, hn]
    · have hmono :
          ν {ω | (1 : ℝ) / (n + 1) ≤ dist (f ω) (g n ω)} ≤
            (μ.restrict (spanningSets μ n))
              {ω | (1 : ℝ) / (n + 1) ≤ dist (f ω) (g n ω)} := by
        exact Measure.restrict_mono_set μ (monotone_spanningSets μ (le_of_not_gt hn)) _
      calc
        ν (S n)
            = ν {ω | (1 : ℝ) / (n + 1) ≤ dist (f ω) (g n ω)} := by simp [S, hn]
        _ ≤ (μ.restrict (spanningSets μ n))
              {ω | (1 : ℝ) / (n + 1) ≤ dist (f ω) (g n ω)} := hmono
        _ ≤ (if n < N then ν univ else 0) + ((2⁻¹ : ℝ≥0∞) ^ n) := by
              simpa [hn] using h_bound n
  have h_prefix_ne_top : ∑' n, (if n < N then ν univ else 0 : ℝ≥0∞) ≠ ∞ := by
    have h_prefix_sum :
        (∑' n, (if n < N then ν univ else 0 : ℝ≥0∞)) =
          ∑ n ∈ Finset.range N, (if n < N then ν univ else 0 : ℝ≥0∞) := by
      refine tsum_eq_sum ?_
      intro n hn
      have hn' : ¬ n < N := by
        simpa [Finset.mem_range] using hn
      simp [hn']
    rw [h_prefix_sum]
    have hsum :
        Finset.sum (Finset.range N) (fun b ↦ (if b < N then ν univ else 0 : ℝ≥0∞)) ≠ ∞ := by
      exact (ENNReal.sum_lt_top.2 fun b hb ↦ by
        simp [Finset.mem_range.mp hb, hν_univ_lt_top]).ne
    simpa using hsum
  have h_geom_ne_top : ∑' n, ((2⁻¹ : ℝ≥0∞) ^ n) ≠ ∞ := by
    have h_geom_lt_top : ∑' n, ((2⁻¹ : ℝ≥0∞) ^ n) < ∞ :=
      (tsum_geometric_lt_top).2 (by simp)
    exact h_geom_lt_top.ne
  have h_series_ne_top : ∑' n, ν (S n) ≠ ∞ := by
    have h_upper :
        ∑' n, ν (S n) ≤
          (∑' n, (if n < N then ν univ else 0 : ℝ≥0∞)) + ∑' n, ((2⁻¹ : ℝ≥0∞) ^ n) := by
      calc
      ∑' n, ν (S n)
          ≤ ∑' n, ((if n < N then ν univ else 0 : ℝ≥0∞) + ((2⁻¹ : ℝ≥0∞) ^ n)) :=
            ENNReal.tsum_le_tsum hS_le
      _ = ∑' n, (if n < N then ν univ else 0 : ℝ≥0∞) + ∑' n, ((2⁻¹ : ℝ≥0∞) ^ n) := by
            rw [ENNReal.tsum_add]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h_prefix_ne_top, h_geom_ne_top⟩) h_upper
  have hμ_limsup : ν (limsup S atTop) = 0 :=
    measure_limsup_atTop_eq_zero h_series_ne_top
  have h_tendsto : ∀ ω ∈ (limsup S atTop)ᶜ, Tendsto (fun n ↦ g n ω) atTop (𝓝 (f ω)) := by
    intro ω hω
    -- Outside the limsup, only finitely many deviation events occur.
    have h_eventually_not : ∀ᶠ n in atTop, ω ∉ S n := by
      rw [Set.mem_compl_iff, mem_limsup_iff_frequently_mem, not_frequently] at hω
      exact hω
    obtain ⟨M, hM⟩ := eventually_atTop.1 h_eventually_not
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
    refine ⟨max (max N K) M, ?_⟩
    intro n hn
    have hNn : N ≤ n := by
      exact (le_max_left _ _).trans ((le_max_left _ _).trans hn)
    have hKn : K ≤ n := by
      exact (le_max_right _ _).trans ((le_max_left _ _).trans hn)
    have hSn : dist (f ω) (g n ω) < (1 : ℝ) / (n + 1) := by
      have h_not_mem : ω ∉ S n := hM n ((le_max_right _ _).trans hn)
      have hnN : ¬ n < N := not_lt.mpr hNn
      simpa [S, hnN] using h_not_mem
    have hdiv_lt : (1 : ℝ) / (n + 1) < ε := by
      exact lt_of_le_of_lt (Nat.one_div_le_one_div hKn) hK
    exact lt_trans (by simpa [dist_comm] using hSn) hdiv_lt
  rw [ae_iff]
  refine measure_mono_null (fun ω hω ↦ ?_) hμ_limsup
  rw [Set.mem_setOf_eq] at hω
  by_contra hlimsup
  exact hω (h_tendsto ω hlimsup)

variable [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.SeparableSpace E]

-- Proof sketch: for `(ii) → (i)`, use the metric from Theorem 6.7 attached to a sigma-finite
-- exhaustion to detect failure of convergence in measure on finite-measure sets; a subsequence
-- staying away from the limit cannot have an almost-everywhere convergent further subsequence by
-- Remark 6.4. For `(i) → (ii)`, apply the finite-measure subsequence criterion on the restricted
-- measures along a sigma-finite exhaustion and conclude global almost-everywhere convergence by a
-- diagonal argument together with Remark 6.3.
/-- Corollary 6.13: On a sigma-finite measure space, for measurable maps into a separable metric
space, convergence in `μ`-measure on every set of finite `μ`-measure is equivalent to
the fact that every subsequence has a sub-subsequence converging to the same limit
`μ`-almost everywhere. -/
theorem
    tendstoInMeasureOnFiniteMeasureSets_iff_every_subsequence_has_ae_subsubsequence
    (μ : Measure Ω) {fSeq : ℕ → Ω → E} {f : Ω → E}
    [SigmaFinite μ]
    (hSeq : ∀ n, Measurable (fSeq n)) :
    TendstoInMeasureOnFiniteMeasureSets μ fSeq f ↔
      ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
        ∀ᵐ ω ∂μ, Tendsto (fun i ↦ fSeq (ns (ns' i)) ω) atTop (𝓝 (f ω)) := by
  refine ⟨?_, ?_⟩
  · intro h_local ns hns
    -- Extract one diagonal subsubsequence that is controlled on the whole exhaustion.
    obtain ⟨ns', hns', h_bound⟩ :=
      exists_strictMono_subsubsequence_with_spanningSet_deviation_bounds μ
        (fun A hA_fin ↦ (h_local A hA_fin).comp hns.tendsto_atTop)
    refine ⟨ns', hns', ?_⟩
    -- The restricted almost-everywhere convergence on each spanning set glues to a global one.
    refine
      (ae_tendsto_iff_forall_ae_restrict_of_iUnion_eq_univ μ (spanningSets μ)
        (iUnion_spanningSets μ)).2 ?_
    intro N
    -- Route correction: use a direct Borel-Cantelli argument on the restricted measure
    -- `μ.restrict (spanningSets μ N)` instead of Theorem 6.12.
    exact tendsto_ae_restrict_spanningSet_of_deviation_bounds μ N h_bound
  · intro h_subseq
    -- If local convergence in measure fails on some finite-measure set, the finite-measure
    -- subsequence principle produces a contradictory bad subsequence.
    by_contra h_local
    rw [TendstoInMeasureOnFiniteMeasureSets] at h_local
    push Not at h_local
    obtain ⟨A, hA_fin, hA_bad⟩ := h_local
    let ν := μ.restrict A
    haveI : IsFiniteMeasure ν :=
      isFiniteMeasure_restrict.2 hA_fin.ne
    have h_bad_subseq :
        ¬ ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
          ∀ᵐ ω ∂ν, Tendsto (fun i ↦ fSeq (ns (ns' i)) ω) atTop (𝓝 (f ω)) := by
      have h_subseq_iff :
          TendstoInMeasure ν fSeq atTop f ↔
            ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
              ∀ᵐ ω ∂ν, Tendsto (fun i ↦ fSeq (ns (ns' i)) ω) atTop (𝓝 (f ω)) :=
        exists_seq_tendstoInMeasure_atTop_iff
          (fun n ↦ (hSeq n).aestronglyMeasurable)
      exact mt
        h_subseq_iff.mpr
        hA_bad
    push Not at h_bad_subseq
    obtain ⟨ns, hns, hns_bad⟩ := h_bad_subseq
    obtain ⟨ns', hns', h_ae⟩ := h_subseq ns hns
    have h_restrict :
        ∀ᵐ ω ∂ν, Tendsto (fun i ↦ fSeq (ns (ns' i)) ω) atTop (𝓝 (f ω)) := by
      have h_restrict_ae :
          ∀ᵐ ω ∂μ.restrict A, Tendsto (fun i ↦ fSeq (ns (ns' i)) ω) atTop (𝓝 (f ω)) :=
        ae_restrict_of_ae (by simpa using h_ae)
      simpa [ν] using h_restrict_ae
    exact hns_bad ns' hns' (h_restrict.mono fun _ hω ↦ not_not_intro hω)
