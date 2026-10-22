/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Corollary_8_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_2
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable {p : ℝ}
variable {X : ℕ → NNReal → Ω → ℝ}
variable {Xtilde : NNReal → MeasureTheory.Lp ℝ (ENNReal.ofReal p) μ}

private theorem fact_one_le_ofReal_of_one_le (hp : 1 ≤ p) :
    Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨by
    simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp⟩

section TimewiseLpLimit

/-- Helper for Exercise 21.4.3: for `s ≤ t`, conditioning the time-`t` `L^p` limit class to
`ℱ s` produces a representative of the time-`s` limit class. -/
lemma condExp_limitSlice_toLp_eq
    (hX : ∀ n : ℕ, Martingale (X n) ℱ μ)
    (hp : 1 ≤ p)
    (hlimit :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp
        ∃ h_memLpSeq : ∀ n, MemLp (X n t) (ENNReal.ofReal p) μ,
          Tendsto (fun n ↦ (h_memLpSeq n).toLp (X n t)) atTop (nhds (Xtilde t)))
    (s t : NNReal) (hst : s ≤ t) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp
    ∃ h_memLp : MemLp (μ[(Xtilde t : Ω → ℝ) | ℱ s]) (ENNReal.ofReal p) μ,
      h_memLp.toLp (μ[(Xtilde t : Ω → ℝ) | ℱ s]) = Xtilde s := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp
  rcases hlimit s with ⟨h_memLpSeq_s, h_tendsto_s⟩
  rcases hlimit t with ⟨h_memLpSeq_t, h_tendsto_t⟩
  let Y : Ω → ℝ := μ[(Xtilde t : Ω → ℝ) | ℱ s]
  have hXtilde_mem : MemLp (Xtilde t : Ω → ℝ) (ENNReal.ofReal p) μ := Lp.memLp (Xtilde t)
  have hY_mem : MemLp Y (ENNReal.ofReal p) μ := by
    -- Proof comment: conditional expectation is an `L^p` contraction on the probability space.
    simpa [Y] using hXtilde_mem.condExp_of_one_le (ℱ.le s)
  have h_tendsto_eLpNorm_t :
      Tendsto (fun n ↦ eLpNorm (X n t - (Xtilde t : Ω → ℝ)) (ENNReal.ofReal p) μ) atTop
        (nhds 0) := by
    -- Proof comment: rewrite the owner-level `Lp` convergence as vanishing `eLpNorm`.
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n ↦ X n t) h_memLpSeq_t
        (Xtilde t : Ω → ℝ) (Lp.memLp (Xtilde t))).1 (by simpa using h_tendsto_t)
  have h_tendsto_cond :
      Tendsto (fun n ↦ eLpNorm (μ[X n t | ℱ s] - Y) (ENNReal.ofReal p) μ) atTop (nhds 0) := by
    -- Proof comment: condition the convergent slices at time `t` down to the earlier sigma-algebra
    -- `ℱ s`; the Chapter 8 continuity theorem keeps the same `L^p` limit.
    simpa [Y] using
      MeasureTheory.tendsto_eLpNorm_condExp_sub_of_tendsto_eLpNorm
        (μ := μ) (p := ENNReal.ofReal p) (ℱ := ℱ s) (ℱ.le s) hXtilde_mem h_memLpSeq_t
        h_tendsto_eLpNorm_t
  have h_cond_eq (n : ℕ) :
      eLpNorm (μ[X n t | ℱ s] - Y) (ENNReal.ofReal p) μ =
        eLpNorm (X n s - Y) (ENNReal.ofReal p) μ := by
    -- Proof comment: the approximating processes are martingales, so their conditioned time-`t`
    -- slice is just the earlier slice `Xⁿ_s`.
    apply eLpNorm_congr_ae
    filter_upwards [(hX n).condExp_ae_eq hst] with ω hω
    simp [Y, hω]
  have h_tendsto_Y :
      Tendsto (fun n ↦ eLpNorm (X n s - Y) (ENNReal.ofReal p) μ) atTop (nhds 0) := by
    have hseq :
        (fun n ↦ eLpNorm (μ[X n t | ℱ s] - Y) (ENNReal.ofReal p) μ) =
          fun n ↦ eLpNorm (X n s - Y) (ENNReal.ofReal p) μ := by
      funext n
      exact h_cond_eq n
    rw [hseq] at h_tendsto_cond
    exact h_tendsto_cond
  have h_tendsto_Y_toLp :
      Tendsto (fun n ↦ (h_memLpSeq_s n).toLp (X n s)) atTop (nhds (hY_mem.toLp Y)) := by
    -- Proof comment: switch back from vanishing `eLpNorm` to convergence in the canonical `Lp`
    -- space, now with the conditioned limit representative.
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n ↦ X n s) h_memLpSeq_s Y hY_mem).2
        h_tendsto_Y
  refine ⟨hY_mem, ?_⟩
  -- Proof comment: the same `Lp` sequence has both limits, so Hausdorff uniqueness identifies the
  -- conditioned representative with the prescribed time-`s` class.
  exact tendsto_nhds_unique h_tendsto_Y_toLp h_tendsto_s

omit [IsProbabilityMeasure μ] in
/-- Helper for Exercise 21.4.3: timewise almost-everywhere equality preserves the martingale
property once the target process is already known to be strongly adapted. -/
lemma martingale_congr_ae
    {M N : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ) (hN_stronglyAdapted : StronglyAdapted ℱ N)
    (hMN : ∀ t : NNReal, M t =ᵐ[μ] N t) :
    Martingale N ℱ μ := by
  refine ⟨hN_stronglyAdapted, ?_⟩
  intro s t hst
  -- Proof comment: conditional expectation respects almost-everywhere equality, so the martingale
  -- identity transfers directly from `M` to `N`.
  exact
    (MeasureTheory.condExp_congr_ae (hMN t)).symm.trans
      ((hM.condExp_ae_eq hst).trans (hMN s))

/-
Analogy recall: mathlib's `MeasureTheory.Martingale` is function-valued, while the source limit
process here is only specified in `L^p`. The source-faithful repair is therefore to conclude that
the timewise `L^p` classes admit one representative process that is an `ℱ`-martingale.
-/
/-- Part (1) of Exercise 21.4.3: if each deterministic-time slice `X^n_t` converges in `L^p` to the
timewise limit class `X̃_t`, then the `L^p`-valued limit process `X̃` admits a representative
process that is an `ℱ`-martingale. -/
theorem martingale_of_timewise_lp_limit
    (hX : ∀ n : ℕ, Martingale (X n) ℱ μ)
    (hp : 1 ≤ p)
    (hlimit :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp
        ∃ h_memLpSeq : ∀ n, MemLp (X n t) (ENNReal.ofReal p) μ,
          Tendsto (fun n ↦ (h_memLpSeq n).toLp (X n t)) atTop (nhds (Xtilde t))) :
    ∃ Y : NNReal → Ω → ℝ,
      Martingale Y ℱ μ ∧
        (∀ t : NNReal,
          ∃ h_memLp : MemLp (Y t) (ENNReal.ofReal p) μ,
            h_memLp.toLp (Y t) = Xtilde t) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp
  let Y : NNReal → Ω → ℝ := fun t ω ↦ μ[(Xtilde t : Ω → ℝ) | ℱ t] ω
  have hY_repr :
      ∀ t : NNReal,
        ∃ h_memLp : MemLp (Y t) (ENNReal.ofReal p) μ,
          h_memLp.toLp (Y t) = Xtilde t := by
    intro t
    -- Proof comment: the diagonal case `s = t` of the helper shows that the conditioned slice
    -- still realizes the original time-`t` `L^p` class.
    simpa [Y] using condExp_limitSlice_toLp_eq hX hp hlimit t t le_rfl
  refine ⟨Y, ?_, hY_repr⟩
  refine ⟨?_, ?_⟩
  · intro t
    -- Proof comment: every slice is a conditional expectation onto `ℱ t`, hence strongly
    -- measurable with respect to that sigma-algebra.
    simpa [Y] using
      (MeasureTheory.stronglyMeasurable_condExp (μ := μ) (m := ℱ t)
        (f := (Xtilde t : Ω → ℝ)))
  · intro s t hst
    have hcond :
        μ[Y t | ℱ s] =ᵐ[μ] μ[(Xtilde t : Ω → ℝ) | ℱ s] := by
      -- Proof comment: conditioning first to `ℱ t` and then to `ℱ s` collapses to conditioning
      -- directly to `ℱ s`.
      simpa [Y] using
        (MeasureTheory.Filtration.condExp_condExp (μ := μ) (f := (Xtilde t : Ω → ℝ)) ℱ hst)
    rcases condExp_limitSlice_toLp_eq hX hp hlimit s t hst with ⟨h_memLp_st, h_repr_st⟩
    rcases hY_repr s with ⟨h_memLp_s, h_repr_s⟩
    have hLp_eq : h_memLp_st.toLp (μ[(Xtilde t : Ω → ℝ) | ℱ s]) = h_memLp_s.toLp (Y s) := by
      exact h_repr_st.trans h_repr_s.symm
    have hslice :
        μ[(Xtilde t : Ω → ℝ) | ℱ s] =ᵐ[μ] Y s := by
      exact
        (MemLp.coeFn_toLp h_memLp_st).symm.trans
          ((Lp.ext_iff.mp hLp_eq).trans (MemLp.coeFn_toLp h_memLp_s))
    exact hcond.trans hslice

variable {q : ℝ≥0∞}

omit [IsProbabilityMeasure μ] in
/-- Helper for Exercise 21.4.3: composing an `L^q`-convergent sequence with a strict monotone
subsequence preserves the same `L^q` limit. -/
lemma tendstoInLp_subsequence [Fact (1 ≤ q)]
    {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ} (h : TendstoInLp q μ fSeq f)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoInLp q μ (fun n ↦ fSeq (φ n)) f := by
  -- Proof comment: the `eLpNorm` distance to the limit still tends to `0` after composing with a
  -- subsequence that tends to `atTop`.
  refine (tendstoInLp_iff_tendsto_eLpNorm).2 ?_
  refine ⟨fun n ↦ h.memLpSeq (φ n), h.memLp, ?_⟩
  exact h.tendsto_eLpNorm.comp (StrictMono.tendsto_atTop hφ)

omit [IsProbabilityMeasure μ] in
/-- Helper for Exercise 21.4.3: the representative produced in part (1) realizes the original
fixed-time `L^p` limits as honest `TendstoInLp` statements. -/
lemma tendstoInLp_partOneRepresentative
    (hp : 1 ≤ p)
    (hlimit :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp
        ∃ h_memLpSeq : ∀ n, MemLp (X n t) (ENNReal.ofReal p) μ,
          Tendsto (fun n ↦ (h_memLpSeq n).toLp (X n t)) atTop (nhds (Xtilde t)))
    {Y : NNReal → Ω → ℝ}
    (hY_repr :
      ∀ t : NNReal,
        ∃ h_memLp : MemLp (Y t) (ENNReal.ofReal p) μ,
          h_memLp.toLp (Y t) = Xtilde t)
    (t : NNReal) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp
    TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Y t) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp
  rcases hlimit t with ⟨h_memLpSeq, h_tendsto⟩
  rcases hY_repr t with ⟨h_memLp, h_repr⟩
  refine ⟨h_memLpSeq, h_memLp, ?_⟩
  -- Proof comment: the owner-level target `Xtilde t` is exactly the `toLp` class of `Y t`.
  simpa [h_repr] using h_tendsto

omit [IsProbabilityMeasure μ] in
/-- Helper for Exercise 21.4.3: the pointwise `limsup` of any martingale subsequence is strongly
adapted, because each deterministic-time slice is a measurable `limsup` of adapted slices. -/
lemma stronglyAdapted_limsupSubsequence
    (hX : ∀ n : ℕ, Martingale (X n) ℱ μ)
    (φ : ℕ → ℕ) :
    StronglyAdapted ℱ (fun t ω ↦ limsup (fun k ↦ X (φ k) t ω) atTop) := by
  intro t
  -- Proof comment: measurability is inherited pointwise from the measurable time-`t` slices of
  -- the martingale subsequence.
  have hmeas :
      Measurable[ℱ t] fun ω ↦ limsup (fun k ↦ X (φ k) t ω) atTop := by
    simpa using
      (Measurable.limsup fun k ↦ ((hX (φ k)).stronglyMeasurable t).measurable :
        Measurable[ℱ t] fun ω ↦ limsup (fun k ↦ X (φ k) t ω) atTop)
  exact hmeas.stronglyMeasurable

/-- Helper for Exercise 21.4.3: once a subsequence converges almost everywhere to `Xc` at each
deterministic time, the fixed-time `L^p` limit from part (1) forces `Xc` to agree almost
everywhere with that representative. -/
lemma aeEq_partOneRepresentative_of_ae_tendsto_subsequence
    (hX : ∀ n : ℕ, Martingale (X n) ℱ μ)
    (hp : 1 ≤ p)
    (hlimit :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp
        ∃ h_memLpSeq : ∀ n, MemLp (X n t) (ENNReal.ofReal p) μ,
          Tendsto (fun n ↦ (h_memLpSeq n).toLp (X n t)) atTop (nhds (Xtilde t)))
    {Y Xc : NNReal → Ω → ℝ}
    (hY_repr :
      ∀ t : NNReal,
        ∃ h_memLp : MemLp (Y t) (ENNReal.ofReal p) μ,
          h_memLp.toLp (Y t) = Xtilde t)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hXc_tendsto :
      ∀ t : NNReal, ∀ᵐ ω ∂μ, Tendsto (fun k ↦ X (φ k) t ω) atTop (nhds (Xc t ω))) :
    ∀ t : NNReal, Xc t =ᵐ[μ] Y t := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp
  intro t
  have hY_tendsto :
      TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Y t) :=
    tendstoInLp_partOneRepresentative hp hlimit hY_repr t
  have hY_subseq :
      TendstoInLp (ENNReal.ofReal p) μ (fun k ↦ X (φ k) t) (Y t) :=
    tendstoInLp_subsequence hY_tendsto hφ
  have hMeasure :
      TendstoInMeasure μ (fun k ↦ X (φ k) t) atTop (Xc t) := by
    -- Proof comment: the assumed almost-everywhere convergence of the subsequence upgrades to
    -- convergence in measure on the probability space.
    refine tendstoInMeasure_of_tendsto_ae ?_ (hXc_tendsto t)
    intro k
    exact (((hX (φ k)).stronglyMeasurable t).mono (ℱ.le t)).aestronglyMeasurable
  -- Proof comment: the same subsequence cannot have two different fixed-time limits in `L^p` and
  -- in measure, except on a null set.
  exact (ae_eq_of_tendstoInLp_and_tendstoInMeasure hY_subseq hMeasure).symm

omit [IsProbabilityMeasure μ] in
/-- Helper for Exercise 21.4.3: almost-sure continuity is preserved under pathwise subtraction. -/
lemma hasAlmostSurelyContinuousPaths_sub
    {Y Z : NNReal → Ω → ℝ}
    (hY : HasAlmostSurelyContinuousPaths μ Y)
    (hZ : HasAlmostSurelyContinuousPaths μ Z) :
    HasAlmostSurelyContinuousPaths μ (fun t ω ↦ Y t ω - Z t ω) := by
  -- Proof comment: on the full-measure event where both sample paths are continuous, the
  -- difference path is again continuous.
  filter_upwards [hY, hZ] with ω hωY hωZ
  simpa [HasAlmostSurelyContinuousPaths, processPath] using hωY.sub hωZ

/-- Helper for Exercise 21.4.3: summable compact-interval increment bounds force a continuous
limit on that interval, and the pointwise `limsup` agrees with the same limit. -/
lemma continuousOn_and_limsup_eq_of_summableCompactIncrementBounds
    {u : ℕ → ℝ} (hu : Summable u)
    {f : ℕ → NNReal → ℝ} (N : NNReal)
    (hcont : ∀ n : ℕ, Continuous (f n))
    (hbound :
      ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : NNReal) N, ‖f (n + 1) t - f n t‖ ≤ u n) :
    ∃ g : NNReal → ℝ,
      ContinuousOn g (Set.Icc (0 : NNReal) N) ∧
        (∀ t ∈ Set.Icc (0 : NNReal) N, Tendsto (fun n ↦ f n t) atTop (nhds (g t))) ∧
        (∀ t ∈ Set.Icc (0 : NNReal) N, limsup (fun n ↦ f n t) atTop = g t) := by
  let inc : ℕ → NNReal → ℝ := fun n t ↦ f (n + 1) t - f n t
  let g : NNReal → ℝ := fun t ↦ f 0 t + ∑' n, inc n t
  have hcont_inc : ∀ n : ℕ, Continuous (inc n) := by
    intro n
    -- Proof comment: each increment is the difference of two continuous approximants.
    simpa [inc] using (hcont (n + 1)).sub (hcont n)
  have hcont_series :
      ContinuousOn (fun t ↦ ∑' n, inc n t) (Set.Icc (0 : NNReal) N) := by
    -- Proof comment: the compact-interval sup bounds make the increment series uniformly
    -- summable, so the series limit is continuous on `[0, N]`.
    refine continuousOn_tsum (s := Set.Icc (0 : NNReal) N) (fun n ↦ (hcont_inc n).continuousOn)
      hu ?_
    intro n t ht
    simpa [inc] using hbound n t ht
  have hpointwiseTendsto :
      ∀ t ∈ Set.Icc (0 : NNReal) N, Tendsto (fun n ↦ f n t) atTop (nhds (g t)) := by
    intro t ht
    have hnorm_summable : Summable (fun n ↦ ‖inc n t‖) := by
      -- Proof comment: each pointwise increment is absolutely summable because the compact bound
      -- is dominated by the summable control sequence `u`.
      refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) ?_ hu
      intro n
      simpa [inc] using hbound n t ht
    have hinc_summable : Summable (fun n ↦ inc n t) := hnorm_summable.of_norm
    have hseries_tendsto :
        Tendsto (fun n ↦ ∑ k ∈ Finset.range n, inc k t) atTop (nhds (∑' n, inc n t)) :=
      hinc_summable.hasSum.tendsto_sum_nat
    have hpartial :
        (fun n ↦ ∑ k ∈ Finset.range n, inc k t) = fun n ↦ f n t - f 0 t := by
      -- Proof comment: the increment partial sums telescope back to the original sequence.
      ext n
      simpa [inc] using (Finset.sum_range_sub fun k : ℕ ↦ f k t) n
    rw [hpartial] at hseries_tendsto
    have hshifted :
        Tendsto (fun n ↦ f n t - f 0 t + f 0 t) atTop
          (nhds ((∑' n, inc n t) + f 0 t)) :=
      Tendsto.add_const (f 0 t) hseries_tendsto
    simpa [g, add_comm, add_left_comm, add_assoc, sub_add_cancel] using hshifted
  refine ⟨g, (hcont 0).continuousOn.add hcont_series, hpointwiseTendsto, ?_⟩
  · intro t ht
    -- Proof comment: once the compact-slice sequence converges pointwise, its `limsup` is the
    -- same limit.
    exact (hpointwiseTendsto t ht).limsup_eq

omit [IsProbabilityMeasure μ] in
/-- Helper for Exercise 21.4.3: a subsequence of almost surely continuous processes is almost
surely simultaneously continuous at every subsequence index. -/
lemma ae_all_continuous_subsequence_paths
    (hcont : ∀ n : ℕ, HasAlmostSurelyContinuousPaths μ (X n))
    (φ : ℕ → ℕ) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, Continuous (processPath (X (φ k)) ω) := by
  -- Proof comment: `ae_all_iff` packages the countable family of full-measure continuity events
  -- for the chosen subsequence onto one common full-measure event.
  exact ae_all_iff.2 fun k ↦ by
    simpa [HasAlmostSurelyContinuousPaths] using hcont (φ k)

omit [IsProbabilityMeasure μ] in
/-- Helper for Exercise 21.4.3: a geometric `2^{-k}` bound on event probabilities is summable, so
the first Borel--Cantelli lemma gives almost-sure eventual avoidance of those events. -/
lemma ae_eventually_notMem_of_geometric_half_bound
    {A : ℕ → Set Ω}
    (hA : ∀ k : ℕ, μ (A k) ≤ ENNReal.ofReal (((1 : ℝ) / 2) ^ k)) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ω ∉ A k := by
  have hgeomSummable : Summable (fun k : ℕ ↦ (((1 : ℝ) / 2) : ℝ) ^ k) :=
    summable_geometric_two
  have hgeom_ne_top :
      (∑' k : ℕ, ENNReal.ofReal ((((1 : ℝ) / 2) : ℝ) ^ k)) ≠ ∞ := by
    simpa using hgeomSummable.tsum_ofReal_ne_top
  have hsum_lt_top : (∑' k : ℕ, μ (A k)) < ∞ := by
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hA) ?_
    exact lt_top_iff_ne_top.mpr hgeom_ne_top
  -- Proof comment: once the event masses form a summable series, Borel--Cantelli gives eventual
  -- exclusion almost surely.
  exact MeasureTheory.ae_eventually_notMem hsum_lt_top.ne

/-- Helper for Exercise 21.4.3: shifting the geometric half-power sequence preserves
summability. -/
private lemma summable_halfPow_natAdd (s : ℕ) :
    Summable (fun m : ℕ ↦ ((1 : ℝ) / 2) ^ (m + s)) := by
  have hgeom : Summable (fun m : ℕ ↦ ((1 : ℝ) / 2 : ℝ) ^ m) := summable_geometric_two
  -- Proof comment: `summable_nat_add_iff` deletes a finite prefix and leaves the same geometric
  -- tail.
  simpa using
    (summable_nat_add_iff (f := fun m : ℕ ↦ ((1 : ℝ) / 2 : ℝ) ^ m) s).2 hgeom

/-- Helper for Exercise 21.4.3: sample the ambient filtration along a monotone deterministic time
map `τ`. -/
private def sampledFiltration (τ : ℕ → NNReal) (hτ : Monotone τ) :
    Filtration ℕ mΩ :=
  Filtration.mk (fun n ↦ ℱ (τ n))
    (fun _ _ hij ↦ ℱ.mono (hτ hij))
    (fun n ↦ ℱ.le (τ n))

/-- Helper for Exercise 21.4.3: a martingale remains a martingale after monotone deterministic
sampling. -/
private theorem sampledMartingaleOfMonotone
    {Y : NNReal → Ω → ℝ}
    (hY : Martingale Y ℱ μ)
    {τ : ℕ → NNReal} (hτ : Monotone τ) :
    Martingale (fun n ω ↦ Y (τ n) ω) (sampledFiltration (ℱ := ℱ) τ hτ) μ := by
  -- Proof comment: the sampled process inherits adaptation, integrability, and the martingale
  -- conditional-expectation identity directly from the ambient continuous-time martingale.
  refine martingale_nat ?_ ?_ ?_
  · intro n
    simpa [sampledFiltration] using hY.stronglyAdapted (τ n)
  · intro n
    exact hY.integrable (τ n)
  · intro n
    simpa [sampledFiltration] using
      (hY.condExp_ae_eq (i := τ n) (j := τ (n + 1)) (hτ (Nat.le_succ n))).symm

/-- Helper for Exercise 21.4.3: the dyadic row up to the integer horizon `N + 1` is truncated at
the deterministic cutoff `(N + 1) 2^n`. -/
private def integerDyadicCutoff (N n : ℕ) : ℕ :=
  (N + 1) * 2 ^ n

/-- Helper for Exercise 21.4.3: the `k`-th dyadic sample time in the row of mesh `2^{-n}`,
truncated at the integer horizon `N + 1`. -/
private def integerDyadicPoint (N n k : ℕ) : NNReal :=
  min (N + 1 : NNReal) ((k : NNReal) / (2 : NNReal) ^ n)

/-- Helper for Exercise 21.4.3: the dyadic sample times stay inside the interval
`[0, N + 1]`. -/
private lemma integerDyadicPoint_mem_Icc (N n k : ℕ) :
    integerDyadicPoint N n k ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal) := by
  -- Proof comment: truncation by the minimum enforces the upper bound, and both coordinates are
  -- nonnegative.
  refine Set.mem_Icc.mpr ⟨zero_le _, min_le_left _ _⟩

/-- Helper for Exercise 21.4.3: along a fixed dyadic row, the sample times are monotone in the
grid index. -/
private lemma integerDyadicPoint_mono (N n : ℕ) :
    Monotone (integerDyadicPoint N n) := by
  intro i j hij
  -- Proof comment: `k ↦ k / 2^n` is monotone, and taking `min (N + 1)` preserves order.
  refine min_le_min le_rfl ?_
  have hij' : (i : NNReal) ≤ (j : NNReal) := by
    exact_mod_cast hij
  simpa [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right hij'
      (inv_nonneg.mpr (show 0 ≤ (2 : NNReal) ^ n by positivity))

/-- Helper for Exercise 21.4.3: the cutoff index samples the terminal time `N + 1` exactly. -/
private lemma integerDyadicPoint_cutoff (N n : ℕ) :
    integerDyadicPoint N n (integerDyadicCutoff N n) = (N + 1 : NNReal) := by
  -- Proof comment: at the deterministic cutoff, the untruncated dyadic time is already `N + 1`,
  -- so the minimum collapses to the terminal horizon.
  unfold integerDyadicPoint integerDyadicCutoff
  apply min_eq_left
  have hpow_ne : (2 : NNReal) ^ n ≠ 0 := by positivity
  have hcutoff :
      (↑((N + 1) * 2 ^ n) : NNReal) / (2 : NNReal) ^ n = (N : NNReal) + 1 := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    calc
      (((N : NNReal) + 1) * (2 : NNReal) ^ n) / (2 : NNReal) ^ n
          = ((N : NNReal) + 1) * (((2 : NNReal) ^ n) / ((2 : NNReal) ^ n)) := by
              exact
                mul_div_assoc ((N : NNReal) + 1) ((2 : NNReal) ^ n) ((2 : NNReal) ^ n)
      _ = (N : NNReal) + 1 := by
              rw [div_self hpow_ne, mul_one]
  exact le_of_eq hcutoff.symm

/-- Helper for Exercise 21.4.3: refining the dyadic mesh preserves the old sample points as even
indices of the next row. -/
private lemma integerDyadicPoint_even (N n k : ℕ) :
    integerDyadicPoint N (n + 1) (2 * k) = integerDyadicPoint N n k := by
  -- Proof comment: after coercing to `ℝ`, the dyadic-time identity is the elementary equality
  -- `(2 * k) / 2^(n + 1) = k / 2^n`.
  apply Subtype.ext
  have hratio :
      (((2 * k : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) = ((k : ℝ) / (2 : ℝ) ^ n) := by
    rw [Nat.cast_mul, pow_succ]
    have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp [hpow_ne]
    ring
  simpa [integerDyadicPoint] using congrArg (min ((N + 1 : NNReal) : ℝ)) hratio

/-- Helper for Exercise 21.4.3: the sampled filtration on the integer dyadic row. -/
private def integerDyadicSampleFiltration (N n : ℕ) :
    Filtration ℕ mΩ :=
  sampledFiltration (ℱ := ℱ) (integerDyadicPoint N n) (integerDyadicPoint_mono N n)

/-- Helper for Exercise 21.4.3: the finite dyadic index set is nonempty because it contains the
initial index `0`. -/
private lemma integerDyadicGridIndex_nonempty (N n : ℕ) :
    (Finset.range (integerDyadicCutoff N n + 1)).Nonempty :=
  (Finset.nonempty_range_iff).2 (Nat.succ_ne_zero _)

/-- Helper for Exercise 21.4.3: the deterministic dyadic sample of a process along the row of
mesh `2^{-n}` up to the integer horizon `N + 1`. -/
private def integerDyadicSampleProcess
    (Y : NNReal → Ω → ℝ) (N n : ℕ) : ℕ → Ω → ℝ :=
  fun k ω ↦ Y (integerDyadicPoint N n k) ω

/-- Helper for Exercise 21.4.3: the dyadic running maximum on the row of mesh `2^{-n}` up to the
integer horizon `N + 1`. -/
private def integerDyadicGridAbsMax
    (Y : NNReal → Ω → ℝ) (N n : ℕ) : Ω → ℝ :=
  fun ω ↦
    (Finset.range (integerDyadicCutoff N n + 1)).sup'
      (integerDyadicGridIndex_nonempty N n)
      (fun k ↦ |integerDyadicSampleProcess Y N n k ω|)

/-- Helper for Exercise 21.4.3: the sampled difference martingale on an integer dyadic row is
still a discrete-time martingale. -/
private lemma integerDyadicSample_martingale
    {Y : NNReal → Ω → ℝ}
    (hY : Martingale Y ℱ μ)
    (N n : ℕ) :
    Martingale (integerDyadicSampleProcess Y N n)
      (integerDyadicSampleFiltration (ℱ := ℱ) N n) μ := by
  -- Proof comment: this is the monotone-sampling bridge specialized to the dyadic time map.
  simpa [integerDyadicSampleProcess, integerDyadicSampleFiltration] using
    sampledMartingaleOfMonotone (ℱ := ℱ) (μ := μ) hY (integerDyadicPoint_mono N n)

omit mΩ in
/-- Helper for Exercise 21.4.3: thresholding the dyadic row maximum is equivalent to thresholding
one sampled value on the same row. -/
private lemma threshold_le_integerDyadicGridAbsMax_iff
    (Y : NNReal → Ω → ℝ) (N n : ℕ) (ω : Ω) {threshold : ℝ} :
    threshold ≤ integerDyadicGridAbsMax Y N n ω ↔
      ∃ k ≤ integerDyadicCutoff N n, threshold ≤ |integerDyadicSampleProcess Y N n k ω| := by
  constructor
  · intro h
    let s := Finset.range (integerDyadicCutoff N n + 1)
    have hs : s.Nonempty := integerDyadicGridIndex_nonempty N n
    rcases Finset.exists_mem_eq_sup' (s := s) hs
      (fun k ↦ |integerDyadicSampleProcess Y N n k ω|) with ⟨k, hk, hk_eq⟩
    have h' : threshold ≤ s.sup' hs (fun k ↦ |integerDyadicSampleProcess Y N n k ω|) := by
      simpa [integerDyadicGridAbsMax, s] using h
    refine ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), ?_⟩
    rwa [hk_eq] at h'
  · rintro ⟨k, hk, hk_threshold⟩
    have hk_mem : k ∈ Finset.range (integerDyadicCutoff N n + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    calc
      threshold ≤ |integerDyadicSampleProcess Y N n k ω| := hk_threshold
      _ ≤ integerDyadicGridAbsMax Y N n ω := by
          simpa [integerDyadicGridAbsMax] using
            (Finset.le_sup' (s := Finset.range (integerDyadicCutoff N n + 1))
              (f := fun j : ℕ ↦ |integerDyadicSampleProcess Y N n j ω|) hk_mem)

/-- Helper for Exercise 21.4.3: the Chapter 11 discrete Doob tail theorem applies verbatim to one
integer dyadic row. -/
private lemma integerDyadicRow_doobLp_tail_bound
    {Y : NNReal → Ω → ℝ}
    (hY : Martingale Y ℱ μ)
    {p threshold : ℝ} (hp : 1 ≤ p) (hthreshold : 0 < threshold)
    (N n : ℕ) :
    ENNReal.ofReal (Real.rpow threshold p) *
        μ {ω | threshold ≤ integerDyadicGridAbsMax Y N n ω} ≤
      ∫⁻ ω, ENNReal.ofReal (Real.rpow |Y (N + 1) ω| p) ∂μ := by
  -- Proof comment: specialize discrete Doob to the sampled row, then rewrite the running maximum
  -- event and the terminal sample back to the continuous-time process at horizon `N + 1`.
  have hset_eq :
      {ω | threshold ≤ integerDyadicGridAbsMax Y N n ω} =
        {ω | ∃ k ≤ integerDyadicCutoff N n,
            threshold ≤ |integerDyadicSampleProcess Y N n k ω|} := by
    ext ω
    simpa using threshold_le_integerDyadicGridAbsMax_iff Y N n ω (threshold := threshold)
  rw [hset_eq]
  simpa [integerDyadicSampleProcess, integerDyadicSampleFiltration, integerDyadicPoint_cutoff] using
    (doobLp_tail_bound
      (X := integerDyadicSampleProcess Y N n)
      (ℱ := integerDyadicSampleFiltration (ℱ := ℱ) N n)
      (μ := μ)
      (Or.inl (integerDyadicSample_martingale (ℱ := ℱ) (μ := μ) hY N n))
      hp hthreshold (integerDyadicCutoff N n))

omit mΩ in
/-- Helper for Exercise 21.4.3: the integer dyadic row maxima increase under dyadic refinement. -/
private lemma integerDyadicGridAbsMax_mono
    (Y : NNReal → Ω → ℝ) (N n : ℕ) (ω : Ω) :
    integerDyadicGridAbsMax Y N n ω ≤ integerDyadicGridAbsMax Y N (n + 1) ω := by
  -- Proof comment: each coarse-grid sample reappears at an even index of the refined row, so the
  -- coarse row maximum is bounded by the refined one.
  let s := Finset.range (integerDyadicCutoff N n + 1)
  have hs : s.Nonempty := integerDyadicGridIndex_nonempty N n
  rcases Finset.exists_mem_eq_sup' (s := s) hs
    (fun k ↦ |integerDyadicSampleProcess Y N n k ω|) with ⟨k, hk, hk_eq⟩
  have hk' :
      2 * k ∈ Finset.range (integerDyadicCutoff N (n + 1) + 1) := by
    refine Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
    calc
      2 * k ≤ 2 * integerDyadicCutoff N n := Nat.mul_le_mul_left 2 (Nat.lt_succ_iff.mp <|
        Finset.mem_range.mp hk)
      _ = integerDyadicCutoff N (n + 1) := by
        simp [integerDyadicCutoff, Nat.pow_succ]
        ring
  have hsample :
      |integerDyadicSampleProcess Y N n k ω| ≤ integerDyadicGridAbsMax Y N (n + 1) ω := by
    calc
      |integerDyadicSampleProcess Y N n k ω|
          = |integerDyadicSampleProcess Y N (n + 1) (2 * k) ω| := by
              simp [integerDyadicSampleProcess, integerDyadicPoint_even]
      _ ≤ integerDyadicGridAbsMax Y N (n + 1) ω := by
            simpa [integerDyadicGridAbsMax] using
              (Finset.le_sup' (s := Finset.range (integerDyadicCutoff N (n + 1) + 1))
                (f := fun j : ℕ ↦ |integerDyadicSampleProcess Y N (n + 1) j ω|) hk')
  simpa [integerDyadicGridAbsMax, s, hk_eq] using hsample

/-- Helper for Exercise 21.4.3: the floor dyadic approximation along the `n`-th row converges to
the target time from below. -/
private lemma integerDyadicPoint_floor_tendsto
    (N : ℕ) {t : NNReal} (ht : t ≤ (N + 1 : NNReal)) :
    Tendsto
      (fun n : ℕ ↦ integerDyadicPoint N n (⌊((t : ℝ) * (2 : ℝ) ^ n)⌋₊))
      atTop (nhds t) := by
  have hpow :
      Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hfloor :
      Tendsto
        (fun x : ℝ ↦ (⌊(t : ℝ) * x⌋₊ : ℝ) / x)
        atTop (nhds (t : ℝ)) :=
    tendsto_nat_floor_mul_div_atTop (show 0 ≤ (t : ℝ) by exact_mod_cast t.2)
  have hcoe :
      Tendsto
        (fun n : ℕ ↦
          (((integerDyadicPoint N n (⌊((t : ℝ) * (2 : ℝ) ^ n)⌋₊)) : NNReal) : ℝ))
        atTop (nhds (t : ℝ)) := by
    have hEq :
        (fun n : ℕ ↦
          (((integerDyadicPoint N n (⌊((t : ℝ) * (2 : ℝ) ^ n)⌋₊)) : NNReal) : ℝ)) =
          fun n : ℕ ↦ (⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊ : ℝ) / (2 : ℝ) ^ n := by
      funext n
      have hdiv_le_t :
          (⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊ : ℝ) / (2 : ℝ) ^ n ≤ (t : ℝ) := by
        have hpow_pos : 0 < (2 : ℝ) ^ n := by positivity
        refine (div_le_iff₀ hpow_pos).2 ?_
        simpa [mul_comm] using
          (Nat.floor_le (show 0 ≤ (t : ℝ) * (2 : ℝ) ^ n by positivity))
      have hdiv_le_t_nn :
          ((⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊ : ℕ) : NNReal) / (2 : NNReal) ^ n ≤ t := by
        exact_mod_cast hdiv_le_t
      have hdiv_le_horizon :
          ((⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊ : ℕ) : NNReal) / (2 : NNReal) ^ n ≤
            (N + 1 : NNReal) :=
        hdiv_le_t_nn.trans ht
      have hmin :
          integerDyadicPoint N n (⌊((t : ℝ) * (2 : ℝ) ^ n)⌋₊) =
            ((⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊ : ℕ) : NNReal) / (2 : NNReal) ^ n := by
        unfold integerDyadicPoint
        exact min_eq_right hdiv_le_horizon
      exact congrArg (fun x : NNReal => (x : ℝ)) hmin
    rw [hEq]
    exact hfloor.comp hpow
  exact NNReal.tendsto_coe.1 hcoe

omit mΩ in
/-- Helper for Exercise 21.4.3: on a continuous path, any threshold crossing on `[0, N + 1]`
already appears on some integer dyadic row. -/
private lemma continuousThresholdCrossing_exists_integerDyadicWitness
    {Δ : NNReal → Ω → ℝ} {ω : Ω} {N : ℕ} {a : ℝ}
    (hcont : Continuous (processPath Δ ω))
    (hcross :
      ∃ t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal), a < |Δ t ω|) :
    ∃ n : ℕ, a < integerDyadicGridAbsMax Δ N n ω := by
  rcases hcross with ⟨t, ht, ht_cross⟩
  let k : ℕ → ℕ := fun n ↦ ⌊((t : ℝ) * (2 : ℝ) ^ n)⌋₊
  have happrox :
      Tendsto (fun n : ℕ ↦ integerDyadicPoint N n (k n)) atTop (nhds t) := by
    simpa [k] using integerDyadicPoint_floor_tendsto (N := N) ht.2
  have hnear :
      {s : NNReal | a < |Δ s ω|} ∈ nhds t := by
    -- Proof comment: the strict threshold event is open along a continuous sample path.
    exact (isOpen_lt continuous_const hcont.abs).mem_nhds ht_cross
  have hevent :
      ∀ᶠ n in atTop, a < |Δ (integerDyadicPoint N n (k n)) ω| := by
    exact happrox hnear
  rcases Filter.eventually_atTop.1 hevent with ⟨n0, hn0⟩
  have hk_le : k n0 ≤ integerDyadicCutoff N n0 := by
    have hfloor_le :
        (k n0 : ℝ) ≤ (t : ℝ) * (2 : ℝ) ^ n0 := by
      simpa [k] using
        (Nat.floor_le (show 0 ≤ (t : ℝ) * (2 : ℝ) ^ n0 by positivity))
    have ht_le :
        (t : ℝ) ≤ (N + 1 : ℝ) := by
      exact_mod_cast ht.2
    have hupper :
        (t : ℝ) * (2 : ℝ) ^ n0 ≤ (integerDyadicCutoff N n0 : ℝ) := by
      have hpow_nonneg : 0 ≤ (2 : ℝ) ^ n0 := by positivity
      calc
        (t : ℝ) * (2 : ℝ) ^ n0 ≤ (N + 1 : ℝ) * (2 : ℝ) ^ n0 :=
          mul_le_mul_of_nonneg_right ht_le hpow_nonneg
        _ = (integerDyadicCutoff N n0 : ℝ) := by
            simp [integerDyadicCutoff, Nat.cast_mul, Nat.cast_pow]
    exact_mod_cast hfloor_le.trans hupper
  have hk_mem :
      k n0 ∈ Finset.range (integerDyadicCutoff N n0 + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le)
  refine ⟨n0, lt_of_lt_of_le (hn0 n0 le_rfl) ?_⟩
  -- Proof comment: the chosen floor dyadic point is one sample on the row, so its absolute value
  -- is bounded by the row maximum.
  simpa [integerDyadicGridAbsMax, integerDyadicSampleProcess] using
    (Finset.le_sup' (s := Finset.range (integerDyadicCutoff N n0 + 1))
      (f := fun j : ℕ ↦ |integerDyadicSampleProcess Δ N n0 j ω|) hk_mem)

omit [IsProbabilityMeasure μ] in
/-- Helper for Exercise 21.4.3: fixed-time `L^p` convergence makes sufficiently late integer
horizons pairwise close in the `L^p` seminorm. -/
private lemma eventually_smallELpNormDifferenceAtIntegerHorizon
    {Y : NNReal → Ω → ℝ}
    (hp : 1 < p)
    (hY_tendsto :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp.le
        TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Y t))
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      eLpNorm (X m (k + 1) - X n (k + 1)) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp.le
  let t : NNReal := (k + 1 : NNReal)
  have hε2 : 0 < ε / 2 := by linarith
  have hsmall :
      ∀ᶠ n in atTop,
        eLpNorm (X n t - Y t) (ENNReal.ofReal p) μ < ENNReal.ofReal (ε / 2) := by
    have hconv := (hY_tendsto t).tendsto_eLpNorm
    exact hconv (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε2))
  rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hm' := hN m hm
  have hn' := hN n hn
  have hm_mem :
      MemLp (X m t - Y t) (ENNReal.ofReal p) μ :=
    ((hY_tendsto t).memLpSeq m).sub (hY_tendsto t).memLp
  have hn_mem :
      MemLp (Y t - X n t) (ENNReal.ofReal p) μ :=
    (hY_tendsto t).memLp.sub ((hY_tendsto t).memLpSeq n)
  have htriangle :
      eLpNorm ((X m t - Y t) + (Y t - X n t)) (ENNReal.ofReal p) μ ≤
        eLpNorm (X m t - Y t) (ENNReal.ofReal p) μ +
          eLpNorm (Y t - X n t) (ENNReal.ofReal p) μ := by
    exact
      eLpNorm_add_le hm_mem.aestronglyMeasurable hn_mem.aestronglyMeasurable
        (by
          simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le)
  have hneg :
      eLpNorm (Y t - X n t) (ENNReal.ofReal p) μ =
        eLpNorm (X n t - Y t) (ENNReal.ofReal p) μ := by
    simpa [sub_eq_add_neg, add_comm] using
      (eLpNorm_neg (f := X n t - Y t) (p := ENNReal.ofReal p) (μ := μ))
  have hsplit : X m t - X n t = (X m t - Y t) + (Y t - X n t) := by
    ext ω
    change X m t ω - X n t ω = (X m t ω - Y t ω) + (Y t ω - X n t ω)
    ring
  calc
    eLpNorm (X m t - X n t) (ENNReal.ofReal p) μ
        = eLpNorm ((X m t - Y t) + (Y t - X n t)) (ENNReal.ofReal p) μ := by
            rw [hsplit]
    _ ≤ eLpNorm (X m t - Y t) (ENNReal.ofReal p) μ +
          eLpNorm (Y t - X n t) (ENNReal.ofReal p) μ := htriangle
    _ = eLpNorm (X m t - Y t) (ENNReal.ofReal p) μ +
          eLpNorm (X n t - Y t) (ENNReal.ofReal p) μ := by rw [hneg]
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hm'.le hn'.le
    _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add hε2.le hε2.le]
          ring
omit [IsProbabilityMeasure μ] in
/-- Helper for Exercise 21.4.3: one can choose a strict subsequence whose consecutive differences
are `L^p`-small at every earlier integer horizon. -/
private lemma existsStrictMonoSubsequence_smallEarlierIntegerHorizons
    {Y : NNReal → Ω → ℝ}
    (hp : 1 < p)
    (hY_tendsto :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp.le
        TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Y t)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k N : ℕ, N ≤ k →
        eLpNorm (X (φ (k + 1)) (N + 1) - X (φ k) (N + 1)) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (((1 : ℝ) / 2) ^ (2 * k)) := by
  classical
  have hsmall :
      ∀ horizon stage : ℕ,
        ∃ cutoff : ℕ,
          ∀ m ≥ cutoff, ∀ n ≥ cutoff,
            eLpNorm (X m (horizon + 1) - X n (horizon + 1)) (ENNReal.ofReal p) μ ≤
              ENNReal.ofReal (((1 : ℝ) / 2) ^ (2 * stage)) := by
    intro horizon stage
    exact
      eventually_smallELpNormDifferenceAtIntegerHorizon
        (μ := μ) (X := X) (p := p) hp hY_tendsto horizon
        (ε := ((1 : ℝ) / 2) ^ (2 * stage))
        (pow_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) _)
  choose cutoff hcutoff using hsmall
  let φ : ℕ → ℕ :=
    Nat.rec (cutoff 0 0) fun k m ↦
      max (m + 1) ((Finset.range (k + 2)).sup fun j ↦ cutoff j (k + 1))
  have hφ_succ :
      ∀ k : ℕ,
        φ (k + 1) = max (φ k + 1) ((Finset.range (k + 2)).sup fun j ↦ cutoff j (k + 1)) := by
    intro k
    simp [φ]
  have hφ_strict : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun k ↦ ?_
    rw [hφ_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
  have hcutoff_le :
      ∀ k N : ℕ, N ≤ k → cutoff N k ≤ φ k := by
    intro k N hNk
    cases k with
    | zero =>
        have hN0 : N = 0 := Nat.eq_zero_of_le_zero hNk
        simp [φ, hN0]
    | succ k =>
        rw [hφ_succ]
        exact le_trans
          (Finset.le_sup (s := Finset.range (k + 2)) (f := fun j ↦ cutoff j (k + 1))
            (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hNk)))
          (Nat.le_max_right _ _)
  refine ⟨φ, hφ_strict, ?_⟩
  intro k N hNk
  have hφk_ge : cutoff N k ≤ φ k := hcutoff_le k N hNk
  have hφksucc_ge : cutoff N k ≤ φ (k + 1) := by
    exact le_trans hφk_ge (Nat.le_of_lt (hφ_strict (Nat.lt_succ_self k)))
  exact hcutoff N k (φ (k + 1)) hφksucc_ge (φ k) hφk_ge

/-- Helper for Exercise 21.4.3: the dyadic-row Doob bound converts a terminal `eLpNorm` estimate
into a probability bound for one compact row crossing event. -/
private lemma rowCrossingMeasure_le_of_eLpNormBound
    {Δ : NNReal → Ω → ℝ}
    (hΔ : Martingale Δ ℱ μ)
    (hp : 1 < p)
    {N n : ℕ} {threshold ε : ℝ}
    (hthreshold : 0 < threshold)
    (hε : 0 ≤ ε)
    (hnorm : eLpNorm (Δ (N + 1)) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε) :
    μ {ω | threshold ≤ integerDyadicGridAbsMax Δ N n ω} ≤
      ENNReal.ofReal (Real.rpow ε p) / ENNReal.ofReal (Real.rpow threshold p) := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.le
  let q : NNReal := ⟨p, hp0⟩
  have hq_ne : q ≠ 0 := by
    intro hq
    have hp_zero : p = 0 := by
      simpa [q] using congrArg (fun x : NNReal ↦ (x : ℝ)) hq
    linarith
  have hmoment_eq :
      ∫⁻ ω, ENNReal.ofReal (Real.rpow |Δ (N + 1) ω| p) ∂μ =
        eLpNorm (Δ (N + 1)) (ENNReal.ofReal p) μ ^ p := by
    -- Proof comment: rewrite the terminal `p`-moment as the `p`-th power of the `eLpNorm`.
    calc
      ∫⁻ ω, ENNReal.ofReal (Real.rpow |Δ (N + 1) ω| p) ∂μ
          = ∫⁻ ω, ‖Δ (N + 1) ω‖ₑ ^ p ∂μ := by
              congr with ω
              calc
                ENNReal.ofReal (Real.rpow |Δ (N + 1) ω| p)
                    = ENNReal.ofReal |Δ (N + 1) ω| ^ p := by
                        symm
                        exact ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0
                _ = ‖Δ (N + 1) ω‖ₑ ^ p := by
                      rw [← Real.norm_eq_abs, ofReal_norm_eq_enorm]
      _ = eLpNorm (Δ (N + 1)) (q : ℝ≥0∞) μ ^ p := by
            simpa [q] using
              (MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
                (μ := μ) (f := Δ (N + 1)) (p := q) hq_ne).symm
      _ = eLpNorm (Δ (N + 1)) (ENNReal.ofReal p) μ ^ p := by
            have hq_cast : (q : ℝ≥0∞) = ENNReal.ofReal p :=
              (ENNReal.ofReal_eq_coe_nnreal hp0).symm
            rw [hq_cast]
  have hmoment_le :
      ∫⁻ ω, ENNReal.ofReal (Real.rpow |Δ (N + 1) ω| p) ∂μ ≤
        ENNReal.ofReal (Real.rpow ε p) := by
    -- Proof comment: the terminal `eLpNorm` bound upgrades to the matching terminal `p`-moment
    -- bound after raising both sides to the exponent `p`.
    rw [hmoment_eq]
    calc
      eLpNorm (Δ (N + 1)) (ENNReal.ofReal p) μ ^ p ≤ (ENNReal.ofReal ε) ^ p := by
        exact ENNReal.rpow_le_rpow hnorm hp0
      _ = ENNReal.ofReal (Real.rpow ε p) := by
        simpa using (ENNReal.ofReal_rpow_of_nonneg hε hp0)
  have hrow :=
    integerDyadicRow_doobLp_tail_bound
      (ℱ := ℱ) (μ := μ) (Y := Δ) hΔ hp.le hthreshold N n
  have hthreshold_pos : 0 < ENNReal.ofReal (Real.rpow threshold p) := by
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hthreshold p)
  have hthreshold_ne_zero : ENNReal.ofReal (Real.rpow threshold p) ≠ 0 :=
    ne_of_gt hthreshold_pos
  have hthreshold_ne_top : ENNReal.ofReal (Real.rpow threshold p) ≠ ∞ := by
    simp
  exact
    (ENNReal.le_div_iff_mul_le (Or.inl hthreshold_ne_zero) (Or.inl hthreshold_ne_top)).2 <|
      by
        simpa [mul_comm] using hrow.trans hmoment_le

/-- Helper for Exercise 21.4.3: the diagonal integer-horizon `L^p` control implies geometric
compact-interval bad-event bounds for consecutive subsequence differences. -/
private lemma compactTailBadEvent_measure_le_geometric
    (hX : ∀ n : ℕ, Martingale (X n) ℱ μ)
    (hcont : ∀ n : ℕ, HasAlmostSurelyContinuousPaths μ (X n))
    (hp : 1 < p)
    {φ : ℕ → ℕ}
    (hsmall :
      ∀ k N : ℕ, N ≤ k →
        eLpNorm (X (φ (k + 1)) (N + 1) - X (φ k) (N + 1)) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (((1 : ℝ) / 2) ^ (2 * k)))
    (N m : ℕ) :
    μ {ω | ∃ t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal),
      ((1 : ℝ) / 2) ^ (N + m) <
        |X (φ (N + m + 1)) t ω - X (φ (N + m)) t ω|} ≤
      ENNReal.ofReal (((1 : ℝ) / 2) ^ m) := by
  let k : ℕ := N + m
  let Δ : NNReal → Ω → ℝ := fun t ω ↦ X (φ (k + 1)) t ω - X (φ k) t ω
  let bad : Set Ω := {ω | ∃ t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal),
    ((1 : ℝ) / 2) ^ k < |Δ t ω|}
  let row : ℕ → Set Ω := fun n ↦
    {ω | ((1 : ℝ) / 2) ^ k ≤ integerDyadicGridAbsMax Δ N n ω}
  letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp.le
  have hΔ_cont : HasAlmostSurelyContinuousPaths μ Δ :=
    hasAlmostSurelyContinuousPaths_sub (hcont (φ (k + 1))) (hcont (φ k))
  have hbad_subset_rows :
      bad ≤ᵐ[μ] ⋃ n : ℕ, row n := by
    -- Proof comment: on every continuous sample path, a strict threshold crossing on the compact
    -- interval is already witnessed on some integer dyadic row.
    filter_upwards [hΔ_cont] with ω hωcont
    intro hω
    rcases continuousThresholdCrossing_exists_integerDyadicWitness hωcont hω with ⟨n, hn⟩
    exact Set.mem_iUnion.2 ⟨n, le_of_lt hn⟩
  have hrow_mono : Monotone row := by
    intro n n' hnn' ω hω
    induction hnn' with
    | refl =>
        exact hω
    | @step n' hnn' ih =>
        exact le_trans ih (integerDyadicGridAbsMax_mono Δ N n' ω)
  have hΔ_mart : Martingale Δ ℱ μ := by
    -- Proof comment: consecutive subsequence differences of martingales are still martingales.
    simpa [Δ] using (hX (φ (k + 1))).sub (hX (φ k))
  have hrow_bound :
      ∀ n : ℕ, μ (row n) ≤ ENNReal.ofReal (((1 : ℝ) / 2) ^ m) := by
    intro n
    have hthreshold_pos : 0 < ((1 : ℝ) / 2) ^ k := by
      exact pow_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) _
    have hε_nonneg : 0 ≤ ((1 : ℝ) / 2) ^ (2 * k) := by
      positivity
    have hbase :
        μ (row n) ≤
          ENNReal.ofReal (Real.rpow (((1 : ℝ) / 2) ^ (2 * k)) p) /
            ENNReal.ofReal (Real.rpow (((1 : ℝ) / 2) ^ k) p) := by
      simpa [row, k] using
        rowCrossingMeasure_le_of_eLpNormBound
          (ℱ := ℱ) (μ := μ) (p := p) hΔ_mart hp hthreshold_pos hε_nonneg
          (hsmall k N (Nat.le_add_right N m))
    have hratio :
        ENNReal.ofReal (Real.rpow (((1 : ℝ) / 2) ^ (2 * k)) p) /
            ENNReal.ofReal (Real.rpow (((1 : ℝ) / 2) ^ k) p) ≤
          ENNReal.ofReal (((1 : ℝ) / 2) ^ m) := by
      have hthreshold_pow_pos : 0 < Real.rpow (((1 : ℝ) / 2) ^ k) p := by
        exact Real.rpow_pos_of_pos (pow_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) _) p
      rw [← ENNReal.ofReal_div_of_pos hthreshold_pow_pos]
      apply ENNReal.ofReal_le_ofReal
      have hratio_eq :
          Real.rpow (((1 : ℝ) / 2) ^ (2 * k)) p / Real.rpow (((1 : ℝ) / 2) ^ k) p =
            Real.rpow (((1 : ℝ) / 2) ^ k) p := by
        have hsplit :
            (((1 : ℝ) / 2) ^ (2 * k)) = (((1 : ℝ) / 2) ^ k) * (((1 : ℝ) / 2) ^ k) := by
          rw [show 2 * k = k + k by ring, pow_add]
        have hmul :
            Real.rpow ((((1 : ℝ) / 2) ^ k) * (((1 : ℝ) / 2) ^ k)) p =
              Real.rpow (((1 : ℝ) / 2) ^ k) p * Real.rpow (((1 : ℝ) / 2) ^ k) p := by
          simpa using
            (Real.mul_rpow
              (show 0 ≤ (((1 : ℝ) / 2) ^ k) by positivity)
              (show 0 ≤ (((1 : ℝ) / 2) ^ k) by positivity) (z := p))
        rw [hsplit, hmul]
        field_simp [Real.rpow_pos_of_pos (pow_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) _) p]
      rw [hratio_eq]
      calc
        Real.rpow (((1 : ℝ) / 2) ^ k) p = ((1 : ℝ) / 2) ^ ((k : ℝ) * p) := by
          simpa [mul_comm] using
            (Real.rpow_natCast_mul (show 0 ≤ (1 : ℝ) / 2 by norm_num) k p).symm
        _ ≤ ((1 : ℝ) / 2) ^ (m : ℝ) := by
          have hm_le_k : (m : ℝ) ≤ k := by
            exact_mod_cast Nat.le_add_left m N
          have hk_mul : (m : ℝ) ≤ (k : ℝ) * p := by
            nlinarith [hp, hm_le_k]
          exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hk_mul
        _ = (((1 : ℝ) / 2) ^ m) := by rw [Real.rpow_natCast]
    exact hbase.trans hratio
  have hmeasure_union :
      μ (⋃ n : ℕ, row n) = ⨆ n : ℕ, μ (row n) := by
    rw [hrow_mono.measure_iUnion]
  calc
    μ bad ≤ μ (⋃ n : ℕ, row n) := measure_mono_ae hbad_subset_rows
    _ = ⨆ n : ℕ, μ (row n) := hmeasure_union
    _ ≤ ENNReal.ofReal (((1 : ℝ) / 2) ^ m) := by
      exact iSup_le hrow_bound
/-- Helper for Exercise 21.4.3: the geometric compact bad-event bounds imply almost-sure eventual
compact control of the subsequence increments. -/
private lemma aeEventually_smallCompactTailIncrements
    (hX : ∀ n : ℕ, Martingale (X n) ℱ μ)
    (hcont : ∀ n : ℕ, HasAlmostSurelyContinuousPaths μ (X n))
    (hp : 1 < p)
    {φ : ℕ → ℕ}
    (hsmall :
      ∀ k N : ℕ, N ≤ k →
        eLpNorm (X (φ (k + 1)) (N + 1) - X (φ k) (N + 1)) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (((1 : ℝ) / 2) ^ (2 * k)))
    (N : ℕ) :
    ∀ᵐ ω ∂μ,
      ∀ᶠ m in atTop,
        ∀ t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal),
          |X (φ (N + m + 1)) t ω - X (φ (N + m)) t ω| ≤ ((1 : ℝ) / 2) ^ (N + m) := by
  let bad : ℕ → Set Ω := fun m ↦
    {ω | ∃ t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal),
      ((1 : ℝ) / 2) ^ (N + m) <
        |X (φ (N + m + 1)) t ω - X (φ (N + m)) t ω|}
  have hbad :
      ∀ m : ℕ, μ (bad m) ≤ ENNReal.ofReal (((1 : ℝ) / 2) ^ m) := by
    intro m
    simpa [bad] using
      compactTailBadEvent_measure_le_geometric
        (ℱ := ℱ) (μ := μ) (X := X) (p := p) hX hcont hp hsmall N m
  filter_upwards [ae_eventually_notMem_of_geometric_half_bound hbad] with ω hω
  filter_upwards [hω] with m hm
  intro t ht
  by_contra hlt
  exact hm ⟨t, ht, lt_of_not_ge hlt⟩

omit mΩ in
/-- Helper for Exercise 21.4.3: for a fixed sample point and integer horizon, eventual geometric
compact-tail bounds turn the pathwise limsup of the subsequence into a continuous compact-interval
limit, and the whole subsequence converges to that limit on the same interval. -/
private lemma compactLimsupAssemblyOnInterval
    {φ : ℕ → ℕ} (ω : Ω) (N : ℕ)
    (hpath : ∀ k : ℕ, Continuous (processPath (X (φ k)) ω))
    (htail :
      ∀ᶠ m in atTop,
        ∀ t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal),
          |X (φ (N + m + 1)) t ω - X (φ (N + m)) t ω| ≤ ((1 : ℝ) / 2) ^ (N + m)) :
    ContinuousOn (fun t ↦ limsup (fun k ↦ X (φ k) t ω) atTop)
        (Set.Icc (0 : NNReal) (N + 1 : NNReal)) ∧
      ∀ t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal),
        Tendsto (fun k ↦ X (φ k) t ω) atTop
          (nhds (limsup (fun k ↦ X (φ k) t ω) atTop)) := by
  rcases Filter.eventually_atTop.1 htail with ⟨K, hK⟩
  let s : ℕ := N + K
  let f : ℕ → NNReal → ℝ := fun m t ↦ X (φ (m + s)) t ω
  have hsummable :
      Summable (fun m : ℕ ↦ ((1 : ℝ) / 2) ^ (m + s)) := by
    -- Proof comment: reuse the dedicated shifted-geometric helper for the compact tail bound.
    simpa [s] using summable_halfPow_natAdd s
  have hf_cont : ∀ m : ℕ, Continuous (f m) := by
    intro m
    -- Proof comment: each shifted term is one of the already continuous subsequence paths.
    simpa [f, s, processPath, Nat.add_comm] using hpath (m + s)
  have hf_bound :
      ∀ m : ℕ, ∀ t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal),
        ‖f (m + 1) t - f m t‖ ≤ ((1 : ℝ) / 2) ^ (m + s) := by
    intro m t ht
    -- Proof comment: the eventual compact-tail estimate becomes a uniform bound for the shifted
    -- tail after fixing one explicit starting index `K`.
    simpa [f, s, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Real.norm_eq_abs] using
      hK (K + m) (Nat.le_add_right K m) t ht
  rcases continuousOn_and_limsup_eq_of_summableCompactIncrementBounds
      (u := fun m : ℕ ↦ ((1 : ℝ) / 2) ^ (m + s))
      hsummable (f := f) (N := (N + 1 : NNReal)) hf_cont hf_bound with
    ⟨g, hg_cont, hg_tendsto, hg_limsup⟩
  have hEqOn :
      Set.EqOn
        (fun t ↦ limsup (fun k ↦ X (φ k) t ω) atTop)
        g
        (Set.Icc (0 : NNReal) (N + 1 : NNReal)) := by
    intro t ht
    -- Proof comment: the compact-interval limit from the shifted tail is the same as the global
    -- limsup because removing finitely many initial terms does not change `limsup`.
    have hshift :
        limsup (fun m ↦ f m t) atTop = limsup (fun k ↦ X (φ k) t ω) atTop := by
      simpa [f, s, Nat.add_comm] using
        (Filter.limsup_nat_add (fun k ↦ X (φ k) t ω) s)
    exact hshift.symm.trans (hg_limsup t ht)
  refine ⟨hg_cont.congr hEqOn, ?_⟩
  intro t ht
  -- Proof comment: shifted-tail convergence gives full-subsequence convergence after one use of
  -- `tendsto_add_atTop_iff_nat`.
  have hEqAt :
      limsup (fun k ↦ X (φ k) t ω) atTop = g t :=
    hEqOn ht
  have hshifted :
      Tendsto (fun m ↦ X (φ (m + s)) t ω) atTop
        (nhds (limsup (fun k ↦ X (φ k) t ω) atTop)) := by
    simpa [f, s, hEqAt, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hg_tendsto t ht
  exact (Filter.tendsto_add_atTop_iff_nat s).1 hshifted

omit [IsProbabilityMeasure μ] in
/-- Helper for Exercise 21.4.3: one full-measure event carries the compact-interval continuity and
pointwise convergence statements for the limsup candidate on every integer horizon. -/
private lemma aeAllCompactLimsupAssembly
    {φ : ℕ → ℕ}
    (hcont : ∀ n : ℕ, HasAlmostSurelyContinuousPaths μ (X n))
    (hcompact_tail :
      ∀ N : ℕ,
        ∀ᵐ ω ∂μ,
          ∀ᶠ m in atTop,
            ∀ t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal),
              |X (φ (N + m + 1)) t ω - X (φ (N + m)) t ω| ≤ ((1 : ℝ) / 2) ^ (N + m)) :
    ∀ᵐ ω ∂μ,
      ∀ N : ℕ,
        ContinuousOn (fun t ↦ limsup (fun k ↦ X (φ k) t ω) atTop)
            (Set.Icc (0 : NNReal) (N + 1 : NNReal)) ∧
          ∀ t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal),
            Tendsto (fun k ↦ X (φ k) t ω) atTop
              (nhds (limsup (fun k ↦ X (φ k) t ω) atTop)) := by
  have hpaths :
      ∀ᵐ ω ∂μ, ∀ k : ℕ, Continuous (processPath (X (φ k)) ω) :=
    ae_all_continuous_subsequence_paths (μ := μ) (X := X) hcont φ
  have htails :
      ∀ᵐ ω ∂μ,
        ∀ N : ℕ,
          ∀ᶠ m in atTop,
            ∀ t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal),
              |X (φ (N + m + 1)) t ω - X (φ (N + m)) t ω| ≤ ((1 : ℝ) / 2) ^ (N + m) :=
    ae_all_iff.2 hcompact_tail
  filter_upwards [hpaths, htails] with ω hω_paths hω_tails
  intro N
  -- Proof comment: the fixed-ω assembly lemma is applied on the common full-measure event where
  -- every subsequence path is continuous and every integer horizon has eventual compact control.
  exact compactLimsupAssemblyOnInterval (X := X) (ω := ω) (N := N) hω_paths (hω_tails N)

/-- Helper for Exercise 21.4.3: continuity on every interval `[(0 : NNReal), N + 1]` gives a
globally continuous path on `NNReal`. -/
private lemma continuous_of_continuousOnIntegerIntervals
    {β : Type*} [TopologicalSpace β] {f : NNReal → β}
    (hcont : ∀ N : ℕ, ContinuousOn f (Set.Icc (0 : NNReal) (N + 1 : NNReal))) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 ?_
  intro t
  by_cases ht0 : t = 0
  · subst ht0
    have hmem : Set.Icc (0 : NNReal) ((0 : ℕ) + 1 : NNReal) ∈ nhds (0 : NNReal) := by
      refine mem_of_superset (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num)) ?_
      intro x hx
      have hx' : x < ((0 : ℕ) + 1 : NNReal) := by
        simpa using hx
      exact Set.mem_Icc.mpr ⟨zero_le x, le_of_lt hx'⟩
    exact (hcont 0).continuousAt hmem
  rcases exists_nat_gt (t : ℝ) with ⟨N, hN⟩
  have ht_lower : (0 : NNReal) < t := bot_lt_iff_ne_bot.mpr ht0
  have ht_upper_nat : t < (N : NNReal) := by
    exact_mod_cast hN
  have ht_upper : t < (N + 1 : NNReal) := by
    exact lt_of_lt_of_le ht_upper_nat (by exact_mod_cast Nat.le_succ N)
  have hmem : Set.Icc (0 : NNReal) (N + 1 : NNReal) ∈ nhds t :=
    Icc_mem_nhds ht_lower ht_upper
  exact (hcont N).continuousAt hmem

/-- Helper for Exercise 21.4.3: a Doob/Borel--Cantelli subsequence can be chosen so that its
pointwise `limsup` is an almost surely continuous compact-uniform limit on every bounded time
interval. -/
lemma exists_continuous_limsupSubsequence
    (hX : ∀ n : ℕ, Martingale (X n) ℱ μ)
    (hcont : ∀ n : ℕ, HasAlmostSurelyContinuousPaths μ (X n))
    (hp : 1 < p)
    (hlimit :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp.le
        ∃ h_memLpSeq : ∀ n, MemLp (X n t) (ENNReal.ofReal p) μ,
          Tendsto (fun n ↦ (h_memLpSeq n).toLp (X n t)) atTop (nhds (Xtilde t))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Xc : NNReal → Ω → ℝ,
        Xc = (fun t ω ↦ limsup (fun k ↦ X (φ k) t ω) atTop) ∧
          HasAlmostSurelyContinuousPaths μ Xc ∧
          (∀ t : NNReal,
            ∀ᵐ ω ∂μ, Tendsto (fun k ↦ X (φ k) t ω) atTop (nhds (Xc t ω))) := by
  rcases martingale_of_timewise_lp_limit hX hp.le hlimit with ⟨Y, -, hY_repr⟩
  have hY_tendsto :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp.le
        TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Y t) := by
    intro t
    exact tendstoInLp_partOneRepresentative hp.le hlimit hY_repr t
  rcases existsStrictMonoSubsequence_smallEarlierIntegerHorizons
      (μ := μ) (X := X) (p := p) hp hY_tendsto with ⟨φ, hφ, hφ_small⟩
  let Xc : NNReal → Ω → ℝ := fun t ω ↦ limsup (fun k ↦ X (φ k) t ω) atTop
  have hcompact_tail :
      ∀ N : ℕ,
        ∀ᵐ ω ∂μ,
          ∀ᶠ m in atTop,
            ∀ t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal),
              |X (φ (N + m + 1)) t ω - X (φ (N + m)) t ω| ≤
                ((1 : ℝ) / 2) ^ (N + m) := by
    -- Proof comment: the new diagonal subsequence together with the dyadic Doob/Borel--Cantelli
    -- helpers reduces the remaining theorem to a pointwise compact-interval assembly argument.
    intro N
    exact
      aeEventually_smallCompactTailIncrements
        (ℱ := ℱ) (μ := μ) (X := X) (p := p) hX hcont hp hφ_small N
  have hassembled :
      ∀ᵐ ω ∂μ,
        ∀ N : ℕ,
          ContinuousOn (fun t ↦ Xc t ω) (Set.Icc (0 : NNReal) (N + 1 : NNReal)) ∧
            ∀ t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal),
              Tendsto (fun k ↦ X (φ k) t ω) atTop (nhds (Xc t ω)) := by
    -- Proof comment: intersect the countable pathwise continuity event with the countable family
    -- of compact-tail bounds, then assemble each compact interval separately.
    simpa [Xc] using
      aeAllCompactLimsupAssembly (μ := μ) (X := X) (hcont := hcont) (φ := φ) hcompact_tail
  refine ⟨φ, hφ, Xc, rfl, ?_, ?_⟩
  · -- Proof comment: continuity on every interval `[0, N + 1]` upgrades to a globally continuous
    -- sample path on `NNReal`.
    filter_upwards [hassembled] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath, Xc] using
      (continuous_of_continuousOnIntegerIntervals
        (f := processPath Xc ω) (fun N ↦ by simpa [processPath] using (hω N).1))
  · intro t
    rcases exists_nat_gt (t : ℝ) with ⟨N, hN⟩
    have ht_mem : t ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal) := by
      have ht_lt : t < (N : NNReal) := by
        exact_mod_cast hN
      refine Set.mem_Icc.mpr ⟨zero_le t, ?_⟩
      exact le_of_lt (lt_of_lt_of_le ht_lt (by exact_mod_cast Nat.le_succ N))
    -- Proof comment: a deterministic time belongs to some integer interval `[0, N + 1]`, so the
    -- compact-interval convergence statement applies there.
    filter_upwards [hassembled] with ω hω
    exact (hω N).2 t ht_mem

-- Proof sketch: part (1) first produces a single representative martingale for the given
-- timewise `L^p` limit classes.
-- For each time horizon `T`, Doob's `L^p` maximal inequality upgrades the owner timewise `L^p`
-- convergence of `Xⁿ - Xᵐ` to convergence of the path suprema on `[0,T]`, so a subsequence
-- converges uniformly almost surely on every compact interval. The limit defines a process with
-- almost surely continuous paths, still represents the given `L^p` classes `X̃_t`, and still
-- receives the same timewise `TendstoInLp` limit.
/-- Exercise 21.4.3 (2): if `p > 1` and every approximating martingale has almost surely
continuous paths, then the timewise `L^p` limit classes `X̃_t` admit a continuous martingale
representative `Xc`; moreover the approximants still converge to `Xc` in `L^p` at each
deterministic time. -/
theorem exists_continuous_martingale_modification_of_timewise_lp_limit
    (hX : ∀ n : ℕ, Martingale (X n) ℱ μ)
    (hcont : ∀ n : ℕ, HasAlmostSurelyContinuousPaths μ (X n))
    (hp : 1 < p)
    (hlimit :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp.le
        ∃ h_memLpSeq : ∀ n, MemLp (X n t) (ENNReal.ofReal p) μ,
          Tendsto (fun n ↦ (h_memLpSeq n).toLp (X n t)) atTop (nhds (Xtilde t))) :
    ∃ Xc : NNReal → Ω → ℝ,
      Martingale Xc ℱ μ ∧
        HasAlmostSurelyContinuousPaths μ Xc ∧
        (∀ t : NNReal,
          ∃ h_memLp : MemLp (Xc t) (ENNReal.ofReal p) μ,
            h_memLp.toLp (Xc t) = Xtilde t) ∧
        (∀ t : NNReal,
          letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp.le
          TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Xc t)) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp.le
  rcases martingale_of_timewise_lp_limit hX hp.le hlimit with ⟨Y, hY_mart, hY_repr⟩
  -- Route correction: instead of reconstructing adaptedness after taking a pathwise limit, define
  -- the candidate continuous version directly as the measurable `limsup` of a subsequence.
  rcases exists_continuous_limsupSubsequence hX hcont hp hlimit with
    ⟨φ, hφ, Xc, hXc_def, hXc_cont, hXc_tendsto⟩
  have hXc_stronglyAdapted : StronglyAdapted ℱ Xc := by
    -- Proof comment: the defining `limsup` formula makes each deterministic-time slice measurable
    -- with respect to the corresponding filtration sigma-algebra.
    simpa [hXc_def] using stronglyAdapted_limsupSubsequence hX φ
  have hXc_eq_Y : ∀ t : NNReal, Xc t =ᵐ[μ] Y t := by
    -- Proof comment: fixed-time almost-everywhere convergence of the subsequence identifies the
    -- `limsup` candidate with the part-(1) martingale representative.
    exact
      aeEq_partOneRepresentative_of_ae_tendsto_subsequence
        hX hp.le hlimit hY_repr hφ hXc_tendsto
  have hXc_martingale : Martingale Xc ℱ μ :=
    martingale_congr_ae hY_mart hXc_stronglyAdapted (fun t ↦ (hXc_eq_Y t).symm)
  have hXc_repr :
      ∀ t : NNReal,
        ∃ h_memLp : MemLp (Xc t) (ENNReal.ofReal p) μ,
          h_memLp.toLp (Xc t) = Xtilde t := by
    intro t
    rcases hY_repr t with ⟨hY_memLp, hY_toLp⟩
    have hXc_memLp : MemLp (Xc t) (ENNReal.ofReal p) μ :=
      (memLp_congr_ae (hXc_eq_Y t)).2 hY_memLp
    refine ⟨hXc_memLp, ?_⟩
    -- Proof comment: the fixed-time `L^p` class of `Xc` is the same as the already identified
    -- class of `Y`.
    exact (MemLp.toLp_congr hXc_memLp hY_memLp (hXc_eq_Y t)).trans hY_toLp
  refine ⟨Xc, hXc_martingale, hXc_cont, hXc_repr, ?_⟩
  intro t
  rcases hXc_repr t with ⟨hXc_memLp, -⟩
  have hY_tendsto :
      TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Y t) :=
    tendstoInLp_partOneRepresentative hp.le hlimit hY_repr t
  refine (tendstoInLp_iff_tendsto_eLpNorm).2 ?_
  refine ⟨hY_tendsto.memLpSeq, hXc_memLp, ?_⟩
  have hnormEq :
      (fun n ↦ eLpNorm (X n t - Xc t) (ENNReal.ofReal p) μ) =
        fun n ↦ eLpNorm (X n t - Y t) (ENNReal.ofReal p) μ := by
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [hXc_eq_Y t] with ω hω
    simp [hω]
  -- Proof comment: after rewriting the target through the fixed-time almost-everywhere
  -- identification `Xc t = Y t`, the original timewise `L^p` convergence statement closes.
  rw [hnormEq]
  exact hY_tendsto.tendsto_eLpNorm

end TimewiseLpLimit

end ProbabilityTheory
