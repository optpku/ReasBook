/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory unitInterval
open scoped ProbabilityTheory Topology unitInterval

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- With Lean's `0`-based indexing, the textbook Bernoulli parameters `1 / n` are represented by
`1 / (n + 1)`. -/
noncomputable def harmonicBernoulliParameter (n : ℕ) : I :=
  ⟨(1 : ℝ) / (n + 1), div_mem zero_le_one (by positivity) <| by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)⟩

/-- Helper for Remark 6.6: a subset of `Set.Iio 1` is either empty or `{0}`. -/
lemma eq_empty_or_singleton_zero_of_subset_Iio_one {s : Set ℕ} (hs : s ⊆ Set.Iio 1) :
    s = ∅ ∨ s = ({0} : Set ℕ) := by
  -- A subset of `{n | n < 1}` can only contain the unique natural number `0`.
  have hs0 : s ⊆ ({0} : Set ℕ) := by
    intro k hk
    have hk0 : k = 0 := by
      have hk1 : k < 1 := hs hk
      omega
    simpa [hk0]
  by_cases h0 : 0 ∈ s
  · right
    ext k
    constructor
    · intro hk
      exact hs0 hk
    · intro hk
      simpa using hk ▸ h0
  · left
    ext k
    constructor
    · intro hk
      have hk1 : k < 1 := hs hk
      have hk0 : k = 0 := by omega
      exact (h0 <| hk0 ▸ hk).elim
    · intro hk
      simp at hk

/-- Helper for Remark 6.6: a one-trial binomial random variable is almost surely `0` or `1`. -/
lemma ae_eq_zero_or_one_of_hasLaw_binomialOne
    {P : Measure Ω} {Y : Ω → ℝ} {n : ℕ}
    (hY : HasLaw Y (Bin(ℝ, 1, harmonicBernoulliParameter n)) P) :
    ∀ᵐ ω ∂P, Y ω = 0 ∨ Y ω = 1 := by
  have hModel : ∀ᵐ x ∂Bin(ℝ, 1, harmonicBernoulliParameter n), x = 0 ∨ x = 1 := by
    -- Push the support statement back to the explicit set-Bernoulli model of `Bin(ℝ, 1, p)`.
    rw [ProbabilityTheory.binomial]
    rw [MeasureTheory.ae_map_iff
      ((measurable_from_nat : Measurable (fun k : ℕ ↦ (k : ℝ))).aemeasurable)]
    · rw [MeasureTheory.ae_map_iff measurable_ncard.aemeasurable]
      · filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := Set.Iio 1)
          (p := harmonicBernoulliParameter n)] with s hs
        rcases eq_empty_or_singleton_zero_of_subset_Iio_one hs with rfl | rfl <;> simp
      · exact measurableSet_setOf.2 <| by fun_prop
    · exact measurableSet_setOf.2 <| by fun_prop
  -- Transport the model support statement back through the law of `Y`.
  exact (hY.ae_iff (p := fun x => x = 0 ∨ x = 1) (by fun_prop)).2 hModel

/-- Helper for Remark 6.6: the natural-valued one-trial binomial law assigns mass `p` to
`{1}`. -/
lemma binomialOne_apply_singleton_one (p : I) :
    Bin(1, p) ({1} : Set ℕ) = ENNReal.ofReal (p : ℝ) := by
  -- Proof comment: unfold the one-trial binomial law to the `setBer(Set.Iio 1, p)` model.
  rw [ProbabilityTheory.binomial, Measure.map_apply measurable_ncard (measurableSet_singleton 1)]
  have hEvent :
      Set.ncard ⁻¹' ({1} : Set ℕ) =ᵐ[setBer(Set.Iio 1, p)]
        ({({0} : Set ℕ)} : Set (Set ℕ)) := by
    -- Proof comment: inside `Set.Iio 1`, cardinality `1` forces the unique singleton `{0}`.
    filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := Set.Iio 1) (p := p)] with s hs
    rcases eq_empty_or_singleton_zero_of_subset_Iio_one hs with rfl | rfl
    · apply propext
      constructor
      · intro h
        change Set.ncard (∅ : Set ℕ) = 1 at h
        simp at h
      · intro h
        change (∅ : Set ℕ) = ({0} : Set ℕ) at h
        simp at h
    · apply propext
      constructor
      · intro h
        trivial
      · intro h
        change Set.ncard ({0} : Set ℕ) = 1
        simp
  rw [measure_congr hEvent]
  calc
    setBer(Set.Iio 1, p) ({({0} : Set ℕ)} : Set (Set ℕ))
        = toNNReal p ^ ({0} : Set ℕ).ncard
            * toNNReal (σ p) ^ (Set.Iio 1 \ ({0} : Set ℕ)).ncard := by
              simpa using
                (ProbabilityTheory.setBernoulli_singleton (u := Set.Iio 1)
                  (p := p) (s := ({0} : Set ℕ)) (by simp) (Set.toFinite _))
    _ = (toNNReal p : ENNReal) := by
      simp
    _ = ENNReal.ofReal (p : ℝ) := by
      simpa using (ENNReal.ofReal_eq_coe_nnreal p.2.1).symm

/-- Helper for Remark 6.6: the success event of a one-trial binomial random variable has
probability `1 / (n + 1)`. -/
lemma measure_preimage_one_of_hasLaw_binomialOne
    {P : Measure Ω} {Y : Ω → ℝ} {n : ℕ}
    (hY : HasLaw Y (Bin(ℝ, 1, harmonicBernoulliParameter n)) P) :
    P {ω | Y ω = 1} = ENNReal.ofReal ((1 : ℝ) / (n + 1)) := by
  -- Route correction: compute the singleton mass on the nat-valued binomial law first, then
  -- transport it through the `Nat.cast` pushforward and the law of `Y`.
  have hBin :
      Bin(ℝ, 1, harmonicBernoulliParameter n) ({1} : Set ℝ) =
        ENNReal.ofReal ((1 : ℝ) / (n + 1)) := by
    -- Proof comment: peel off the outer real-valued pushforward before using the nat-level bridge.
    rw [ProbabilityTheory.binomial, Measure.map_apply
      (measurable_from_nat : Measurable (fun k : ℕ ↦ (k : ℝ))) (measurableSet_singleton 1)]
    have hPreimage :
        (fun k : ℕ ↦ (k : ℝ)) ⁻¹' ({1} : Set ℝ) = ({1} : Set ℕ) := by
      ext k
      simp
    rw [hPreimage]
    calc
      Bin(1, harmonicBernoulliParameter n) ({1} : Set ℕ)
          = ENNReal.ofReal (harmonicBernoulliParameter n : ℝ) := by
            simpa using binomialOne_apply_singleton_one (harmonicBernoulliParameter n)
      _ = ENNReal.ofReal ((1 : ℝ) / (n + 1)) := by simp [harmonicBernoulliParameter]
  -- Proof comment: rewrite the success event as the singleton mass of the pushforward law.
  calc
    P {ω | Y ω = 1} = P.map Y ({1} : Set ℝ) := by
      simpa [Set.preimage, Set.mem_setOf_eq] using
        (Measure.map_apply_of_aemeasurable hY.aemeasurable (measurableSet_singleton 1)).symm
    _ = Bin(ℝ, 1, harmonicBernoulliParameter n) ({1} : Set ℝ) := by rw [hY.map_eq]
    _ = ENNReal.ofReal ((1 : ℝ) / (n + 1)) := hBin

/-- Helper for Remark 6.6: measurable singleton preimages of an independent family form an
independent family of events. -/
lemma iIndepSet_preimage_singleton_of_iIndepFun
    {P : Measure Ω} {Y : ℕ → Ω → ℝ} (hYm : ∀ n, Measurable (Y n)) (c : ℝ)
    (hY : iIndepFun Y P) :
    iIndepSet (fun n ↦ {ω | Y n ω = c}) P := by
  -- Rewrite `iIndepSet` using the finite-intersection criterion and then apply the preimage form
  -- of `iIndepFun`.
  rw [ProbabilityTheory.iIndepSet_iff_meas_biInter]
  · intro s
    simpa [Set.setOf_eq_eq_singleton] using
      hY.measure_inter_preimage_eq_mul s (sets := fun _ ↦ ({c} : Set ℝ))
        (by intro i hi; exact measurableSet_singleton c)
  · intro n
    exact (hYm n) (measurableSet_singleton c)

/-- Helper for Remark 6.6: a real sequence bounded above by `1` and frequently equal to `1`
has limsup equal to `1`. -/
lemma limsup_eq_one_of_frequently_eq_one_of_forall_le_one {x : ℕ → ℝ}
    (hx_le : ∀ n, x n ≤ 1) (hfreq : ∃ᶠ n in atTop, x n = 1) :
    limsup x atTop = 1 := by
  -- Route correction: the closing step only needs an upper bound by `1` and frequent hits of `1`.
  have hfreq_le : ∃ᶠ n in atTop, 1 ≤ x n := by
    exact hfreq.mono fun _ hn => by simpa [hn]
  have hCobdd : IsCoboundedUnder (· ≤ ·) atTop x := by
    exact IsCoboundedUnder.of_frequently_ge hfreq_le
  have hBdd : IsBoundedUnder (· ≤ ·) atTop x := by
    exact isBoundedUnder_of_eventually_le (Eventually.of_forall hx_le)
  -- Proof comment: frequent equality to `1` gives the lower bound, while `x n ≤ 1` gives the
  -- upper bound on every tail.
  exact le_antisymm
    (Filter.limsup_le_of_le hCobdd (Eventually.of_forall hx_le))
    (Filter.le_limsup_of_frequently_le hfreq_le hBdd)

-- Proof sketch: for convergence in measure, rewrite the deviation event
-- `{ω | ε ≤ |X n ω|}` using the `{0,1}`-valued Bernoulli law of `X n`, so its probability is
-- either `(n + 1)⁻¹` or `0` and therefore tends to `0`. For the almost-sure `limsup`, apply the
-- second Borel--Cantelli lemma to the events `{ω | X n ω = 1}`, whose probabilities form the
-- harmonic series.
/-- Remark 6.6: with Lean's `0`-based indexing, the textbook laws `\mathrm{Ber}_{1 / n}` are
formalized as the one-trial binomial laws `Bin(ℝ, 1, harmonicBernoulliParameter n)`. If
`(Xₙ)` is an independent sequence with these laws, then `Xₙ` converges in probability to `0`,
but `limsup_{n → ∞} Xₙ = 1` almost surely. Hence convergence in measure does not imply
almost-everywhere convergence. -/
theorem harmonicBernoulli_tendstoInMeasure_zero_and_ae_limsup_eq_one
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (h_indep : iIndepFun X P)
    (h_law : ∀ n, HasLaw (X n) (Bin(ℝ, 1, harmonicBernoulliParameter n)) P) :
    TendstoInMeasure P X atTop (fun _ ↦ (0 : ℝ)) ∧
      ∀ᵐ ω ∂P, limsup (fun n ↦ X n ω) atTop = 1 := by
  let Y : ℕ → Ω → ℝ := fun n ↦ (h_law n).aemeasurable.mk (X n)
  have hY_meas : ∀ n, Measurable (Y n) := by
    intro n
    exact (h_law n).aemeasurable.measurable_mk
  have hY_ae : ∀ n, Y n =ᵐ[P] X n := by
    intro n
    exact (h_law n).aemeasurable.ae_eq_mk.symm
  have hY_indep : iIndepFun Y P := by
    -- Proof comment: independence is stable under coordinatewise a.e. replacement.
    exact h_indep.congr fun n ↦ (hY_ae n).symm
  have hY_law : ∀ n, HasLaw (Y n) (Bin(ℝ, 1, harmonicBernoulliParameter n)) P := by
    intro n
    exact (h_law n).congr (hY_ae n)
  have hY_support : ∀ n, ∀ᵐ ω ∂P, Y n ω = 0 ∨ Y n ω = 1 := by
    intro n
    exact ae_eq_zero_or_one_of_hasLaw_binomialOne (hY_law n)
  have hY_tendsto : TendstoInMeasure P Y atTop (fun _ ↦ (0 : ℝ)) := by
    -- Proof comment: the deviation event is either the success event `{Y n = 1}` or the empty
    -- set, depending on whether `ε ≤ 1`.
    rw [MeasureTheory.tendstoInMeasure_iff_measureReal_norm]
    simp only [sub_zero]
    intro ε hε
    by_cases hε1 : ε ≤ 1
    · have hProb :
          (fun n : ℕ ↦ P.real {ω | ε ≤ ‖Y n ω‖}) = fun n : ℕ ↦ (1 : ℝ) / (n + 1) := by
        funext n
        have hEvent :
            {ω | ε ≤ ‖Y n ω‖} =ᵐ[P] {ω | Y n ω = 1} := by
          filter_upwards [hY_support n] with ω hω
          rcases hω with h0 | h1
          · apply propext
            have hEq : ε ≤ ‖Y n ω‖ ↔ Y n ω = 1 := by
              rw [h0]
              constructor
              · intro h
                have hFalse : ¬ ε ≤ ‖(0 : ℝ)‖ := by
                  simpa using (not_le_of_gt hε)
                exact (hFalse h).elim
              · intro h
                have hFalse : (0 : ℝ) = 1 := by simpa [h0] using h
                norm_num at hFalse
            simpa using hEq
          · apply propext
            have hEq : ε ≤ ‖Y n ω‖ ↔ Y n ω = 1 := by
              rw [h1]
              constructor
              · intro h
                simp
              · intro h
                simpa using hε1
            simpa using hEq
        rw [measureReal_def, measure_congr hEvent,
          measure_preimage_one_of_hasLaw_binomialOne (hY := hY_law n)]
        exact ENNReal.toReal_ofReal (by positivity)
      rw [hProb]
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
        (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (𝓝 0))
    · have hε_gt : 1 < ε := lt_of_not_ge hε1
      have hProb :
          (fun n : ℕ ↦ P.real {ω | ε ≤ ‖Y n ω‖}) = fun _ : ℕ ↦ 0 := by
        funext n
        have hEvent : {ω | ε ≤ ‖Y n ω‖} =ᵐ[P] (∅ : Set Ω) := by
          have hnot : ¬ ε ≤ (1 : ℝ) := not_le.mpr hε_gt
          filter_upwards [hY_support n] with ω hω
          rcases hω with h0 | h1
          · apply propext
            constructor
            · intro h
              have hFalse : ¬ ε ≤ ‖(0 : ℝ)‖ := by
                simpa using (not_le_of_gt hε)
              change ε ≤ ‖Y n ω‖ at h
              exact (hFalse (by simpa [h0] using h)).elim
            · intro h
              have hFalse : False := by simpa using h
              exact hFalse.elim
          · apply propext
            constructor
            · intro h
              change ε ≤ ‖Y n ω‖ at h
              exact (hnot (by simpa [h1] using h)).elim
            · intro h
              have hFalse : False := by simpa using h
              exact hFalse.elim
        rw [measureReal_def, measure_congr hEvent]
        simp
      rw [hProb]
      exact tendsto_const_nhds
  let s : ℕ → Set Ω := fun n ↦ {ω | Y n ω = 1}
  have hs_meas : ∀ n, MeasurableSet (s n) := by
    intro n
    exact (hY_meas n) (measurableSet_singleton 1)
  have hs_indep : iIndepSet s P := by
    -- Proof comment: singleton preimages inherit independence from the measurable family `Y`.
    simpa [s] using iIndepSet_preimage_singleton_of_iIndepFun (hYm := hY_meas) (c := 1) hY_indep
  have hs_series : (∑' n : ℕ, P (s n)) = ⊤ := by
    have hPartial :
        Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.range N, P (s k)) atTop (𝓝 (⊤ : ENNReal)) := by
      have hReal :
          Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.range N, (1 : ℝ) / (k + 1)) atTop atTop :=
        Real.tendsto_sum_range_one_div_nat_succ_atTop
      have hOfReal :
          Tendsto
            (fun N : ℕ ↦ ENNReal.ofReal (∑ k ∈ Finset.range N, (1 : ℝ) / (k + 1)))
            atTop (𝓝 (⊤ : ENNReal)) :=
        ENNReal.tendsto_ofReal_nhds_top.2 hReal
      refine hOfReal.congr' <| Eventually.of_forall fun N ↦ ?_
      rw [ENNReal.ofReal_sum_of_nonneg]
      · refine Finset.sum_congr rfl fun k hk ↦ ?_
        simpa [s] using (measure_preimage_one_of_hasLaw_binomialOne (hY := hY_law k)).symm
      · intro k hk
        positivity
    have htsum : (⊤ : ENNReal) = ∑' n : ℕ, P (s n) :=
      tendsto_nhds_unique hPartial (ENNReal.tendsto_nat_tsum fun n ↦ P (s n))
    simpa using htsum.symm
  have hs_limsup_ae : ∀ᵐ ω ∂P, ω ∈ limsup s atTop := by
    -- Proof comment: the divergent harmonic series and independence trigger Borel-Cantelli.
    exact
      (MeasureTheory.mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hs_meas)).2
        (ProbabilityTheory.measure_limsup_eq_one (μ := P) (s := s) hs_meas hs_indep hs_series)
  have hY_support_all : ∀ᵐ ω ∂P, ∀ n, Y n ω = 0 ∨ Y n ω = 1 := by
    rw [ae_all_iff]
    intro n
    exact hY_support n
  have hY_limsup_ae : ∀ᵐ ω ∂P, limsup (fun n ↦ Y n ω) atTop = 1 := by
    -- Proof comment: on the full-measure `{0,1}` support, limsup `1` is exactly frequent equality
    -- to `1`.
    filter_upwards [hs_limsup_ae, hY_support_all] with ω hω_limsup hω_support
    have hfreqY : ∃ᶠ n in atTop, Y n ω = 1 := by
      simpa [s, Filter.mem_limsup_iff_frequently_mem] using hω_limsup
    have hY_le : ∀ n, Y n ω ≤ 1 := by
      intro n
      rcases hω_support n with h0 | h1
      · simp [h0]
      · simp [h1]
    exact limsup_eq_one_of_frequently_eq_one_of_forall_le_one hY_le hfreqY
  have hY_eq_all : ∀ᵐ ω ∂P, ∀ n, Y n ω = X n ω := by
    rw [ae_all_iff]
    intro n
    exact hY_ae n
  refine ⟨hY_tendsto.congr (fun n ↦ hY_ae n) EventuallyEq.rfl, ?_⟩
  filter_upwards [hY_limsup_ae, hY_eq_all] with ω hω_limsup hω_eq
  have hSeq : (fun n ↦ Y n ω) = fun n ↦ X n ω := funext hω_eq
  simpa [hSeq] using hω_limsup
