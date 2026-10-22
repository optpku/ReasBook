/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_40

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ENNReal

local notation "S" => petersburgPartialSum
local notation "μ" => fairBernoulliMeasure
local notation "ℱ" => petersburgPayoffFiltration

/- Example 11.6 is `source-facing`: it records the almost-sure convergence of the Petersburg gain
process to `1`, its failure to converge in `L¹`, and the resulting failure of uniform
integrability. The `core/canonical` owner layer is split between the Chapter 4 Petersburg limit
API (`petersburgLimit`, `petersburgPartialSum_ae_tendsto_limit`, `petersburgLimit_ae_eq_one`,
`integral_petersburgPartialSum_eq_zero`) and the Chapter 9/Mathlib martingale owner abstraction
(`petersburg_game_gain_process_martingale`, `ℱ.limitProcess`). The only `bridge/view` introduced
here is the almost-sure identification of that canonical `limitProcess` with the constant `1`;
the file does not keep a parallel wrapper around the Petersburg process itself.
-/

/-- Helper for Example 11.6: the fair Bernoulli product measure has total mass `1`. -/
private theorem fairBernoulliMeasure_univ_eq_one :
    μ Set.univ = 1 := by
  simp [fairBernoulliMeasure]

/-- Helper for Example 11.6: the fair Bernoulli product measure is a probability measure. -/
private theorem fairBernoulliMeasure_isProbabilityMeasure :
    IsProbabilityMeasure μ :=
  ⟨fairBernoulliMeasure_univ_eq_one⟩

/-- Helper for Example 11.6: every Petersburg gain has expectation `0`. -/
private theorem integral_petersburg_gain_process_eq_zero (n : ℕ) :
    ∫ ω, S n ω ∂ μ = 0 := by
  letI : IsProbabilityMeasure μ := fairBernoulliMeasure_isProbabilityMeasure
  have hInt :
      ∫ ω in Set.univ, S 0 ω ∂ μ = ∫ ω in Set.univ, S n ω ∂ μ :=
    (petersburg_game_gain_process_martingale.setIntegral_eq
      (i := 0) (j := n) (by simp) MeasurableSet.univ)
  calc
    ∫ ω, S n ω ∂ μ = ∫ ω, S 0 ω ∂ μ := by simpa using hInt.symm
    _ = 0 := by simp [petersburgPartialSum]

/-- Helper for Example 11.6: the event that the first `n` rounds are all losses. -/
private def petersburgPrefixLosses (n : ℕ) : Set BernoulliSequence :=
  {ω | ∀ k < n, ω k = false}

/-- Helper for Example 11.6: the prefix-loss events shrink as the prefix length grows. -/
private theorem petersburgPrefixLosses_antitone :
    Antitone petersburgPrefixLosses := by
  -- Forgetting the final loss condition leaves an earlier prefix-loss event.
  intro m n hmn ω hω k hk
  exact hω k (lt_of_lt_of_le hk hmn)

/-- Helper for Example 11.6: the prefix-loss events are measurable finite-coordinate cylinders. -/
private theorem measurableSet_petersburgPrefixLosses (n : ℕ) :
    MeasurableSet (petersburgPrefixLosses n) := by
  -- Rewrite the event as a finite intersection of coordinate singleton events.
  have hset :
      petersburgPrefixLosses n =
        ⋂ k ∈ Finset.range n, Function.eval k ⁻¹' ({false} : Set Bool) := by
    ext ω
    simp [petersburgPrefixLosses]
  rw [hset]
  exact (Finset.range n).measurableSet_biInter fun k _ ↦
    (measurable_pi_apply k) (measurableSet_singleton false)

/-- Helper for Example 11.6: the fair Bernoulli mass of `n` initial losses is `(1/2)^n`. -/
private theorem petersburgPrefixLosses_measure (n : ℕ) :
    μ (petersburgPrefixLosses n) = (1 / 2 : ENNReal) ^ n := by
  -- Identify the prefix-loss event with the corresponding finite product cylinder.
  have hset :
      petersburgPrefixLosses n =
        Set.pi (Finset.range n) (fun _ : ℕ ↦ ({false} : Set Bool)) := by
    ext ω
    simp [petersburgPrefixLosses, Set.mem_pi]
  rw [hset]
  let ν : ℕ → Measure Bool := fun _ ↦ (PMF.uniformOfFintype Bool).toMeasure
  have hpi :
      Measure.infinitePi ν
        (Set.pi (Finset.range n) (fun _ : ℕ ↦ ({false} : Set Bool))) =
          ∏ i ∈ Finset.range n, ν i ({false} : Set Bool) := by
    exact Measure.infinitePi_pi ν
      (s := Finset.range n)
      (t := fun _ : ℕ ↦ ({false} : Set Bool))
      (fun _ _ ↦ measurableSet_singleton false)
  simpa [fairBernoulliMeasure, ν, PMF.uniformOfFintype_apply] using hpi

/-- Helper for Example 11.6: belonging to every prefix-loss event means that every toss is a
loss. -/
private theorem mem_iInter_petersburgPrefixLosses_iff {ω : BernoulliSequence} :
    ω ∈ ⋂ n, petersburgPrefixLosses n ↔ ∀ n, ω n = false := by
  constructor
  · intro hω n
    -- Read the `n`th coordinate from the `(n + 1)`-prefix all-loss event.
    have hprefix : ω ∈ petersburgPrefixLosses (n + 1) := Set.mem_iInter.mp hω (n + 1)
    exact hprefix n (by omega)
  · intro hω
    -- Repackage the pointwise all-loss statement into every finite prefix event.
    refine Set.mem_iInter.mpr ?_
    intro n
    show ω ∈ petersburgPrefixLosses n
    intro k hk
    exact hω k

/-- Helper for Example 11.6: the all-loss branch has probability zero under the fair Bernoulli
product measure. -/
private theorem all_losses_measure_zero :
    μ {ω : BernoulliSequence | ∀ n, ω n = false} = 0 := by
  have hfinite : ∃ n, μ (petersburgPrefixLosses n) ≠ ⊤ := by
    -- The stage `n = 0` event is the whole space and has finite mass.
    refine ⟨0, ?_⟩
    rw [petersburgPrefixLosses_measure]
    norm_num
  have hpow :
      Tendsto (fun n : ℕ ↦ (1 / 2 : NNReal) ^ n) atTop (nhds (0 : NNReal)) := by
    -- The fair-coin prefix-loss masses decay geometrically to zero.
    simpa using
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : NNReal)) (by norm_num))
  have hprefix_tendsto :
      Tendsto (fun n : ℕ ↦ μ (petersburgPrefixLosses n)) atTop (nhds (0 : ENNReal)) := by
    have hpow_enn :
        Tendsto (fun n : ℕ ↦ ((1 / 2 : NNReal) ^ n : ENNReal)) atTop (nhds (0 : ENNReal)) := by
      exact (ENNReal.continuous_coe.tendsto 0).comp hpow
    simpa [petersburgPrefixLosses_measure] using hpow_enn
  have hinter_tendsto_comp :
      Tendsto (μ ∘ petersburgPrefixLosses) atTop
        (nhds (μ (⋂ n, petersburgPrefixLosses n))) := by
    exact tendsto_measure_iInter_atTop
      (fun n ↦ (measurableSet_petersburgPrefixLosses n).nullMeasurableSet)
      petersburgPrefixLosses_antitone
      hfinite
  have hinter_tendsto :
      Tendsto (fun n : ℕ ↦ μ (petersburgPrefixLosses n)) atTop
        (nhds (μ (⋂ n, petersburgPrefixLosses n))) := by
    simpa [Function.comp] using hinter_tendsto_comp
  have hinter : μ (⋂ n, petersburgPrefixLosses n) = 0 :=
    tendsto_nhds_unique hinter_tendsto hprefix_tendsto
  -- Rewrite the exceptional all-loss branch as the decreasing intersection of prefix-loss events.
  have hset :
      {ω : BernoulliSequence | ∀ n, ω n = false} = ⋂ n, petersburgPrefixLosses n := by
    ext ω
    rw [Set.mem_setOf_eq, mem_iInter_petersburgPrefixLosses_iff]
  rw [hset]
  exact hinter

-- Proof sketch: use the pathwise identity
-- `one_sub_petersburgGainProcess_eq_prod`; each factor `1 - D_i(ω)` is either `0` or `2`, hence
-- the product is nonnegative and therefore `1 - S_n(ω) ≥ 0`.
/-- Every finite Petersburg gain is pathwise bounded above by `1`, hence also almost surely. -/
theorem petersburg_gain_process_le_one (n : ℕ) (ω : BernoulliSequence) :
    S n ω ≤ 1 := by
  -- Freeze the pathwise two-branch normal form and inspect the all-loss prefix event.
  rw [petersburgPartialSum_eq_if_allPrefixLosses]
  by_cases hprefix : ∀ k < n, ω k = false
  · rw [if_pos hprefix]
    have hpow : 0 ≤ (2 : ℝ) ^ n := by positivity
    linarith
  · rw [if_neg hprefix]

-- Proof sketch: reuse the Chapter 4 owner theorem `petersburgPartialSum_ae_tendsto_limit`, then
-- intersect with the full-measure event from `petersburgLimit_ae_eq_one`; on that event the
-- `EReal` limit is the finite value `1`, so the convergence upgrades to ordinary real-valued
-- convergence to the constant random variable `1`.
/-- Example 11.6: the Petersburg game gain process from Example 9.40 converges almost surely to
the constant random variable `1`. -/
theorem petersburg_gain_process_ae_tendsto_one :
    ∀ᵐ ω ∂ μ, Tendsto (fun n ↦ S n ω) atTop (nhds 1) :=
  by
  -- Route correction: the Chapter 4 `EReal` limit lemmas are not imported here, so prove the
  -- almost-sure limit directly from the first-win event and the pathwise two-branch normal form.
  have h_not_all_losses : ∀ᵐ ω ∂ μ, ¬ ∀ n, ω n = false := by
    rw [ae_iff]
    simpa [not_not] using all_losses_measure_zero
  filter_upwards [h_not_all_losses] with ω hω
  have hwin : ∃ m, ω m = true := by
    by_contra hwin
    apply hω
    intro n
    cases hωn : ω n with
    | false =>
        simp
    | true =>
        exfalso
        exact hwin ⟨n, hωn⟩
  rcases hwin with ⟨m, hm⟩
  have h_eventually : (fun _ : ℕ ↦ (1 : ℝ)) =ᶠ[atTop] fun n ↦ S n ω := by
    refine Filter.eventually_atTop.2 ⟨m + 1, ?_⟩
    intro n hn
    have hm_lt_n : m < n := lt_of_lt_of_le (Nat.lt_succ_self m) hn
    have hnotprefix : ¬ ∀ k < n, ω k = false := by
      intro hprefix
      have hmfalse : ω m = false := hprefix m hm_lt_n
      simp [hm] at hmfalse
    change (1 : ℝ) = S n ω
    rw [petersburgPartialSum_eq_if_allPrefixLosses, if_neg hnotprefix]
  exact Tendsto.congr' h_eventually tendsto_const_nhds

-- Proof sketch: if the martingale were uniformly integrable, then the owner theorem
-- `Martingale.ae_eq_condExp_limitProcess` would identify each `S_n` with the conditional
-- expectation of the canonical limit process `ℱ.limitProcess S μ`; compare that owner limit with
-- the Chapter 4 almost-sure limit `1` using `petersburg_gain_process_ae_tendsto_one`.
/-- The canonical Chapter 11 limit process of the Petersburg gain martingale is almost surely the
constant random variable `1`. -/
theorem petersburg_gain_process_limitProcess_ae_eq_one :
    limitProcess S ℱ μ =ᵐ[μ] fun _ ↦ (1 : ℝ) := by
  classical
  let hlimit :
      ∃ g : BernoulliSequence → ℝ,
        StronglyMeasurable[⨆ n, ℱ n] g ∧
          ∀ᵐ ω ∂ μ, Tendsto (fun n ↦ S n ω) atTop (nhds (g ω)) :=
    ⟨fun _ ↦ (1 : ℝ), stronglyMeasurable_const, petersburg_gain_process_ae_tendsto_one⟩
  -- Unfold the owner choice: `limitProcess` selects one almost-sure limit once such a limit exists.
  rw [Filtration.limitProcess, dif_pos hlimit]
  have hchosen :
      ∀ᵐ ω ∂ μ, Tendsto (fun n ↦ S n ω) atTop (nhds (Classical.choose hlimit ω)) :=
    (Classical.choose_spec hlimit).2
  -- Compare the chosen limit with the explicit a.s. limit `1`; real limits are pointwise unique.
  filter_upwards [hchosen, petersburg_gain_process_ae_tendsto_one] with ω hω hω'
  exact tendsto_nhds_unique hω hω'

-- Proof sketch: if `S_n → 1` in mean, then the owner theorem `TendstoInMean.integrableSeq`
-- gives integrability of each `S_n`, `TendstoInMean.integrable` gives integrability of the limit,
-- and `TendstoInMean.tendsto_eLpNorm` recovers the raw `L¹` seminorm convergence. The standard
-- `L¹` continuity of integration would then force the integrals to converge. But `∫ S_n dP = 0`
-- for every `n`, while `∫ 1 dP = 1` on the fair Bernoulli probability space, giving a
-- contradiction.
/-- The almost-sure convergence of the Petersburg gain process does not improve to convergence in
`L¹`. -/
theorem petersburg_gain_process_not_tendstoInMean_to_one :
    ¬ TendstoInMean μ S (fun _ ↦ (1 : ℝ)) := by
  letI : IsProbabilityMeasure μ := fairBernoulliMeasure_isProbabilityMeasure
  letI : IsFiniteMeasure μ := inferInstance
  intro h_mean
  have hIntSub : ∀ n, Integrable (fun ω ↦ S n ω - 1) μ := by
    intro n
    exact (petersburg_game_gain_process_martingale.integrable n).sub (integrable_const 1)
  have hEq :
      (fun n ↦ eLpNorm (S n - fun _ ↦ (1 : ℝ)) 1 μ) =
        fun n ↦ ENNReal.ofReal (∫ ω, ‖S n ω - 1‖ ∂ μ) := by
    funext n
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp_rw [Pi.sub_apply]
    exact (ofReal_integral_norm_eq_lintegral_enorm (hIntSub n)).symm
  have hL1_ofReal :
      Tendsto (fun n ↦ ENNReal.ofReal (∫ ω, ‖S n ω - 1‖ ∂ μ)) atTop (nhds 0) := by
    -- Rewrite the `L¹` seminorms as ordinary integrals of the absolute errors.
    simpa [hEq] using h_mean.tendsto_eLpNorm
  have hL1_toReal :
      Tendsto (fun n ↦ (ENNReal.ofReal (∫ ω, ‖S n ω - 1‖ ∂ μ)).toReal) atTop (nhds 0) := by
    simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1_ofReal
  have hL1 :
      Tendsto (fun n ↦ ∫ ω, ‖S n ω - 1‖ ∂ μ) atTop (nhds 0) := by
    have hToRealEq :
        (fun n ↦ (ENNReal.ofReal (∫ ω, ‖S n ω - 1‖ ∂ μ)).toReal) =
          fun n ↦ ∫ ω, ‖S n ω - 1‖ ∂ μ := by
      funext n
      rw [ENNReal.toReal_ofReal]
      exact integral_nonneg fun _ ↦ norm_nonneg _
    exact Tendsto.congr' (EventuallyEq.of_eq hToRealEq) hL1_toReal
  have hLower : ∀ n, 1 ≤ ∫ ω, ‖S n ω - 1‖ ∂ μ := by
    intro n
    have hIntegral :
        ‖∫ ω, (S n ω - 1) ∂ μ‖ = (1 : ℝ) := by
      rw [integral_sub (petersburg_game_gain_process_martingale.integrable n) (integrable_const 1)]
      simp [integral_petersburg_gain_process_eq_zero n]
    calc
      1 = ‖∫ ω, (S n ω - 1) ∂ μ‖ := hIntegral.symm
      _ ≤ ∫ ω, ‖S n ω - 1‖ ∂ μ := by
        simpa using norm_integral_le_integral_norm (fun ω ↦ S n ω - 1)
  -- The limit `0` would force the nonnegative error integrals eventually below `1 / 2`.
  have hEventually :
      ∀ᶠ n in atTop, ∫ ω, ‖S n ω - 1‖ ∂ μ < 1 / 2 :=
    hL1.eventually <| Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventually
  have hAbsurd : ¬ ((1 : ℝ) ≤ 1 / 2) := by
    norm_num
  exact hAbsurd <| le_trans (hLower N) (le_of_lt (hN N le_rfl))

-- Proof sketch: a uniformly integrable martingale converges in `L¹` to its owner limit process
-- `ℱ.limitProcess S μ`; the bridge theorem `petersburg_gain_process_limitProcess_ae_eq_one`
-- identifies that canonical limit with `1`, contradicting
-- `petersburg_gain_process_not_tendstoInMean_to_one`.
/-- The Petersburg gain process is not uniformly integrable. -/
theorem petersburg_gain_process_not_uniformIntegrable :
    ¬ UniformIntegrable S 1 μ := by
  letI : IsProbabilityMeasure μ := fairBernoulliMeasure_isProbabilityMeasure
  letI : IsFiniteMeasure μ := inferInstance
  intro hUI
  have h_tendsto_limit :
      Tendsto (fun n ↦ eLpNorm (S n - limitProcess S ℱ μ) 1 μ) atTop (nhds 0) :=
    petersburg_game_gain_process_martingale.submartingale.tendsto_eLpNorm_one_limitProcess hUI
  have h_tendsto_one :
      Tendsto (fun n ↦ eLpNorm (S n - fun _ ↦ (1 : ℝ)) 1 μ) atTop (nhds 0) := by
    -- Rewrite the canonical owner limit to the explicit constant limit from the previous theorem.
    have hEq :
        (fun n ↦ eLpNorm (S n - limitProcess S ℱ μ) 1 μ) =
          fun n ↦ eLpNorm (S n - fun _ ↦ (1 : ℝ)) 1 μ := by
      funext n
      exact eLpNorm_congr_ae (EventuallyEq.sub EventuallyEq.rfl
        petersburg_gain_process_limitProcess_ae_eq_one)
    simpa [hEq] using h_tendsto_limit
  have h_mean : TendstoInMean μ S (fun _ ↦ (1 : ℝ)) := by
    refine (tendstoInMean_iff).2 ?_
    exact ⟨fun n ↦ petersburg_game_gain_process_martingale.integrable n, integrable_const 1,
      h_tendsto_one⟩
  exact petersburg_gain_process_not_tendstoInMean_to_one h_mean
