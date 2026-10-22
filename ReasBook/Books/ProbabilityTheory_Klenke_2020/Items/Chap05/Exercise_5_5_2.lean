/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ProbabilityTheory

universe u

variable {Ω : Type u}

-- Lebesgue measure restricted to the unit interval `[0,1]`.
local notation "unitIntervalVolume" => volume.restrict (Set.Icc (0 : ℝ) 1)

noncomputable section

/-- Helper for Exercise 5.5.2: the `n`th arrival time of a `0`-indexed interarrival sequence is
the sum of its first `n` interarrivals. -/
private def arrivalTime (W : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range n, W i ω

/-- Helper for Exercise 5.5.2: the initial arrival time is `0`. -/
@[simp] private theorem arrivalTime_zero (W : ℕ → Ω → ℝ) :
    arrivalTime W 0 = 0 := by
  -- Proof comment: the empty partial sum is zero.
  funext ω
  simp [arrivalTime]

/-- Helper for Exercise 5.5.2: the next arrival time adds the next interarrival. -/
@[simp] private theorem arrivalTime_succ (W : ℕ → Ω → ℝ) (n : ℕ) :
    arrivalTime W (n + 1) = arrivalTime W n + W n := by
  -- Proof comment: split the range sum at the final index.
  funext ω
  simp [arrivalTime, Finset.sum_range_succ]

/-- Helper for Exercise 5.5.2: the renewal count is the smallest index whose next arrival exceeds
the observation time. -/
private noncomputable def renewalCountingProcess (W : ℕ → Ω → ℝ) : NNReal → Ω → ℕ :=
  fun t ω ↦ sInf {n : ℕ | t < arrivalTime W (n + 1) ω}

variable [MeasurableSpace Ω]

/-- Helper for Exercise 5.5.2: the unit-interval measure assigns zero mass to `(-∞, 0]`. -/
private theorem unitIntervalVolume_Iic_zero :
    unitIntervalVolume (Set.Iic (0 : ℝ)) = 0 := by
  -- Proof comment: restricting Lebesgue measure to `[0,1]` turns `(-∞, 0]` into the singleton
  -- `{0}`, and singletons have zero volume.
  rw [Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic (0 : ℝ) ∩ Set.Icc (0 : ℝ) 1 = ({0} : Set ℝ) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx_nonpos, hx_unit⟩
      have hx_nonpos' : x ≤ 0 := by
        simpa using hx_nonpos
      apply Set.mem_singleton_iff.2
      exact le_antisymm hx_nonpos' hx_unit.1
    · intro hx
      rcases Set.mem_singleton_iff.1 hx with rfl
      simp
  rw [hset]
  simp

/-- Helper for Exercise 5.5.2: the unit-interval measure gives the right half-interval mass
`1 / 2`. -/
private theorem unitIntervalVolume_real_Ioi_half :
    (unitIntervalVolume).real (Set.Ioi (1 / 2 : ℝ)) = (1 : ℝ) / 2 := by
  -- Proof comment: intersecting `(1 / 2, ∞)` with `[0,1]` leaves the interval `(1 / 2, 1]`,
  -- whose Lebesgue measure is `1 / 2`.
  rw [measureReal_def]
  rw [Measure.restrict_apply measurableSet_Ioi]
  have hset :
      Set.Ioi (1 / 2 : ℝ) ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc (1 / 2 : ℝ) 1 := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx_half, hx_unit⟩
      have hx_half' : (1 / 2 : ℝ) < x := by
        simpa using hx_half
      exact ⟨hx_half', hx_unit.2⟩
    · intro hx
      rcases hx with ⟨hx_half, hx_one⟩
      exact ⟨hx_half, ⟨by linarith, hx_one⟩⟩
  rw [hset]
  norm_num [Real.volume_Ioc]

/-- Helper for Exercise 5.5.2: every coordinate of an i.i.d. unit-interval interarrival sequence
has the same uniform law as the distinguished coordinate `X 0`. -/
private theorem interarrival_hasLaw_of_iid_unitInterval
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P) (n : ℕ) :
    HasLaw (X n) unitIntervalVolume P := by
  -- Proof comment: identical distribution transports the unit-interval law from `X 0` to `X n`.
  exact (hX_iid.identDistrib 0 n).hasLaw hX0_law

/-- Helper for Exercise 5.5.2: every finite prefix of the i.i.d. interarrival sequence has the
finite product of unit-interval laws as its distribution. -/
private theorem iid_unitInterval_prefix_hasLaw_pi
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P) (n : ℕ) :
    HasLaw (fun ω ↦ fun i : Fin n ↦ X i ω)
      (Measure.pi (fun _ : Fin n ↦ unitIntervalVolume)) P := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: the finite coordinate vector is almost everywhere measurable coordinatewise.
    exact aemeasurable_pi_lambda _ fun i : Fin n ↦
      (interarrival_hasLaw_of_iid_unitInterval P X hX_iid hX0_law i).aemeasurable
  · have h_prefix_iIndep : iIndepFun (fun i : Fin n ↦ X i) P :=
      hX_iid.iIndepFun.precomp Fin.val_injective
    -- Proof comment: restrict the i.i.d. family to the finite index type `Fin n`.
    rw [(
      iIndepFun_iff_map_fun_eq_pi_map
        (fun i : Fin n ↦
          (interarrival_hasLaw_of_iid_unitInterval P X hX_iid hX0_law i).aemeasurable)).1
      h_prefix_iIndep]
    have h_marginals :
        (fun i : Fin n ↦ Measure.map (X i) P) = fun _ : Fin n ↦ unitIntervalVolume := by
      funext i
      exact (interarrival_hasLaw_of_iid_unitInterval P X hX_iid hX0_law i).map_eq
    -- Proof comment: each coordinate marginal is the same unit-interval law.
    rw [h_marginals]

/-- Helper for Exercise 5.5.2: every interarrival is almost surely strictly positive under the
unit-interval law. -/
private theorem ae_interarrival_pos_of_iid_unitInterval
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P) :
    ∀ᵐ ω ∂P, ∀ n, 0 < X n ω := by
  have h_pos_unitInterval : ∀ᵐ x ∂unitIntervalVolume, 0 < x := by
    -- Proof comment: the uniform law on `[0,1]` assigns zero mass to the single point `0`.
    rw [ae_iff]
    simpa [not_lt] using unitIntervalVolume_Iic_zero
  refine ae_all_iff.2 fun n ↦ ?_
  have hXn_law := interarrival_hasLaw_of_iid_unitInterval P X hX_iid hX0_law n
  -- Proof comment: transport the positivity event through the law of `X n`.
  exact (hXn_law.ae_iff (measurable_const.lt measurable_id)).2 h_pos_unitInterval

/-- Helper for Exercise 5.5.2: an i.i.d. unit-interval interarrival sequence almost surely has
strictly increasing arrival times and arrival times diverging to `∞`. -/
private theorem ae_arrivalTime_strictMono_and_tendsto_of_iid_unitInterval
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P) :
    ∀ᵐ ω ∂P,
      StrictMono (fun n ↦ arrivalTime X n ω) ∧
        Tendsto (fun n ↦ arrivalTime X n ω) atTop atTop := by
  let F : ℝ → ℝ := Set.indicator (Set.Ioi (1 / 2 : ℝ)) (fun _ ↦ (1 : ℝ))
  let Y : ℕ → Ω → ℝ := fun n ω ↦ F (X n ω)
  letI : IsProbabilityMeasure unitIntervalVolume := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have hF_meas : Measurable F := by
    -- Proof comment: the large-gap indicator is measurable because `Ioi (1 / 2)` is measurable.
    simpa [F] using (measurable_indicator_const_iff (1 : ℝ)).2 measurableSet_Ioi
  have hF_law : HasLaw F (Measure.map F unitIntervalVolume) unitIntervalVolume := by
    exact
      (show MeasurePreserving F unitIntervalVolume (Measure.map F unitIntervalVolume) from
        ⟨hF_meas, rfl⟩).hasLaw
  have hF_integrable : Integrable F unitIntervalVolume := by
    -- Proof comment: `F` is a bounded indicator, hence integrable under the probability law.
    simpa [F] using (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  have hY_iIndep : iIndepFun Y P := by
    -- Proof comment: independence is preserved under measurable postcomposition.
    simpa [Y] using hX_iid.iIndepFun.comp (fun _ ↦ F) (fun _ ↦ hF_meas)
  have hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) P P := by
    -- Proof comment: all large-gap indicators have the same law because the interarrivals are
    -- identically distributed.
    intro n
    simpa [Y] using (hX_iid.identDistrib n 0).comp hF_meas
  have hY0_ident : IdentDistrib (Y 0) F P unitIntervalVolume := by
    have hY0_law : HasLaw (Y 0) (Measure.map F unitIntervalVolume) P := by
      -- Proof comment: push the law of `X 0` forward through the indicator map `F`.
      simpa [Y] using hF_law.fun_comp hX0_law
    exact hY0_law.identDistrib hF_law
  have hY0_integrable : Integrable (Y 0) P := by
    -- Proof comment: integrability transfers across identical distribution.
    exact hY0_ident.integrable_iff.2 hF_integrable
  have hY0_expectation : P[Y 0] = (1 : ℝ) / 2 := by
    -- Proof comment: the mean of the indicator is exactly the half-interval probability.
    calc
      P[Y 0] = ∫ x, F x ∂unitIntervalVolume := by
        simpa [Y] using hX0_law.integral_comp hF_meas.aestronglyMeasurable
      _ = (unitIntervalVolume).real (Set.Ioi (1 / 2 : ℝ)) := by
        simp [F, integral_indicator_const, measurableSet_Ioi, smul_eq_mul]
      _ = (1 : ℝ) / 2 := unitIntervalVolume_real_Ioi_half
  have hY0_expectation_pos : 0 < P[Y 0] := by
    rw [hY0_expectation]
    norm_num
  have hY_limit :
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Y i ω) / n) atTop
        (𝓝 (P[Y 0])) := by
    -- Proof comment: apply the strong law to the i.i.d. large-gap indicators.
    exact ProbabilityTheory.strong_law_ae_real Y hY0_integrable
      (fun i j hij ↦ hY_iIndep.indepFun hij) hY_ident
  have hX_pos : ∀ᵐ ω ∂P, ∀ n, 0 < X n ω :=
    ae_interarrival_pos_of_iid_unitInterval P X hX_iid hX0_law
  filter_upwards [hX_pos, hY_limit] with ω hX_pos_ω hY_limit_ω
  refine ⟨?_, ?_⟩
  · -- Proof comment: strictly positive interarrivals force strict growth of the arrival times.
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    rw [arrivalTime_succ]
    exact lt_add_of_pos_right _ (hX_pos_ω n)
  · -- Route correction: instead of estimating the raw uniform sums directly, compare them with the
    -- count of interarrivals larger than `1 / 2`, whose strong-law limit is the positive constant
    -- `1 / 2`. Since `1_{x > 1 / 2} ≤ 2x` on `[0,1]`, this still yields a linear lower bound on
    -- the arrival times and hence divergence to `∞`.
    have hYsum_le_double_arrival :
        ∀ n, (∑ i ∈ Finset.range n, Y i ω) ≤ 2 * arrivalTime X n ω := by
      -- Proof comment: each large-gap indicator is bounded by twice the corresponding interarrival.
      intro n
      calc
        ∑ i ∈ Finset.range n, Y i ω ≤ ∑ i ∈ Finset.range n, 2 * X i ω := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          by_cases hlarge : 1 / 2 < X i ω
          · have hbound : (1 : ℝ) ≤ 2 * X i ω := by
              linarith
            have hlarge' : (2 : ℝ)⁻¹ < X i ω := by
              simpa using hlarge
            simpa [Y, F, hlarge'] using hbound
          · have hnonneg : 0 ≤ X i ω := (hX_pos_ω i).le
            have hbound : 0 ≤ 2 * X i ω := by
              exact mul_nonneg zero_le_two hnonneg
            have hlarge' : ¬ (2 : ℝ)⁻¹ < X i ω := by
              simpa using hlarge
            simpa [Y, F, hlarge'] using hbound
        _ = 2 * arrivalTime X n ω := by
          simp [arrivalTime, Finset.mul_sum]
    have hhalf_pos : 0 < P[Y 0] / 2 := by
      linarith
    have hhalf_lt : P[Y 0] / 2 < P[Y 0] := by
      linarith
    have havg_eventually :
        ∀ᶠ n : ℕ in atTop, P[Y 0] / 2 < (∑ i ∈ Finset.range n, Y i ω) / n := by
      -- Proof comment: the strong-law limit is positive, so the empirical frequency is
      -- eventually bounded below by half of that limit.
      exact hY_limit_ω.eventually (Ioi_mem_nhds hhalf_lt)
    have hlinear_le_sumY :
        (fun n : ℕ ↦ (P[Y 0] / 2) * (n : ℝ)) ≤ᶠ[atTop] fun n ↦ ∑ i ∈ Finset.range n, Y i ω := by
      -- Proof comment: multiply the eventual lower bound on the empirical frequencies by `n`.
      filter_upwards [havg_eventually] with n hn
      by_cases hzero : n = 0
      · subst hzero
        simp
      · have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero)
        exact le_of_lt ((lt_div_iff₀ hn_pos).mp hn)
    have hquarter_pos : 0 < P[Y 0] / 4 := by
      linarith
    have hlinear_tendsto :
        Tendsto (fun n : ℕ ↦ (P[Y 0] / 4) * (n : ℝ)) atTop atTop := by
      -- Proof comment: a positive multiple of `n` still tends to `∞`.
      exact Filter.Tendsto.const_mul_atTop' hquarter_pos tendsto_natCast_atTop_atTop
    have harrival_lower :
        (fun n : ℕ ↦ (P[Y 0] / 4) * (n : ℝ)) ≤ᶠ[atTop] fun n ↦ arrivalTime X n ω := by
      filter_upwards [hlinear_le_sumY] with n hn
      have hdouble_le : (P[Y 0] / 2) * (n : ℝ) ≤ 2 * arrivalTime X n ω := by
        exact le_trans hn (hYsum_le_double_arrival n)
      linarith
    -- Proof comment: eventual domination by a divergent linear function forces the arrival times
    -- themselves to diverge to `∞`.
    exact tendsto_atTop_mono' atTop harrival_lower hlinear_tendsto

/-- Helper for Exercise 5.5.2: an i.i.d. unit-interval interarrival sequence almost surely has
strictly increasing arrival times. -/
private theorem ae_arrivalTime_strictMono_of_iid_unitInterval
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P) :
    ∀ᵐ ω ∂P, StrictMono (fun n ↦ arrivalTime X n ω) := by
  filter_upwards
    [ae_arrivalTime_strictMono_and_tendsto_of_iid_unitInterval P X hX_iid hX0_law]
    with ω hω
  exact hω.1

/-- Helper for Exercise 5.5.2: an i.i.d. unit-interval interarrival sequence almost surely has
arrival times diverging to `∞`. -/
private theorem ae_arrivalTime_tendsto_of_iid_unitInterval
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ arrivalTime X n ω) atTop atTop := by
  filter_upwards
    [ae_arrivalTime_strictMono_and_tendsto_of_iid_unitInterval P X hX_iid hX0_law]
    with ω hω
  exact hω.2

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.2: on a genuine renewal path, the count inequality `n < N_t`
is equivalent to saying that the `(n + 1)`st arrival has already occurred by time `t`. -/
private theorem renewalCountingProcess_lt_iff_arrivalTime_le
    (W : ℕ → Ω → ℝ) {t : NNReal} {ω : Ω} {n : ℕ}
    (h_arrival_strict : StrictMono (fun m ↦ arrivalTime W m ω))
    (h_arrival_tendsto : Tendsto (fun m ↦ arrivalTime W m ω) atTop atTop) :
    n < renewalCountingProcess W t ω ↔ arrivalTime W (n + 1) ω ≤ t := by
  let S : Set ℕ := {m : ℕ | t < arrivalTime W (m + 1) ω}
  have h_nonempty : S.Nonempty := by
    obtain ⟨N, hN⟩ := (tendsto_atTop.1 h_arrival_tendsto ((t : ℝ) + 1)).exists
    have hN_pos : 0 < N := by
      by_contra hN_zero
      have hN_eq : N = 0 := Nat.eq_zero_of_not_pos hN_zero
      have hle : (t : ℝ) + 1 ≤ arrivalTime W 0 ω := by
        simpa [hN_eq] using hN
      simp [arrivalTime_zero] at hle
      linarith
    refine ⟨N - 1, ?_⟩
    have hle : (t : ℝ) + 1 ≤ arrivalTime W N ω := hN
    have hlt : (t : ℝ) < arrivalTime W N ω := by
      linarith
    have hpred : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hN_pos)
    change (t : ℝ) < arrivalTime W ((N - 1) + 1) ω
    rw [hpred]
    exact hlt
  constructor
  · intro hn
    by_contra harrival
    have hmem : n ∈ S := by
      -- Proof comment: if `T_(n+1)` already exceeds `t`, then `n` lies in the defining set.
      exact lt_of_not_ge harrival
    have hsInf_le : sInf S ≤ n := Nat.sInf_le hmem
    exact not_lt_of_ge hsInf_le (by simpa [renewalCountingProcess, S] using hn)
  · intro harrival
    have hsInf_mem : sInf S ∈ S := Nat.sInf_mem h_nonempty
    have hsInf_lt : t < arrivalTime W (sInf S + 1) ω := by
      simpa [S] using hsInf_mem
    by_contra hn
    have hsInf_le : sInf S ≤ n := Nat.not_lt.mp (by simpa [renewalCountingProcess, S] using hn)
    have hupper_le :
        arrivalTime W (sInf S + 1) ω ≤ arrivalTime W (n + 1) ω :=
      h_arrival_strict.monotone (Nat.succ_le_succ hsInf_le)
    exact not_lt_of_ge (le_trans hupper_le harrival) hsInf_lt

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.2: on a genuine renewal path, the renewal count is the tail-indicator
series of the arrival-time events `T_(n+1) ≤ t`. -/
private theorem renewalCount_eq_tsum_arrivalIndicators
    (W : ℕ → Ω → ℝ) {t : NNReal} {ω : Ω}
    (h_arrival_strict : StrictMono (fun n ↦ arrivalTime W n ω))
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) :
    (renewalCountingProcess W t ω : ℝ) =
      ∑' n : ℕ, if arrivalTime W (n + 1) ω ≤ t then (1 : ℝ) else 0 := by
  let N := renewalCountingProcess W t ω
  have htail_zero :
      ∀ n ∉ Finset.range N,
        (if arrivalTime W (n + 1) ω ≤ t then (1 : ℝ) else 0) = 0 := by
    intro n hn
    have hN_le : N ≤ n := by
      exact Nat.not_lt.mp (by simpa [N, Finset.mem_range] using hn)
    have harrival_not_le : ¬ arrivalTime W (n + 1) ω ≤ t := by
      intro hle
      have hn_lt :
          n < renewalCountingProcess W t ω :=
        (renewalCountingProcess_lt_iff_arrivalTime_le W h_arrival_strict h_arrival_tendsto).2 hle
      exact (Nat.not_lt.mpr hN_le) hn_lt
    -- Proof comment: once `n` lies beyond `N_t - 1`, the pathwise strip characterization forces
    -- the corresponding tail indicator to vanish.
    exact if_neg harrival_not_le
  calc
    (renewalCountingProcess W t ω : ℝ) = ∑ n ∈ Finset.range N, (1 : ℝ) := by
      -- Proof comment: the finite sum of `1`s over `range N_t` is exactly the count `N_t`.
      simp [N]
    _ = ∑ n ∈ Finset.range N, if arrivalTime W (n + 1) ω ≤ t then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hn_lt :
          n < renewalCountingProcess W t ω := by
        simpa [N, Finset.mem_range] using hn
      have harrival_le :
          arrivalTime W (n + 1) ω ≤ t :=
        (renewalCountingProcess_lt_iff_arrivalTime_le W h_arrival_strict h_arrival_tendsto).1 hn_lt
      -- Proof comment: inside `range N_t`, each tail indicator is equal to `1`.
      exact (if_pos harrival_le).symm
    _ = ∑' n : ℕ, if arrivalTime W (n + 1) ω ≤ t then (1 : ℝ) else 0 := by
      -- Proof comment: the indicator family has finite support, so the `tsum` reduces to the
      -- corresponding finite sum.
      symm
      exact tsum_eq_sum htail_zero

/-- Helper for Exercise 5.5.2: the pointwise tail-indicator expansion holds almost surely for i.i.d.
unit-interval interarrivals. -/
private theorem ae_renewalCount_eq_tsum_arrivalIndicators
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P) (t : NNReal) :
    ∀ᵐ ω ∂P,
      (renewalCountingProcess X t ω : ℝ) =
        ∑' n : ℕ, if arrivalTime X (n + 1) ω ≤ t then (1 : ℝ) else 0 := by
  filter_upwards
    [ae_arrivalTime_strictMono_and_tendsto_of_iid_unitInterval P X hX_iid hX0_law]
    with ω hω
  exact renewalCount_eq_tsum_arrivalIndicators X hω.1 hω.2

/-- Helper for Exercise 5.5.2: the finite-prefix sum map on `Fin n → ℝ` is measurable. -/
private theorem prefixSum_measurable (n : ℕ) :
    Measurable (fun z : Fin n → ℝ ↦ ∑ i, z i) := by
  -- Proof comment: a finite sum of measurable coordinate projections is measurable.
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  exact measurable_pi_apply i

/-- Helper for Exercise 5.5.2: every arrival time is almost everywhere measurable under the i.i.d.
unit-interval law assumptions. -/
private theorem arrivalTime_aemeasurable_of_iid_unitInterval
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P) (n : ℕ) :
    AEMeasurable (fun ω ↦ arrivalTime X n ω) P := by
  induction n with
  | zero =>
      -- Proof comment: the zeroth arrival time is the constant zero function.
      simp [arrivalTime_zero]
  | succ n ih =>
      -- Proof comment: `T_(n+1) = T_n + X_n`, so a.e.-measurability is preserved by addition.
      simpa [arrivalTime_succ] using
        ih.add (interarrival_hasLaw_of_iid_unitInterval P X hX_iid hX0_law n).aemeasurable

/-- Helper for Exercise 5.5.2: the `(n + 1)`st arrival time has the same law as the sum of the
first `n + 1` coordinates on the finite unit cube with product measure. -/
private theorem arrivalTime_hasLaw_of_iid_unitInterval_prefixSum
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P) (n : ℕ) :
    HasLaw (fun ω ↦ arrivalTime X (n + 1) ω)
      (Measure.map (fun z : Fin (n + 1) → ℝ ↦ ∑ i, z i)
        (Measure.pi (fun _ : Fin (n + 1) ↦ unitIntervalVolume))) P := by
  let prefixSum : (Fin (n + 1) → ℝ) → ℝ := fun z ↦ ∑ i, z i
  have hPrefixLaw := iid_unitInterval_prefix_hasLaw_pi P X hX_iid hX0_law (n + 1)
  have hPrefixSumLaw :
      HasLaw prefixSum
        (Measure.map prefixSum (Measure.pi (fun _ : Fin (n + 1) ↦ unitIntervalVolume)))
        (Measure.pi (fun _ : Fin (n + 1) ↦ unitIntervalVolume)) := by
    -- Proof comment: every measurable function has its pushforward law under the source measure.
    exact
      (show MeasurePreserving prefixSum
          (Measure.pi (fun _ : Fin (n + 1) ↦ unitIntervalVolume))
          (Measure.map prefixSum (Measure.pi (fun _ : Fin (n + 1) ↦ unitIntervalVolume))) from
        ⟨prefixSum_measurable (n + 1), rfl⟩).hasLaw
  -- Proof comment: compose the finite-prefix product-law with the measurable coordinate-sum map.
  convert hPrefixSumLaw.fun_comp hPrefixLaw using 1
  funext ω
  simpa [prefixSum, arrivalTime] using
    (Fin.sum_univ_eq_sum_range (fun i ↦ X i ω) (n + 1)).symm

/-- Helper for Exercise 5.5.2: each arrival-time event `T_(n+1) ≤ t` transports to the product-law
sublevel event for the coordinate sum on the finite unit cube. -/
private theorem arrivalTimeEvent_eq_prefixSumSublevel_of_iid_unitInterval
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P)
    (t : NNReal) (n : ℕ) :
    P {ω | arrivalTime X (n + 1) ω ≤ t} =
      (Measure.pi (fun _ : Fin (n + 1) ↦ unitIntervalVolume))
        {z | ∑ i, z i ≤ (t : ℝ)} := by
  let prefixSum : (Fin (n + 1) → ℝ) → ℝ := fun z ↦ ∑ i, z i
  have hArrivalLaw :=
    arrivalTime_hasLaw_of_iid_unitInterval_prefixSum P X hX_iid hX0_law n
  calc
    P {ω | arrivalTime X (n + 1) ω ≤ t} =
        Measure.map (fun ω ↦ arrivalTime X (n + 1) ω) P (Set.Iic (t : ℝ)) := by
          -- Proof comment: rewrite the event through the pushforward law of the arrival time.
          symm
          rw [Measure.map_apply_of_aemeasurable
            (arrivalTime_aemeasurable_of_iid_unitInterval P X hX_iid hX0_law (n + 1))
            measurableSet_Iic]
          simp [Set.preimage, Set.mem_Iic]
    _ = Measure.map prefixSum (Measure.pi (fun _ : Fin (n + 1) ↦ unitIntervalVolume))
          (Set.Iic (t : ℝ)) := by
            rw [hArrivalLaw.map_eq]
    _ = (Measure.pi (fun _ : Fin (n + 1) ↦ unitIntervalVolume))
          {z | ∑ i, z i ≤ (t : ℝ)} := by
            -- Proof comment: apply the same pushforward rewrite on the finite-cube side.
            rw [Measure.map_apply_of_aemeasurable
              ((prefixSum_measurable (n + 1)).aemeasurable) measurableSet_Iic]
            rfl

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.2: on a genuine renewal path, the renewal count also equals the
`ENNReal` tail-indicator series of the events `T_(n+1) ≤ t`. -/
private theorem renewalCount_eq_tsum_arrivalIndicatorsENNReal
    (W : ℕ → Ω → ℝ) {t : NNReal} {ω : Ω}
    (h_arrival_strict : StrictMono (fun n ↦ arrivalTime W n ω))
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) :
    (renewalCountingProcess W t ω : ENNReal) =
      ∑' n : ℕ,
        Set.indicator {ω' | arrivalTime W (n + 1) ω' ≤ t} (fun _ ↦ (1 : ENNReal)) ω := by
  let N := renewalCountingProcess W t ω
  have htail_zero :
      ∀ n ∉ Finset.range N,
        Set.indicator {ω' | arrivalTime W (n + 1) ω' ≤ t} (fun _ ↦ (1 : ENNReal)) ω = 0 := by
    intro n hn
    have hN_le : N ≤ n := by
      exact Nat.not_lt.mp (by simpa [N, Finset.mem_range] using hn)
    have harrival_not_le : ¬ arrivalTime W (n + 1) ω ≤ t := by
      intro hle
      have hn_lt :
          n < renewalCountingProcess W t ω :=
        (renewalCountingProcess_lt_iff_arrivalTime_le W h_arrival_strict h_arrival_tendsto).2 hle
      exact (Nat.not_lt.mpr hN_le) hn_lt
    -- Proof comment: beyond the renewal count the corresponding `ENNReal` indicator vanishes.
    simpa [arrivalTime_succ] using harrival_not_le
  calc
    (renewalCountingProcess W t ω : ENNReal) = ∑ n ∈ Finset.range N, (1 : ENNReal) := by
      -- Proof comment: the finite sum of `1`s over `range N_t` is exactly the count `N_t`.
      simp [N]
    _ = ∑ n ∈ Finset.range N,
          Set.indicator {ω' | arrivalTime W (n + 1) ω' ≤ t} (fun _ ↦ (1 : ENNReal)) ω := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hn_lt :
          n < renewalCountingProcess W t ω := by
        simpa [N, Finset.mem_range] using hn
      have harrival_le :
          arrivalTime W (n + 1) ω ≤ t :=
        (renewalCountingProcess_lt_iff_arrivalTime_le W h_arrival_strict h_arrival_tendsto).1 hn_lt
      -- Proof comment: inside `range N_t`, each `ENNReal` indicator is equal to `1`.
      have hmem : ω ∈ {ω' | arrivalTime W (n + 1) ω' ≤ t} := harrival_le
      rw [Set.indicator_of_mem hmem]
    _ = ∑' n : ℕ,
          Set.indicator {ω' | arrivalTime W (n + 1) ω' ≤ t} (fun _ ↦ (1 : ENNReal)) ω := by
      -- Proof comment: the `ENNReal` indicator family has finite support, so the `tsum` reduces
      -- to the finite prefix sum.
      symm
      exact tsum_eq_sum htail_zero

/-- Helper for Exercise 5.5.2: the nonnegative expectation of the renewal count is the tail sum of
the arrival-time probabilities. -/
private theorem renewalCountingProcess_lintegral_eq_tsum_arrivalTimeMeasure
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P) (t : NNReal) :
    (∫⁻ ω, (renewalCountingProcess X t ω : ENNReal) ∂P) =
      ∑' n : ℕ, P {ω | arrivalTime X (n + 1) ω ≤ t} := by
  have hseries_ae :
      ∀ᵐ ω ∂P,
        (renewalCountingProcess X t ω : ENNReal) =
          ∑' n : ℕ,
            Set.indicator {ω' | arrivalTime X (n + 1) ω' ≤ t} (fun _ ↦ (1 : ENNReal)) ω := by
    filter_upwards
      [ae_arrivalTime_strictMono_and_tendsto_of_iid_unitInterval P X hX_iid hX0_law]
      with ω hω
    exact renewalCount_eq_tsum_arrivalIndicatorsENNReal X hω.1 hω.2
  calc
    (∫⁻ ω, (renewalCountingProcess X t ω : ENNReal) ∂P) =
        ∫⁻ ω,
          ∑' n : ℕ,
            Set.indicator {ω' | arrivalTime X (n + 1) ω' ≤ t} (fun _ ↦ (1 : ENNReal)) ω ∂P := by
          -- Proof comment: replace the renewal count by the almost-sure indicator expansion.
          refine lintegral_congr_ae hseries_ae
    _ = ∑' n : ℕ,
          ∫⁻ ω,
            Set.indicator {ω' | arrivalTime X (n + 1) ω' ≤ t} (fun _ ↦ (1 : ENNReal)) ω ∂P := by
          -- Proof comment: each indicator is a.e. measurable, so the `lintegral` commutes with
          -- the countable sum.
          rw [lintegral_tsum]
          intro n
          refine aemeasurable_const.indicator₀ ?_
          exact nullMeasurableSet_le
            (arrivalTime_aemeasurable_of_iid_unitInterval P X hX_iid hX0_law (n + 1))
            aemeasurable_const
    _ = ∑' n : ℕ, P {ω | arrivalTime X (n + 1) ω ≤ t} := by
          -- Proof comment: the `lintegral` of an indicator of `1` is exactly the measure of the
          -- underlying event, even with only null measurability available.
          refine tsum_congr fun n ↦ ?_
          simpa using
            (lintegral_indicator_one₀
              (μ := P)
              (s := {ω | arrivalTime X (n + 1) ω ≤ t})
              (hs := nullMeasurableSet_le
                (arrivalTime_aemeasurable_of_iid_unitInterval P X hX_iid hX0_law (n + 1))
                aemeasurable_const))

-- Proof sketch: use the tail-sum identity `E[N] = ∑_{n ≥ 0} P(S_{n+1} ≤ t)`, identify the law of
-- each finite partial sum with the Irwin--Hall distribution from the i.i.d. and uniform-law
-- assumptions, compute `P(S_n ≤ t)` by the inclusion-exclusion formula for the Irwin--Hall CDF,
-- and then interchange the resulting finite and infinite sums.
/-- Helper for Exercise 5.5.2: the fixed-`k` coefficient series coming from the Irwin--Hall tail
expansion collapses to a single exponential term, with the `k = 0` case contributing the
exceptional `-1`. -/
private theorem uniformArrivalTailCoefficient_tsum (k : ℕ) (a : ℝ) :
    (∑' n : ℕ, (Nat.choose (n + 1) k : ℝ) * a ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) =
      if k = 0 then Real.exp a - 1 else Real.exp a * a ^ k / (Nat.factorial k : ℝ) := by
  let g : ℕ → ℝ := fun n ↦ (Nat.choose n k : ℝ) * a ^ n / (Nat.factorial n : ℝ)
  have hterm_shift :
      ∀ n : ℕ,
        g (n + k) = (a ^ k / (Nat.factorial k : ℝ)) * (a ^ n / (Nat.factorial n : ℝ)) := by
    -- Proof comment: rewrite the shifted binomial coefficient by factorials so the whole tail is
    -- a constant multiple of the exponential series.
    intro n
    dsimp [g]
    have hchoose :
        (Nat.choose (n + k) k : ℝ) =
          (Nat.factorial (n + k) : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by
      simpa [Nat.add_comm, mul_comm, mul_left_comm, mul_assoc] using
        (Nat.cast_add_choose (K := ℝ) (a := k) (b := n))
    have hkFactorial_ne_zero : (Nat.factorial k : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    have hnFactorial_ne_zero : (Nat.factorial n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    have hnkFactorial_ne_zero : (Nat.factorial (n + k) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n + k)
    rw [hchoose, pow_add, div_eq_mul_inv]
    field_simp [hkFactorial_ne_zero, hnFactorial_ne_zero, hnkFactorial_ne_zero]
  have hsBase : Summable (fun n : ℕ ↦ a ^ n / (Nat.factorial n : ℝ)) :=
    Real.summable_pow_div_factorial a
  have hs_shift : Summable (fun n : ℕ ↦ g (n + k)) := by
    -- Proof comment: the shifted coefficient family is a constant multiple of the exponential
    -- series, so it is summable.
    exact (hsBase.mul_left (a ^ k / (Nat.factorial k : ℝ))).congr
      (fun n ↦ (hterm_shift n).symm)
  have hs : Summable g := (summable_nat_add_iff k).1 hs_shift
  have hfull : (∑' n : ℕ, g n) = Real.exp a * a ^ k / (Nat.factorial k : ℝ) := by
    have hprefix_zero : ∑ i ∈ Finset.range k, g i = 0 := by
      -- Proof comment: the prefix terms vanish because `Nat.choose i k = 0` whenever `i < k`.
      refine Finset.sum_eq_zero ?_
      intro i hi
      dsimp [g]
      have hik : i < k := by
        simpa [Finset.mem_range] using hi
      have hchoose_zero : Nat.choose i k = 0 := Nat.choose_eq_zero_iff.mpr hik
      simp [hchoose_zero]
    calc
      ∑' n : ℕ, g n = ∑ i ∈ Finset.range k, g i + ∑' n : ℕ, g (n + k) := by
        -- Proof comment: split the full series into the zero prefix and the shifted tail.
        symm
        exact Summable.sum_add_tsum_nat_add k hs
      _ = ∑' n : ℕ, g (n + k) := by
        rw [hprefix_zero, zero_add]
      _ = ∑' n : ℕ, (a ^ k / (Nat.factorial k : ℝ)) * (a ^ n / (Nat.factorial n : ℝ)) := by
        refine tsum_congr fun n ↦ hterm_shift n
      _ = (a ^ k / (Nat.factorial k : ℝ)) * ∑' n : ℕ, (a ^ n / (Nat.factorial n : ℝ)) := by
        rw [tsum_mul_left]
      _ = Real.exp a * a ^ k / (Nat.factorial k : ℝ) := by
        have hexp :
            (∑' n : ℕ, a ^ n / (Nat.factorial n : ℝ)) = Real.exp a := by
          simpa [Real.exp_eq_exp_ℝ] using
            (congrArg (fun f : ℝ → ℝ => f a)
              (NormedSpace.exp_eq_tsum_div : NormedSpace.exp = fun x : ℝ =>
                ∑' n : ℕ, x ^ n / (Nat.factorial n : ℝ))).symm
        rw [hexp]
        ring
  have hzero : g 0 = if k = 0 then 1 else 0 := by
    -- Proof comment: removing the zeroth term creates exactly the exceptional `-1` in the
    -- `k = 0` case.
    by_cases hk : k = 0
    · subst hk
      simp [g]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      simp [g, hk, Nat.choose_eq_zero_of_lt hkpos]
  calc
    (∑' n : ℕ, (Nat.choose (n + 1) k : ℝ) * a ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) =
        ∑' n : ℕ, g (n + 1) := by
          simp [g]
    _ = ∑' n : ℕ, g n - g 0 := by
          -- Proof comment: rewrite the shifted series as the full series with its zeroth term
          -- removed.
          have hsplit := Summable.tsum_eq_zero_add hs
          rw [hsplit]
          ring
    _ = Real.exp a * a ^ k / (Nat.factorial k : ℝ) - (if k = 0 then 1 else 0) := by
          rw [hfull, hzero]
    _ = if k = 0 then Real.exp a - 1 else Real.exp a * a ^ k / (Nat.factorial k : ℝ) := by
          by_cases hk : k = 0
          · subst hk
            simp
          · simp [hk]

/-- Helper for Exercise 5.5.2: the fixed-`k` Irwin--Hall coefficient series is summable, so finite
`k`-sums may be interchanged with the outer `tsum`. -/
private theorem uniformArrivalTailCoefficient_summable (k : ℕ) (a : ℝ) :
    Summable
      (fun n : ℕ ↦
        (Nat.choose (n + 1) k : ℝ) * a ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) := by
  by_cases hk : k = 0
  · subst hk
    -- Proof comment: the `k = 0` coefficients are just the exponential tail series.
    simpa using (summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial a)
  · let f : ℕ → ℝ := fun n ↦ (Nat.choose n k : ℝ) * a ^ n / (Nat.factorial n : ℝ)
    have hsBase : Summable (fun n : ℕ ↦ a ^ n / (Nat.factorial n : ℝ)) :=
      Real.summable_pow_div_factorial a
    have hterm_shift :
        ∀ n : ℕ,
          f (n + k) = (a ^ k / (Nat.factorial k : ℝ)) * (a ^ n / (Nat.factorial n : ℝ)) := by
      intro n
      dsimp [f]
      have hchoose :
          (Nat.choose (n + k) k : ℝ) =
            (Nat.factorial (n + k) : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by
        -- Proof comment: rewrite the shifted binomial coefficient by the factorial closed form.
        simpa [Nat.add_comm, mul_comm, mul_left_comm, mul_assoc] using
          (Nat.cast_add_choose (K := ℝ) (a := k) (b := n))
      have hkFactorial_ne_zero : (Nat.factorial k : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero k
      have hnFactorial_ne_zero : (Nat.factorial n : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      have hnkFactorial_ne_zero : (Nat.factorial (n + k) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (n + k)
      rw [hchoose, pow_add, div_eq_mul_inv]
      field_simp [hkFactorial_ne_zero, hnFactorial_ne_zero, hnkFactorial_ne_zero]
    have hs_shift : Summable (fun n : ℕ ↦ f (n + k)) := by
      -- Proof comment: after shifting by `k`, the coefficients are a constant multiple of the
      -- exponential series, so the whole family is summable.
      exact (hsBase.mul_left (a ^ k / (Nat.factorial k : ℝ))).congr
        (fun n ↦ (hterm_shift n).symm)
    have hs : Summable f := (summable_nat_add_iff k).1 hs_shift
    -- Proof comment: the target coefficient family is the `1`-shift of the summable family `f`.
    simpa [f] using (summable_nat_add_iff 1).2 hs

/-- Helper for Exercise 5.5.2: after the deterministic arrival-time probabilities are rewritten in
closed form, the remaining outer `tsum` collapses to the stated finite exponential sum. -/
private theorem uniformArrivalTailSeries_closedForm (t : NNReal) :
    (∑' n : ℕ,
      ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (-1 : ℝ) ^ k * (Nat.choose (n + 1) k : ℝ) * ((t : ℝ) - k) ^ (n + 1) /
          (Nat.factorial (n + 1) : ℝ)) =
      -1 + ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (-1 : ℝ) ^ k * Real.exp ((t : ℝ) - k) * ((t : ℝ) - k) ^ k /
          (Nat.factorial k : ℝ) := by
  let m : ℕ := Nat.floor (t : ℝ)
  let B : ℕ → ℝ := fun k ↦
    (-1 : ℝ) ^ k * Real.exp ((t : ℝ) - k) * ((t : ℝ) - k) ^ k / (Nat.factorial k : ℝ)
  calc
    (∑' n : ℕ,
      ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (-1 : ℝ) ^ k * (Nat.choose (n + 1) k : ℝ) * ((t : ℝ) - k) ^ (n + 1) /
          (Nat.factorial (n + 1) : ℝ)) =
        ∑ k ∈ Finset.range (m + 1),
          ∑' n : ℕ,
            (-1 : ℝ) ^ k * (Nat.choose (n + 1) k : ℝ) * ((t : ℝ) - k) ^ (n + 1) /
              (Nat.factorial (n + 1) : ℝ) := by
          -- Proof comment: commute the finite `k`-sum with the outer `tsum`.
          simpa [m] using
            (Summable.tsum_finsetSum
              (s := Finset.range (m + 1))
              (f := fun k n : ℕ ↦
                (-1 : ℝ) ^ k * (Nat.choose (n + 1) k : ℝ) * ((t : ℝ) - k) ^ (n + 1) /
                  (Nat.factorial (n + 1) : ℝ))
              (fun k hk ↦
                by
                  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
                    (uniformArrivalTailCoefficient_summable k ((t : ℝ) - k)).mul_left
                      ((-1 : ℝ) ^ k)))
    _ = ∑ k ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ k *
            (∑' n : ℕ,
              (Nat.choose (n + 1) k : ℝ) * ((t : ℝ) - k) ^ (n + 1) /
                (Nat.factorial (n + 1) : ℝ)) := by
          -- Proof comment: pull the constant sign factor out of each inner series.
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hmul :
              (∑' n : ℕ,
                (-1 : ℝ) ^ k *
                  ((Nat.choose (n + 1) k : ℝ) * ((t : ℝ) - k) ^ (n + 1) /
                    (Nat.factorial (n + 1) : ℝ))) =
                (-1 : ℝ) ^ k *
                  ∑' n : ℕ,
                    (Nat.choose (n + 1) k : ℝ) * ((t : ℝ) - k) ^ (n + 1) /
                      (Nat.factorial (n + 1) : ℝ) := by
            rw [tsum_mul_left]
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    _ = ∑ k ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ k *
            (if k = 0 then Real.exp ((t : ℝ) - k) - 1 else
              Real.exp ((t : ℝ) - k) * ((t : ℝ) - k) ^ k / (Nat.factorial k : ℝ)) := by
          -- Proof comment: evaluate each fixed-`k` coefficient series explicitly.
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [uniformArrivalTailCoefficient_tsum]
    _ = ∑ k ∈ Finset.range m, B (k + 1) + (Real.exp (t : ℝ) - 1) := by
          -- Proof comment: separate the `k = 0` term, which is the only exceptional branch.
          simpa [m, B, Nat.succ_ne_zero, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            (Finset.sum_range_succ'
              (fun k ↦
                (-1 : ℝ) ^ k *
                  (if k = 0 then Real.exp ((t : ℝ) - k) - 1 else
                    Real.exp ((t : ℝ) - k) * ((t : ℝ) - k) ^ k /
                      (Nat.factorial k : ℝ)))
              m)
    _ = -1 + (∑ k ∈ Finset.range m, B (k + 1) + Real.exp (t : ℝ)) := by
          ring
    _ = -1 + ∑ k ∈ Finset.range (m + 1), B k := by
          rw [Finset.sum_range_succ']
          simp [B]
    _ = -1 + ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
          (-1 : ℝ) ^ k * Real.exp ((t : ℝ) - k) * ((t : ℝ) - k) ^ k /
            (Nat.factorial k : ℝ) := by
          simp [m, B]

/-- Helper for Exercise 5.5.2: the finite product of the restricted unit-interval measures is
ambient Lebesgue measure restricted to the cube `[0,1]^m`. -/
private theorem unitIntervalPi_eq_volumeRestrictCube (m : ℕ) :
    Measure.pi (fun _ : Fin m ↦ unitIntervalVolume) =
      (volume : Measure (Fin m → ℝ)).restrict (Set.Icc (fun _ ↦ 0) (fun _ ↦ 1)) := by
  -- Proof comment: rewrite the finite product of restricted one-dimensional measures as the
  -- restriction of the ambient product measure to the product cube, then identify the product
  -- cube with the coordinatewise interval `Set.Icc`.
  calc
    Measure.pi (fun _ : Fin m ↦ unitIntervalVolume) =
        (Measure.pi fun _ : Fin m ↦ (volume : Measure ℝ)).restrict
          (Set.univ.pi fun _ : Fin m ↦ Set.Icc (0 : ℝ) 1) := by
          change Measure.pi (fun _ : Fin m ↦ volume.restrict (Set.Icc (0 : ℝ) 1)) =
            (Measure.pi fun _ : Fin m ↦ (volume : Measure ℝ)).restrict
              (Set.univ.pi fun _ : Fin m ↦ Set.Icc (0 : ℝ) 1)
          simpa using
            (Measure.restrict_pi_pi
              (μ := fun _ : Fin m ↦ (volume : Measure ℝ))
              (s := fun _ : Fin m ↦ Set.Icc (0 : ℝ) 1)).symm
    _ = (volume : Measure (Fin m → ℝ)).restrict (Set.Icc (fun _ ↦ 0) (fun _ ↦ 1)) := by
          rw [← MeasureTheory.volume_pi]
          simp [Set.pi_univ_Icc]

/-- Helper for Exercise 5.5.2: the sum of the subset-indicator vector on `Fin m` is the
cardinality of the subset. -/
private theorem indicatorFinsetOne_sum (m : ℕ) (s : Finset (Fin m)) :
    ∑ i : Fin m, (if i ∈ s then (1 : ℝ) else 0) = s.card := by
  -- Proof comment: extending the constant function `1` by zero outside `s` turns the full
  -- `Fin m`-sum into the sum over the finite subset itself.
  rw [Finset.sum_ite_mem_eq]
  simp

/-- Helper for Exercise 5.5.2: the positive-simplex sublevel set in `Fin m → ℝ` is measurable. -/
private theorem positiveSimplex_measurableSet (m : ℕ) (a : ℝ) :
    MeasurableSet {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} := by
  have hnonneg : MeasurableSet {z : Fin m → ℝ | ∀ i, 0 ≤ z i} := by
    -- Proof comment: the coordinatewise nonnegativity constraint is the finite intersection of
    -- the measurable half-spaces `{z | 0 ≤ z i}`.
    rw [show {z : Fin m → ℝ | ∀ i, 0 ≤ z i} = ⋂ i, {z : Fin m → ℝ | 0 ≤ z i} by
      ext z
      simp]
    exact MeasurableSet.iInter fun i ↦ measurable_pi_apply i measurableSet_Ici
  have hsum : MeasurableSet {z : Fin m → ℝ | ∑ i, z i ≤ a} := by
    -- Proof comment: the prefix-sum map is measurable, so its closed sublevel sets are
    -- measurable as well.
    exact (prefixSum_measurable m) measurableSet_Iic
  -- Proof comment: the simplex sublevel set is the intersection of the nonnegativity region and
  -- the sum sublevel.
  simpa [Set.setOf_and] using hnonneg.inter hsum

/-- Helper for Exercise 5.5.2: translating by the subset-indicator vector identifies the
intersection of the positive simplex with the coordinate constraints `1 ≤ z i` for `i ∈ s` with a
smaller-threshold positive simplex. -/
private theorem positiveSimplex_shift_preimage
    (m : ℕ) (s : Finset (Fin m)) (t : ℝ) :
    let simplex : ℝ → Set (Fin m → ℝ) :=
      fun a ↦ {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a}
    (fun z : Fin m → ℝ ↦ z + fun i ↦ if i ∈ s then 1 else 0) ⁻¹'
        (simplex t ∩ ⋂ i ∈ s, {z : Fin m → ℝ | 1 ≤ z i}) =
      simplex (t - (s.card : ℝ)) := by
  dsimp
  ext z
  constructor
  · intro hz
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter] at hz ⊢
    rcases hz with ⟨hz_simplex, hz_lower⟩
    constructor
    · intro i
      by_cases hi : i ∈ s
      · -- Proof comment: on the constrained coordinates, subtracting the unit shift keeps the
        -- point nonnegative because the translated point lies in `{z | 1 ≤ z i}`.
        have hcoord : 1 ≤ z i + 1 := by
          simpa [hi] using hz_lower i hi
        linarith
      · -- Proof comment: outside `s`, the translation does not change the coordinate.
        simpa [hi] using hz_simplex.1 i
    · -- Proof comment: the shift adds exactly `s.card` to the total sum, so the threshold drops
      -- from `t` to `t - s.card`.
      have hsum_le : ∑ i, (z i + if i ∈ s then 1 else 0) ≤ t := hz_simplex.2
      have hsum_split :
          ∑ i, (z i + if i ∈ s then 1 else 0) =
            ∑ i, z i + ∑ i : Fin m, (if i ∈ s then (1 : ℝ) else 0) := by
        simp [Finset.sum_add_distrib]
      rw [hsum_split, indicatorFinsetOne_sum] at hsum_le
      linarith
  · intro hz
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter] at hz ⊢
    rcases hz with ⟨hz_nonneg, hz_sum⟩
    constructor
    · constructor
      · intro i
        by_cases hi : i ∈ s
        · -- Proof comment: on coordinates in `s`, translation adds `1` to a nonnegative entry.
          have hz_i : 0 ≤ z i := hz_nonneg i
          have : 0 ≤ z i + 1 := by
            linarith
          simpa [hi] using this
        · -- Proof comment: outside `s`, the translated point has the original coordinate.
          simpa [hi] using hz_nonneg i
      · -- Proof comment: adding the indicator vector raises the total sum by exactly `s.card`,
        -- so the translated point stays below the original threshold `t`.
        have hsum_split :
            ∑ i, (z i + if i ∈ s then 1 else 0) =
              ∑ i, z i + ∑ i : Fin m, (if i ∈ s then (1 : ℝ) else 0) := by
          simp [Finset.sum_add_distrib]
        rw [hsum_split, indicatorFinsetOne_sum]
        linarith
    · intro i hi
      -- Proof comment: every shifted coordinate in `s` is at least `1` because the unshifted
      -- coordinate is nonnegative.
      have hz_i : 0 ≤ z i := hz_nonneg i
      have : 1 ≤ z i + 1 := by
        linarith
      simpa [hi] using this

/-- Helper for Exercise 5.5.2: a translated simplex intersection has the same Lebesgue measure as
the smaller-threshold simplex obtained by subtracting the indicator-vector shift. -/
private theorem positiveSimplexShift_real
    (m : ℕ) (s : Finset (Fin m)) (t : ℝ) :
    volume.real
        ({z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ t} ∩
          ⋂ i ∈ s, {z : Fin m → ℝ | 1 ≤ z i}) =
      volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ t - (s.card : ℝ)} := by
  -- Proof comment: translating by the subset-indicator vector preserves Lebesgue measure on
  -- `ℝ^m`, and the previous set-level lemma identifies the translated preimage with the smaller
  -- simplex.
  rw [measureReal_def]
  rw [← measure_preimage_add_right
    (volume : Measure (Fin m → ℝ))
    (fun i : Fin m ↦ if i ∈ s then 1 else 0)
    ({z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ t} ∩
      ⋂ i ∈ s, {z : Fin m → ℝ | 1 ≤ z i})]
  rw [positiveSimplex_shift_preimage]
  rw [measureReal_def]

/-- Helper for Exercise 5.5.2: a positive-simplex sublevel with negative threshold is empty, so
its Lebesgue measure vanishes. -/
private theorem positiveSimplexReal_zero_of_lt_zero
    (m : ℕ) (a : ℝ) (ha : a < 0) :
    volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} = 0 := by
  have hEmpty :
      {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} = (∅ : Set (Fin m → ℝ)) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨hz_nonneg, hz_sum⟩
      have hsum_nonneg : 0 ≤ ∑ i, z i := by
        refine Finset.sum_nonneg ?_
        intro i hi
        exact hz_nonneg i
      linarith
    · simp
  -- Proof comment: once the simplex set is identified with the empty set, its real measure is
  -- zero by definition.
  rw [hEmpty]
  simp

/-- Helper for Exercise 5.5.2: splitting off the first coordinate with
`MeasurableEquiv.piFinSuccAbove` rewrites positive-simplex membership into the head/tail form
needed for the later slicing argument. -/
private theorem positiveSimplex_piFinSuccAbove_symm_mem_iff
    (m : ℕ) (a x : ℝ) (y : Fin m → ℝ) :
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm (x, y) ∈
      {z : Fin (m + 1) → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a}) ↔
      0 ≤ x ∧ (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x := by
  -- Proof comment: `piFinSuccAbove` isolates the zeroth coordinate, and the total sum splits as
  -- the head `x` plus the sum over the remaining `m` coordinates.
  constructor
  · intro hz
    rcases hz with ⟨hz_nonneg, hz_sum⟩
    refine ⟨hz_nonneg 0, ?_, ?_⟩
    · intro i
      simpa using hz_nonneg i.succ
    · simpa [Fin.sum_univ_succ, le_sub_iff_add_le, add_comm, add_left_comm, add_assoc] using hz_sum
  · rintro ⟨hx, hy, hsum⟩
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using hx
      · intro j
        simpa using hy j
    · simpa [Fin.sum_univ_succ, le_sub_iff_add_le, add_comm, add_left_comm, add_assoc] using hsum

/-- Helper for Exercise 5.5.2: transporting the positive simplex through
`MeasurableEquiv.piFinSuccAbove` produces the stable head/tail product-side set used in the
Fubini argument. -/
private theorem positiveSimplexTransport_preimage_eq
    (m : ℕ) (a : ℝ) :
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm ⁻¹'
        {z : Fin (m + 1) → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a}) =
      {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ a - p.1} := by
  -- Proof comment: membership in the transported set is exactly the head/tail simplex condition
  -- from `positiveSimplex_piFinSuccAbove_symm_mem_iff`.
  ext p
  rcases p with ⟨x, y⟩
  simpa [Set.mem_preimage] using positiveSimplex_piFinSuccAbove_symm_mem_iff m a x y

/-- Helper for Exercise 5.5.2: the fiber of the head/tail simplex set over a fixed first
coordinate is either the lower-dimensional simplex with threshold `a - x` or the empty set. -/
private theorem positiveSimplexSection_preimage_eq
    (m : ℕ) (a x : ℝ) :
    Prod.mk x ⁻¹'
        {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ a - p.1} =
      if 0 ≤ x then
        {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}
      else ∅ := by
  -- Proof comment: once the first coordinate is frozen to `x`, only the sign of `x` determines
  -- whether any fiber remains; the surviving fiber is the lower-dimensional simplex section.
  ext y
  by_cases hx : 0 ≤ x
  · simp [hx]
  · simp [hx]

/-- Helper for Exercise 5.5.2: the real volume of a head/tail fiber is the simplex-section
integrand supported on `Set.Icc 0 a`. -/
private theorem positiveSimplexSection_real_eq_indicator
    (m : ℕ) (a x : ℝ) :
    volume.real
        (Prod.mk x ⁻¹'
          {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ a - p.1}) =
      (Set.Icc (0 : ℝ) a).indicator
        (fun x ↦ volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}) x := by
  -- Proof comment: the `x < 0` fibers are empty, the `0 ≤ x ≤ a` fibers are the lower-dimensional
  -- simplices themselves, and the `x > a` fibers have negative threshold so their volume is zero.
  by_cases hx : 0 ≤ x
  · rw [positiveSimplexSection_preimage_eq, if_pos hx]
    by_cases hxa : x ≤ a
    · rw [Set.indicator_of_mem (by exact ⟨hx, hxa⟩)]
    · have hax : a - x < 0 := by
        linarith
      have hx_not_mem : x ∉ Set.Icc (0 : ℝ) a := by
        simp [Set.mem_Icc, hx, hxa]
      rw [positiveSimplexReal_zero_of_lt_zero m (a - x) hax]
      rw [Set.indicator_of_notMem hx_not_mem]
  · rw [positiveSimplexSection_preimage_eq, if_neg hx]
    have hx_not_mem : x ∉ Set.Icc (0 : ℝ) a := by
      simp [Set.mem_Icc, hx]
    rw [Set.indicator_of_notMem hx_not_mem]
    simp

/-- Helper for Exercise 5.5.2: slicing the `(m + 1)`-dimensional positive simplex by its first
coordinate turns its real volume into a one-dimensional interval integral of the lower-dimensional
simplex sections. -/
private theorem positiveSimplexReal_succ_eq_intervalIntegral
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    volume.real {z : Fin (m + 1) → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} =
      ∫ x in 0..a,
        volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x} := by
  let simplex : Set (Fin (m + 1) → ℝ) :=
    {z : Fin (m + 1) → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a}
  let headTailSet : Set (ℝ × (Fin m → ℝ)) :=
    {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ a - p.1}
  let e : (ℝ × (Fin m → ℝ)) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm
  have hem : MeasurePreserving e := by
    exact (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm _
  have hsimplex : MeasurableSet simplex := by
    -- Proof comment: the ambient simplex sublevel is measurable by the earlier finite-dimensional
    -- simplex measurability lemma.
    simpa [simplex] using positiveSimplex_measurableSet (m + 1) a
  have htransport : e ⁻¹' simplex = headTailSet := by
    -- Proof comment: freeze the product-side transport once so the main proof never unfolds
    -- `piFinSuccAbove` again.
    simpa [e, simplex, headTailSet] using positiveSimplexTransport_preimage_eq m a
  have hheadTail : MeasurableSet headTailSet := by
    -- Proof comment: the transported head/tail set is measurable because it is the preimage of
    -- the measurable simplex under the measurable equivalence.
    rw [← htransport]
    exact hsimplex.preimage e.measurable
  have hsimplex_subset_box :
      simplex ⊆ Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ a) := by
    -- Proof comment: each simplex coordinate is nonnegative and bounded by the full coordinate
    -- sum, which itself is bounded by `a`.
    intro z hz
    rcases hz with ⟨hz_nonneg, hz_sum⟩
    refine ⟨hz_nonneg, ?_⟩
    intro i
    have hcoord_le_sum : z i ≤ ∑ j, z j := by
      simpa using Finset.single_le_sum (fun j _ ↦ hz_nonneg j) (Finset.mem_univ i)
    linarith
  have hboxFinite :
      (volume : Measure (Fin (m + 1) → ℝ)) (Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ a)) ≠ ⊤ := by
    -- Proof comment: the enclosing box `[0,a]^(m+1)` has finite Lebesgue volume.
    rw [Real.volume_Icc_pi]
    simp
  have hsimplexFinite : (volume : Measure (Fin (m + 1) → ℝ)) simplex ≠ ⊤ :=
    measure_ne_top_of_subset hsimplex_subset_box hboxFinite
  have hheadTailFinite : (volume : Measure (ℝ × (Fin m → ℝ))) headTailSet ≠ ⊤ := by
    -- Proof comment: transport through the volume-preserving equivalence preserves the simplex's
    -- finite measure.
    rw [← htransport, ← Measure.map_apply e.measurable hsimplex, hem.map_eq]
    exact hsimplexFinite
  have hindicator :
      Integrable (headTailSet.indicator (fun _ : ℝ × (Fin m → ℝ) ↦ (1 : ℝ)))
        (volume : Measure (ℝ × (Fin m → ℝ))) := by
    -- Proof comment: the indicator of a measurable finite-measure set is integrable.
    exact (integrableOn_const hheadTailFinite).integrable_indicator hheadTail
  have hsection_indicator :
      ∀ x : ℝ,
        ∫ y, headTailSet.indicator (fun _ : ℝ × (Fin m → ℝ) ↦ (1 : ℝ)) (x, y)
            ∂(volume : Measure (Fin m → ℝ)) =
          volume.real (Prod.mk x ⁻¹' headTailSet) := by
    intro x
    have hsection_eq :
        (fun y : Fin m → ℝ ↦ headTailSet.indicator (fun _ : ℝ × (Fin m → ℝ) ↦ (1 : ℝ)) (x, y)) =
          (Prod.mk x ⁻¹' headTailSet).indicator (fun _ : Fin m → ℝ ↦ (1 : ℝ)) := by
      -- Proof comment: evaluating the product-side indicator at fixed `x` is exactly the
      -- indicator of the `x`-fiber.
      funext y
      simp [Set.indicator, Set.mem_preimage]
    have hsection_meas :
        MeasurableSet (Prod.mk x ⁻¹' headTailSet) := by
      -- Proof comment: the section formula is explicit, so its measurability reduces to the
      -- measurable simplex sections and the empty-set branch.
      rw [show Prod.mk x ⁻¹' headTailSet =
          Prod.mk x ⁻¹'
            {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ a - p.1} by
          rfl]
      rw [positiveSimplexSection_preimage_eq]
      by_cases hx : 0 ≤ x
      · simpa [hx] using positiveSimplex_measurableSet m (a - x)
      · simp [hx]
    simpa [hsection_eq] using
      (integral_indicator_one
        (μ := (volume : Measure (Fin m → ℝ)))
        (s := Prod.mk x ⁻¹' headTailSet)
        hsection_meas)
  have hsection_interval :
      ∀ x : ℝ,
        volume.real (Prod.mk x ⁻¹' headTailSet) =
          (Set.Icc (0 : ℝ) a).indicator
            (fun x ↦ volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}) x := by
    -- Proof comment: package the fiber volume into the exact outer integrand supported on
    -- `[0,a]`.
    intro x
    simpa [headTailSet] using positiveSimplexSection_real_eq_indicator m a x
  have hinterval :
      ∫ x in Set.Ioc (0 : ℝ) a,
          volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}
            ∂(volume : Measure ℝ) =
        ∫ x in 0..a,
          volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x} := by
    -- Proof comment: convert the outer set integral on the half-open interval to the standard
    -- interval integral over `0..a`.
    have htmp :
        ∫ x in 0..a,
            volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}
              ∂(volume : Measure ℝ) =
          ∫ x in Set.uIoc (0 : ℝ) a,
            volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}
              ∂(volume : Measure ℝ) := by
      rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
      simp [ha]
    simpa [Set.uIoc_of_le ha] using htmp.symm
  -- Route correction: replace the earlier `Measure.prod_apply`/`ENNReal.toReal` approach by a
  -- transported indicator integral, then apply Fubini once and rewrite the fibers explicitly.
  calc
    volume.real simplex = ∫ z, simplex.indicator (fun _ : Fin (m + 1) → ℝ ↦ (1 : ℝ)) z
        ∂(volume : Measure (Fin (m + 1) → ℝ)) := by
          simpa using
            (integral_indicator_one
              (μ := (volume : Measure (Fin (m + 1) → ℝ)))
              (s := simplex)
              hsimplex).symm
    _ =
        ∫ p,
          simplex.indicator (fun _ : Fin (m + 1) → ℝ ↦ (1 : ℝ)) (e p)
            ∂(volume : Measure (ℝ × (Fin m → ℝ))) := by
          rw [← hem.integral_comp' (simplex.indicator
            (fun _ : Fin (m + 1) → ℝ ↦ (1 : ℝ)))]
    _ =
        ∫ p,
          headTailSet.indicator (fun _ : ℝ × (Fin m → ℝ) ↦ (1 : ℝ)) p
            ∂(volume : Measure (ℝ × (Fin m → ℝ))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
          have hpiff : e p ∈ simplex ↔ p ∈ headTailSet := by
            rcases p with ⟨x, y⟩
            simpa [e, simplex, headTailSet] using
              positiveSimplex_piFinSuccAbove_symm_mem_iff m a x y
          by_cases hp : p ∈ headTailSet
          · have hpe : e p ∈ simplex := hpiff.mpr hp
            simp [Set.indicator, hp, hpe]
          · have hpe : e p ∉ simplex := by
              intro hpe
              exact hp (hpiff.mp hpe)
            simp [Set.indicator, hp, hpe]
    _ =
        ∫ x, ∫ y,
          headTailSet.indicator (fun _ : ℝ × (Fin m → ℝ) ↦ (1 : ℝ)) (x, y)
            ∂(volume : Measure (Fin m → ℝ)) ∂(volume : Measure ℝ) := by
          rw [Measure.volume_eq_prod, integral_prod _ hindicator]
    _ = ∫ x, volume.real (Prod.mk x ⁻¹' headTailSet) ∂(volume : Measure ℝ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall hsection_indicator)
    _ =
        ∫ x,
          (Set.Icc (0 : ℝ) a).indicator
            (fun x ↦ volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}) x
            ∂(volume : Measure ℝ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall hsection_interval)
    _ =
        ∫ x in Set.Icc (0 : ℝ) a,
          volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}
            ∂(volume : Measure ℝ) := by
          rw [integral_indicator measurableSet_Icc]
    _ =
        ∫ x in Set.Ioc (0 : ℝ) a,
          volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}
            ∂(volume : Measure ℝ) := by
          rw [integral_Icc_eq_integral_Ioc]
    _ =
        ∫ x in 0..a,
          volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x} := hinterval

/-- Helper for Exercise 5.5.2: the `m`-dimensional positive simplex with threshold `a ≥ 0` has
real volume `a^m / m!`. -/
private theorem positiveSimplexReal_eq_pow_div_factorial
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} =
      a ^ m / (Nat.factorial m : ℝ) := by
  induction m generalizing a with
  | zero =>
      -- Proof comment: in dimension `0`, the simplex is the unique point, whose volume is `1`.
      have hset :
          {z : Fin 0 → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} = Set.univ := by
        ext z
        simp [ha]
      rw [hset]
      have huniv :
          (Set.univ : Set (Fin 0 → ℝ)) =
            Set.Icc (fun _ : Fin 0 ↦ (0 : ℝ)) (fun _ : Fin 0 ↦ (1 : ℝ)) := by
        ext z
        simp
      rw [huniv, measureReal_def, Real.volume_Icc_pi]
      simp
  | succ m hm =>
      rw [positiveSimplexReal_succ_eq_intervalIntegral m a ha]
      have hsection :
          ∀ᵐ x ∂(volume : Measure ℝ),
            x ∈ Set.uIoc (0 : ℝ) a →
              volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x} =
                (a - x) ^ m / (Nat.factorial m : ℝ) := by
        -- Proof comment: every section over the interval `0 < x ≤ a` has a nonnegative
        -- threshold, so the induction hypothesis applies pointwise.
        filter_upwards with x hx
        have hx' : x ∈ Set.Ioc (0 : ℝ) a := by
          simpa [Set.uIoc_of_le ha] using hx
        exact hm (a - x) (by linarith [hx'.2])
      rw [intervalIntegral.integral_congr_ae hsection]
      have hcomp :
          ∫ x in 0..a, (a - x) ^ m = ∫ x in 0..a, x ^ m := by
        simpa using
          (intervalIntegral.integral_comp_sub_left (f := fun x : ℝ ↦ x ^ m) (a := (0 : ℝ))
            (b := a) a)
      calc
        ∫ x in 0..a, (a - x) ^ m / (Nat.factorial m : ℝ) =
            (∫ x in 0..a, (a - x) ^ m) / (Nat.factorial m : ℝ) := by
              rw [intervalIntegral.integral_div]
        _ = (∫ x in 0..a, x ^ m) / (Nat.factorial m : ℝ) := by
              rw [hcomp]
        _ = (a ^ (m + 1) / (m + 1 : ℝ)) / (Nat.factorial m : ℝ) := by
              rw [integral_pow]
              ring
        _ = a ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
              have hm1_ne : (m + 1 : ℝ) ≠ 0 := by
                exact_mod_cast Nat.succ_ne_zero m
              have hfact_ne : (Nat.factorial m : ℝ) ≠ 0 := by
                exact_mod_cast Nat.factorial_ne_zero m
              rw [Nat.factorial_succ, Nat.cast_mul]
              field_simp [hm1_ne, hfact_ne]
              rw [Nat.cast_add, Nat.cast_one]

/-- Helper for Exercise 5.5.2: the open unit cube is the complement of the union of the
coordinatewise bad half-spaces `{z | 1 ≤ z i}`. -/
private theorem unitCubeOpen_eq_diff_badCoords (m : ℕ) :
    (Set.univ.pi fun _ : Fin m ↦ Set.Iio (1 : ℝ)) =
      (Set.univ : Set (Fin m → ℝ)) \
        ⋃ i ∈ (Finset.univ : Finset (Fin m)), {z : Fin m → ℝ | 1 ≤ z i} := by
  -- Proof comment: every coordinate lies in `Iio 1` exactly when no coordinate lies in the bad
  -- half-space `Ici 1`.
  ext z
  simp

/-- Helper for Exercise 5.5.2: inside the positive simplex, replacing the closed upper cube face
`z i ≤ 1` by the open face `z i < 1` does not change the ambient real volume. -/
private theorem positiveSimplexClosedUpperCube_real (m : ℕ) (a : ℝ) :
    volume.real
        ({z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} ∩
          Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ 1)) =
      volume.real
        ({z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} ∩
          Set.univ.pi (fun _ : Fin m ↦ Set.Iio (1 : ℝ))) := by
  let simplex : Set (Fin m → ℝ) := {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a}
  have hclosed :
      simplex ∩ Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ 1) =
        simplex ∩ Set.Iic (fun _ : Fin m ↦ (1 : ℝ)) := by
    -- Proof comment: simplex membership already contains the lower-coordinate inequalities
    -- `0 ≤ z i`, so intersecting with the closed cube only adds the upper bounds `z i ≤ 1`.
    ext z
    constructor
    · intro hz
      rcases hz with ⟨hz_simplex, hz_cube⟩
      exact ⟨hz_simplex, fun i ↦ hz_cube.2 i⟩
    · intro hz
      rcases hz with ⟨hz_simplex, hz_upper⟩
      exact ⟨hz_simplex, ⟨hz_simplex.1, hz_upper⟩⟩
  have hcube_ae :
      Set.univ.pi (fun _ : Fin m ↦ Set.Iio (1 : ℝ)) =ᵐ[(volume : Measure (Fin m → ℝ))]
        Set.Iic (fun _ : Fin m ↦ (1 : ℝ)) := by
    -- Proof comment: product Lebesgue measure does not see the upper boundary of the cube.
    simpa [MeasureTheory.volume_pi] using
      (Measure.univ_pi_Iio_ae_eq_Iic
        (μ := fun _ : Fin m ↦ (volume : Measure ℝ))
        (f := fun _ : Fin m ↦ (1 : ℝ)))
  have hinter_ae :
      (Set.inter simplex (Set.univ.pi (fun _ : Fin m ↦ Set.Iio (1 : ℝ)))) =ᵐ[
          (volume : Measure (Fin m → ℝ))]
        (Set.inter simplex (Set.Iic (fun _ : Fin m ↦ (1 : ℝ)))) :=
    (ae_eq_refl simplex).inter hcube_ae
  -- Proof comment: after intersecting with the simplex, the closed and open upper-cube spellings
  -- are almost everywhere equal, so their real volumes coincide.
  calc
    volume.real (simplex ∩ Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ 1)) =
        volume.real (simplex ∩ Set.Iic (fun _ : Fin m ↦ (1 : ℝ))) := by
          rw [hclosed]
    _ = volume.real (simplex ∩ Set.univ.pi (fun _ : Fin m ↦ Set.Iio (1 : ℝ))) := by
          simpa [measureReal_def] using
            congrArg ENNReal.toReal (measure_congr hinter_ae).symm

/-- Helper for Exercise 5.5.2: after normalizing the product law to ambient volume, the cube
sublevel becomes a finite alternating sum of shifted positive-simplex volumes. -/
private theorem unitIntervalPrefixSumSublevel_real_as_simplexMeasureSum (m : ℕ) (t : NNReal) :
    (Measure.pi (fun _ : Fin m ↦ unitIntervalVolume)).real {z | ∑ i, z i ≤ (t : ℝ)} =
      ∑ k ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) *
          volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ (t : ℝ) - k} := by
  let simplex : Set (Fin m → ℝ) := {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ (t : ℝ)}
  let bad : Fin m → Set (Fin m → ℝ) := fun i ↦ {z : Fin m → ℝ | 1 ≤ z i}
  let μ : Measure (Fin m → ℝ) := (volume : Measure (Fin m → ℝ)).restrict simplex
  have hprefixMeas : MeasurableSet {z : Fin m → ℝ | ∑ i, z i ≤ (t : ℝ)} :=
    (prefixSum_measurable m) measurableSet_Iic
  have hbadMeas : ∀ i : Fin m, MeasurableSet (bad i) := by
    -- Proof comment: each bad-coordinate half-space is a measurable coordinate projection
    -- preimage of `Ici 1`.
    intro i
    exact measurable_pi_apply i measurableSet_Ici
  have hUnionMeas :
      MeasurableSet (⋃ i ∈ (Finset.univ : Finset (Fin m)), bad i) := by
    -- Proof comment: the bad-coordinate union is finite, so measurability is preserved.
    exact Finset.measurableSet_biUnion _ fun i _ ↦ hbadMeas i
  have hsimplex_subset_box :
      simplex ⊆ Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ (t : ℝ)) := by
    intro z hz
    rcases hz with ⟨hz_nonneg, hz_sum⟩
    refine ⟨hz_nonneg, ?_⟩
    intro i
    have hcoord_le_sum : z i ≤ ∑ j, z j := by
      simpa using
        Finset.single_le_sum (fun j _ ↦ hz_nonneg j) (Finset.mem_univ i)
    linarith
  have hboxFinite :
      ((volume : Measure (Fin m → ℝ))
        (Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ (t : ℝ)))) ≠ ⊤ := by
    -- Proof comment: the ambient cube `[0,t]^m` has finite product Lebesgue measure.
    rw [Real.volume_Icc_pi]
    simp
  have hsimplexFinite : (volume : Measure (Fin m → ℝ)) simplex ≠ ⊤ :=
    measure_ne_top_of_subset hsimplex_subset_box hboxFinite
  letI : IsFiniteMeasure μ := by
    -- Proof comment: the restricted simplex measure is finite because the simplex sits inside the
    -- finite cube `[0,t]^m`.
    refine isFiniteMeasure_restrict.2 ?_
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using hsimplexFinite
  have hpowSplit :
      ∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
          (-1 : ℝ) ^ s.card * μ.real (⋂ i ∈ s, bad i) =
        μ.real (Set.univ : Set (Fin m → ℝ)) +
          ∑ s ∈ ((Finset.univ : Finset (Fin m)).powerset.filter Finset.Nonempty),
            (-1 : ℝ) ^ s.card * μ.real (⋂ i ∈ s, bad i) := by
    -- Proof comment: split the powerset sum into the empty subset term and the nonempty
    -- remainder that appears in inclusion-exclusion.
    calc
      ∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
          (-1 : ℝ) ^ s.card * μ.real (⋂ i ∈ s, bad i) =
          ∑ s ∈ ((Finset.univ : Finset (Fin m)).powerset.filter Finset.Nonempty),
            (-1 : ℝ) ^ s.card * μ.real (⋂ i ∈ s, bad i) +
              ∑ s ∈ ((Finset.univ : Finset (Fin m)).powerset.filter fun s ↦ ¬ Finset.Nonempty s),
                (-1 : ℝ) ^ s.card * μ.real (⋂ i ∈ s, bad i) := by
            simpa using
              (Finset.sum_filter_add_sum_filter_not
                (s := (Finset.univ : Finset (Fin m)).powerset)
                (p := Finset.Nonempty)
                (f := fun s ↦ (-1 : ℝ) ^ s.card * μ.real (⋂ i ∈ s, bad i))).symm
      _ = μ.real (Set.univ : Set (Fin m → ℝ)) +
            ∑ s ∈ ((Finset.univ : Finset (Fin m)).powerset.filter Finset.Nonempty),
              (-1 : ℝ) ^ s.card * μ.real (⋂ i ∈ s, bad i) := by
            rw [add_comm]
            have hempty :
                ∑ s ∈ ((Finset.univ : Finset (Fin m)).powerset.filter fun s ↦ ¬ Finset.Nonempty s),
                    (-1 : ℝ) ^ s.card * μ.real (⋂ i ∈ s, bad i) =
                  μ.real (Set.univ : Set (Fin m → ℝ)) := by
              rw [show
                  ((Finset.univ : Finset (Fin m)).powerset.filter fun s ↦ ¬ Finset.Nonempty s) =
                    ({∅} : Finset (Finset (Fin m))) by
                  ext s
                  simp]
              simp
            rw [hempty]
  have hnegNonemptySum :
      -∑ s ∈ ((Finset.univ : Finset (Fin m)).powerset.filter Finset.Nonempty),
          (-1 : ℝ) ^ (s.card + 1) * μ.real (⋂ i ∈ s, bad i) =
        ∑ s ∈ ((Finset.univ : Finset (Fin m)).powerset.filter Finset.Nonempty),
          (-1 : ℝ) ^ s.card * μ.real (⋂ i ∈ s, bad i) := by
    -- Proof comment: negating the inclusion-exclusion sum removes exactly one factor of `-1`.
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro s hs
    calc
      -(((-1 : ℝ) ^ (s.card + 1)) * μ.real (⋂ i ∈ s, bad i)) =
          -((((-1 : ℝ) ^ s.card) * (-1)) * μ.real (⋂ i ∈ s, bad i)) := by
            rw [pow_succ]
      _ = (-1 : ℝ) ^ s.card * μ.real (⋂ i ∈ s, bad i) := by
            ring
  have hGoodMeas :
      MeasurableSet
        ((Set.univ : Set (Fin m → ℝ)) \
          ⋃ i ∈ (Finset.univ : Finset (Fin m)), bad i) := by
    -- Proof comment: the good-coordinate region is the complement of a finite measurable union.
    exact MeasurableSet.univ.diff hUnionMeas
  have hprefixCubeEq :
      ({z : Fin m → ℝ | ∑ i, z i ≤ (t : ℝ)} ∩ Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ 1)) =
        simplex ∩ Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ 1) := by
    -- Proof comment: on the cube, the lower-coordinate bounds already present in `Icc` produce
    -- the positive-simplex spelling.
    ext z
    constructor
    · intro hz
      rcases hz with ⟨hz_sum, hz_cube⟩
      exact ⟨⟨fun i ↦ hz_cube.1 i, hz_sum⟩, hz_cube⟩
    · intro hz
      exact ⟨hz.1.2, hz.2⟩
  calc
    (Measure.pi (fun _ : Fin m ↦ unitIntervalVolume)).real {z : Fin m → ℝ | ∑ i, z i ≤ (t : ℝ)} =
        volume.real (simplex ∩ Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ 1)) := by
          rw [unitIntervalPi_eq_volumeRestrictCube m, measureReal_def]
          rw [Measure.restrict_apply hprefixMeas, measureReal_def]
          -- Proof comment: intersecting the sum sublevel with the cube is exactly the same as
          -- intersecting the positive simplex with the cube.
          exact congrArg ENNReal.toReal
            (congrArg (fun s : Set (Fin m → ℝ) => (volume : Measure (Fin m → ℝ)) s) hprefixCubeEq)
    _ = volume.real (simplex ∩ Set.univ.pi (fun _ : Fin m ↦ Set.Iio (1 : ℝ))) := by
          -- Proof comment: switch from the closed to the open upper cube, which is the spelling
          -- matched by the bad-coordinate complement.
          exact positiveSimplexClosedUpperCube_real m (t : ℝ)
    _ = volume.real
          (simplex ∩
            ((Set.univ : Set (Fin m → ℝ)) \
              ⋃ i ∈ (Finset.univ : Finset (Fin m)), bad i)) := by
          rw [unitCubeOpen_eq_diff_badCoords]
    _ = μ.real
          ((Set.univ : Set (Fin m → ℝ)) \
            ⋃ i ∈ (Finset.univ : Finset (Fin m)), bad i) := by
          -- Proof comment: move the simplex intersection into the measure by passing to the
          -- restricted simplex measure exactly once.
          simpa [μ, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
            (measureReal_restrict_apply
              (μ := (volume : Measure (Fin m → ℝ)))
              (s := simplex)
              (t := (Set.univ : Set (Fin m → ℝ)) \
                ⋃ i ∈ (Finset.univ : Finset (Fin m)), bad i)
              hGoodMeas).symm
    _ = μ.real (Set.univ : Set (Fin m → ℝ)) -
          μ.real (⋃ i ∈ (Finset.univ : Finset (Fin m)), bad i) := by
          -- Proof comment: under the restricted simplex measure, the good region is the
          -- complement of the bad-coordinate union.
          simpa using
            (measureReal_diff
              (μ := μ)
              (s₁ := (Set.univ : Set (Fin m → ℝ)))
              (s₂ := ⋃ i ∈ (Finset.univ : Finset (Fin m)), bad i)
              (by intro x hx; simp)
              hUnionMeas)
    _ = μ.real (Set.univ : Set (Fin m → ℝ)) -
          ∑ s ∈ ((Finset.univ : Finset (Fin m)).powerset.filter Finset.Nonempty),
            (-1 : ℝ) ^ (s.card + 1) * μ.real (⋂ i ∈ s, bad i) := by
          -- Proof comment: inclusion-exclusion expands the bad-coordinate union into powerset
          -- intersections.
          rw [MeasureTheory.measureReal_biUnion_eq_sum_powerset
            (μ := μ)
            (t := (Finset.univ : Finset (Fin m)))
            (s := bad)
            (hs := fun i _ ↦ hbadMeas i)]
    _ = μ.real (Set.univ : Set (Fin m → ℝ)) +
          ∑ s ∈ ((Finset.univ : Finset (Fin m)).powerset.filter Finset.Nonempty),
            (-1 : ℝ) ^ s.card * μ.real (⋂ i ∈ s, bad i) := by
          rw [sub_eq_add_neg, hnegNonemptySum]
    _ =
        ∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
          (-1 : ℝ) ^ s.card * μ.real (⋂ i ∈ s, bad i) := by
          -- Proof comment: reincorporate the empty-subset term, which is exactly `μ.real univ`.
          rw [hpowSplit]
    _ =
        ∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
          (-1 : ℝ) ^ s.card *
            volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ (t : ℝ) - s.card} := by
          -- Proof comment: each powerset intersection is a translated simplex, so it depends only
          -- on the subset cardinality.
          refine Finset.sum_congr rfl ?_
          intro s hs
          congr 1
          have hinterMeas : MeasurableSet (⋂ i ∈ s, bad i) :=
            s.measurableSet_biInter fun i hi ↦ hbadMeas i
          calc
            μ.real (⋂ i ∈ s, bad i) =
                volume.real ((⋂ i ∈ s, bad i) ∩ simplex) := by
                  simpa [μ, Set.inter_comm] using
                    (measureReal_restrict_apply
                      (μ := (volume : Measure (Fin m → ℝ)))
                      (s := simplex)
                      (t := ⋂ i ∈ s, bad i)
                      hinterMeas)
            _ =
                volume.real (simplex ∩ ⋂ i ∈ s, bad i) := by
                  rw [Set.inter_comm]
            _ =
                volume.real
                  {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ (t : ℝ) - s.card} := by
                  simpa [simplex] using positiveSimplexShift_real m s (t : ℝ)
    _ =
        ∑ k ∈ Finset.range (m + 1),
          (Nat.choose m k : ℝ) *
            (((-1 : ℝ) ^ k) *
              volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ (t : ℝ) - k}) := by
          -- Proof comment: regroup the powerset contributions by subset cardinality.
          simpa [Finset.card_univ, nsmul_eq_mul] using
            (Finset.sum_powerset_apply_card
              (f := fun k : ℕ ↦
                (-1 : ℝ) ^ k *
                  volume.real
                    {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ (t : ℝ) - k})
              (x := (Finset.univ : Finset (Fin m))))
    _ =
        ∑ k ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) *
            volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ (t : ℝ) - k} := by
          -- Proof comment: rewrite the grouped cardinality sum into the target coefficient order.
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring

/-- Helper for Exercise 5.5.2: each shifted positive-simplex term in the inclusion-exclusion sum
is either the polynomial simplex volume for a nonnegative threshold or `0` once the threshold is
negative. -/
private theorem shiftedPositiveSimplexReal_eq_if
    (m : ℕ) (t : NNReal) (k : ℕ) :
    volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ (t : ℝ) - k} =
      if k ≤ Nat.floor (t : ℝ) then
        ((t : ℝ) - k) ^ m / (Nat.factorial m : ℝ)
      else 0 := by
  by_cases hk : k ≤ Nat.floor (t : ℝ)
  · -- Proof comment: below the floor cutoff, the shifted threshold stays nonnegative and the
    -- simplex-volume formula applies directly.
    have hnonneg : 0 ≤ (t : ℝ) - k := by
      have hk_real : (k : ℝ) ≤ (t : ℝ) := (Nat.le_floor_iff t.2).1 hk
      linarith
    simp [hk, positiveSimplexReal_eq_pow_div_factorial m ((t : ℝ) - k) hnonneg]
  · -- Proof comment: above the floor cutoff, the shifted threshold is negative, so the simplex is
    -- empty and its real volume vanishes.
    have hfloor_lt : Nat.floor (t : ℝ) < k := lt_of_not_ge hk
    have hneg : (t : ℝ) - k < 0 := by
      have hk_real : (t : ℝ) < (k : ℝ) := (Nat.floor_lt t.2).1 hfloor_lt
      linarith
    simp [hk, positiveSimplexReal_zero_of_lt_zero m ((t : ℝ) - k) hneg]

/-- Helper for Exercise 5.5.2: after rewriting the shifted simplex volumes with the floor cutoff,
the alternating inclusion-exclusion sum truncates exactly to `range (⌊t⌋ + 1)`. -/
private theorem cutoffAlternatingSimplexSum_eq_floorRange
    (m : ℕ) (t : NNReal) :
    ∑ k ∈ Finset.range (m + 1),
      (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) *
        (if k ≤ Nat.floor (t : ℝ) then
          ((t : ℝ) - k) ^ m / (Nat.factorial m : ℝ)
        else 0) =
      ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) * ((t : ℝ) - k) ^ m /
          (Nat.factorial m : ℝ) := by
  by_cases hfloor_le : Nat.floor (t : ℝ) ≤ m
  · -- Proof comment: when `⌊t⌋ ≤ m`, only the initial `⌊t⌋ + 1` terms survive; every later term
    -- in `range (m + 1)` is killed by the cutoff `if`.
    have hsubset :
        Finset.range (Nat.floor (t : ℝ) + 1) ⊆ Finset.range (m + 1) := by
      intro k hk
      exact Finset.mem_range.2 <|
        lt_of_lt_of_le (Finset.mem_range.1 hk) (Nat.succ_le_succ hfloor_le)
    calc
      ∑ k ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) *
            (if k ≤ Nat.floor (t : ℝ) then
              ((t : ℝ) - k) ^ m / (Nat.factorial m : ℝ)
            else 0) =
          ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
            (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) *
              (if k ≤ Nat.floor (t : ℝ) then
                ((t : ℝ) - k) ^ m / (Nat.factorial m : ℝ)
              else 0) := by
                symm
                refine Finset.sum_subset hsubset ?_
                intro k hkbig hksmall
                have hfloor_lt_k : Nat.floor (t : ℝ) < k := by
                  exact Nat.lt_of_succ_le (Nat.not_lt.1 (by simpa using hksmall))
                simp [if_neg (Nat.not_le_of_lt hfloor_lt_k)]
      _ =
          ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
            (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) * ((t : ℝ) - k) ^ m /
              (Nat.factorial m : ℝ) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                have hk_le : k ≤ Nat.floor (t : ℝ) := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
                have hmul :
                    (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) *
                        (((t : ℝ) - k) ^ m / (Nat.factorial m : ℝ)) =
                      (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) * ((t : ℝ) - k) ^ m /
                        (Nat.factorial m : ℝ) := by
                  ring
                simpa [hk_le] using hmul
  · -- Proof comment: when `m < ⌊t⌋`, every term in `range (m + 1)` survives, and the longer
    -- target range contributes only the vanishing tail where `Nat.choose m k = 0`.
    have hm_lt_floor : m < Nat.floor (t : ℝ) := lt_of_not_ge hfloor_le
    have hsubset :
        Finset.range (m + 1) ⊆ Finset.range (Nat.floor (t : ℝ) + 1) := by
      intro k hk
      exact Finset.mem_range.2 <|
        lt_of_lt_of_le (Finset.mem_range.1 hk) (Nat.succ_le_succ (Nat.le_of_lt hm_lt_floor))
    calc
      ∑ k ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) *
            (if k ≤ Nat.floor (t : ℝ) then
              ((t : ℝ) - k) ^ m / (Nat.factorial m : ℝ)
            else 0) =
      ∑ k ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) * ((t : ℝ) - k) ^ m /
              (Nat.factorial m : ℝ) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                have hk_le_m : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
                have hk_le_floor : k ≤ Nat.floor (t : ℝ) :=
                  le_trans hk_le_m (Nat.le_of_lt hm_lt_floor)
                have hmul :
                    (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) *
                        (((t : ℝ) - k) ^ m / (Nat.factorial m : ℝ)) =
                      (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) * ((t : ℝ) - k) ^ m /
                        (Nat.factorial m : ℝ) := by
                  ring
                simpa [hk_le_floor] using hmul
      _ =
          ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
            (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) * ((t : ℝ) - k) ^ m /
              (Nat.factorial m : ℝ) := by
                refine Finset.sum_subset hsubset ?_
                intro k hkbig hksmall
                have hm_lt_k : m < k := by
                  exact Nat.lt_of_succ_le (Nat.not_lt.1 (by simpa using hksmall))
                simp [Nat.choose_eq_zero_of_lt hm_lt_k]

/-- Helper for Exercise 5.5.2: the deterministic Irwin--Hall sublevel formula for the sum of `m`
independent `Uniform[0,1]` coordinates. -/
private theorem unitIntervalPrefixSumSublevel_real (m : ℕ) (t : NNReal) :
    (Measure.pi (fun _ : Fin m ↦ unitIntervalVolume)).real {z | ∑ i, z i ≤ (t : ℝ)} =
      ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) * ((t : ℝ) - k) ^ m /
          (Nat.factorial m : ℝ) := by
  -- Route correction: the product law is now normalized to ambient cube volume before the
  -- inclusion-exclusion step, so the only remaining work is the deterministic simplex-volume
  -- computation in that normal form.
  calc
    (Measure.pi (fun _ : Fin m ↦ unitIntervalVolume)).real {z : Fin m → ℝ | ∑ i, z i ≤ (t : ℝ)} =
        ∑ k ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) *
            volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ (t : ℝ) - k} := by
              rw [unitIntervalPrefixSumSublevel_real_as_simplexMeasureSum m t]
    _ =
        ∑ k ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) *
            (if k ≤ Nat.floor (t : ℝ) then
              ((t : ℝ) - k) ^ m / (Nat.factorial m : ℝ)
            else 0) := by
              -- Proof comment: rewrite each simplex summand using the positive-threshold closed
              -- form below the floor cutoff and the empty-simplex vanishing above it.
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [shiftedPositiveSimplexReal_eq_if m t k]
    _ =
        ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
          (-1 : ℝ) ^ k * (Nat.choose m k : ℝ) * ((t : ℝ) - k) ^ m /
            (Nat.factorial m : ℝ) := cutoffAlternatingSimplexSum_eq_floorRange m t

/-- Helper for Exercise 5.5.2: each arrival-time probability under the i.i.d. unit-interval law
has the finite Irwin--Hall closed form in `ℝ`. -/
private theorem arrivalTimeProbability_toReal_closedForm
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P)
    (t : NNReal) (n : ℕ) :
    (P {ω | arrivalTime X (n + 1) ω ≤ t}).toReal =
      ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (-1 : ℝ) ^ k * (Nat.choose (n + 1) k : ℝ) * ((t : ℝ) - k) ^ (n + 1) /
          (Nat.factorial (n + 1) : ℝ) := by
  -- Proof comment: first rewrite the arrival-time event as a sublevel set for the finite prefix
  -- sum under the product unit-cube law, then apply the deterministic Irwin--Hall formula.
  rw [arrivalTimeEvent_eq_prefixSumSublevel_of_iid_unitInterval P X hX_iid hX0_law t n]
  simpa using unitIntervalPrefixSumSublevel_real (n + 1) t

/-- Helper for Exercise 5.5.2: the real expectation of the renewal count is the `toReal` of the
`ENNReal` arrival-time tail sum already proved above. -/
private theorem renewalCountingProcess_expectation_eq_tsum_arrivalTimeMeasure
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P) (t : NNReal) :
    P[fun ω ↦ (renewalCountingProcess X t ω : ℝ)] =
      (∑' n : ℕ, P {ω | arrivalTime X (n + 1) ω ≤ t}).toReal := by
  have hseries_aemeasurable :
      AEMeasurable
        (fun ω ↦
          ∑' n : ℕ,
            Set.indicator {ω' | arrivalTime X (n + 1) ω' ≤ t} (fun _ ↦ (1 : ENNReal)) ω) P := by
    -- Proof comment: each arrival-time indicator is a.e. measurable, so their `ENNReal` sum is
    -- a.e. measurable as well.
    refine AEMeasurable.ennreal_tsum ?_
    intro n
    refine aemeasurable_const.indicator₀ ?_
    exact nullMeasurableSet_le
      (arrivalTime_aemeasurable_of_iid_unitInterval P X hX_iid hX0_law (n + 1))
      aemeasurable_const
  have hrenewal_aemeasurable :
      AEMeasurable (fun ω ↦ (renewalCountingProcess X t ω : ENNReal)) P := by
    -- Proof comment: reuse the almost-sure indicator-series expansion to transfer
    -- a.e.-measurability to the renewal count.
    refine hseries_aemeasurable.congr ?_
    filter_upwards
      [ae_arrivalTime_strictMono_and_tendsto_of_iid_unitInterval P X hX_iid hX0_law]
      with ω hω
    exact (renewalCount_eq_tsum_arrivalIndicatorsENNReal X hω.1 hω.2).symm
  have hrenewal_finite :
      ∀ᵐ ω ∂P, (renewalCountingProcess X t ω : ENNReal) < ⊤ := by
    -- Proof comment: a natural-valued renewal count is automatically finite as an `ENNReal`.
    exact Filter.Eventually.of_forall fun ω ↦ ENNReal.natCast_lt_top _
  calc
    P[fun ω ↦ (renewalCountingProcess X t ω : ℝ)] =
        (∫⁻ ω, (renewalCountingProcess X t ω : ENNReal) ∂P).toReal := by
          -- Proof comment: convert the nonnegative real expectation to the matching `ENNReal`
          -- integral exactly once.
          simpa using
            (MeasureTheory.integral_toReal
              (μ := P)
              (f := fun ω ↦ (renewalCountingProcess X t ω : ENNReal))
              hrenewal_aemeasurable
              hrenewal_finite)
    _ = (∑' n : ℕ, P {ω | arrivalTime X (n + 1) ω ≤ t}).toReal := by
          rw [renewalCountingProcess_lintegral_eq_tsum_arrivalTimeMeasure P X hX_iid hX0_law t]

-- TODO: the structural prefix is now in place: finite-prefix product laws, the almost-sure
-- renewal-path hypotheses, and the `ENNReal` tail-sum identity for
-- `renewalCountingProcess` are proved locally above. The remaining blocker is the deterministic
-- Irwin--Hall layer: compute the finite-cube sublevel set `{z | ∑ i, z i ≤ t}` in closed form,
-- rewrite each arrival-time probability through that formula, and then assemble the already-proved
-- coefficient identity `uniformArrivalTailCoefficient_tsum` over the finite `k`-sum.
/-- Exercise 5.5.2 in the chapter's canonical owner API: if `X 0, X 1, …` are independent and
each has the uniform law on `[0,1]`, then the expected renewal count at time `t : NNReal` is the
Irwin--Hall closed form. This is the canonical `NNReal`-time version of the textbook formula for
positive real times. -/
theorem uniform_unit_renewal_count_mean
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P)
    (t : NNReal) :
    P[fun ω ↦ (renewalCountingProcess X t ω : ℝ)] =
      -1 + ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (-1 : ℝ) ^ k * Real.exp ((t : ℝ) - k) * ((t : ℝ) - k) ^ k / (Nat.factorial k : ℝ) :=
  by
  calc
    P[fun ω ↦ (renewalCountingProcess X t ω : ℝ)] =
        (∑' n : ℕ, P {ω | arrivalTime X (n + 1) ω ≤ t}).toReal := by
          -- Proof comment: start from the already-proved probabilistic tail-sum identity.
          simpa using
            renewalCountingProcess_expectation_eq_tsum_arrivalTimeMeasure P X hX_iid hX0_law t
    _ = ∑' n : ℕ, (P {ω | arrivalTime X (n + 1) ω ≤ t}).toReal := by
          -- Proof comment: event probabilities are finite under a probability measure, so `toReal`
          -- commutes with the outer `tsum`.
          rw [ENNReal.tsum_toReal_eq]
          intro n
          simp
    _ = ∑' n : ℕ,
          ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
            (-1 : ℝ) ^ k * (Nat.choose (n + 1) k : ℝ) * ((t : ℝ) - k) ^ (n + 1) /
              (Nat.factorial (n + 1) : ℝ) := by
          -- Proof comment: rewrite each arrival-time probability in the deterministic
          -- Irwin--Hall normal form.
          refine tsum_congr ?_
          intro n
          rw [arrivalTimeProbability_toReal_closedForm P X hX_iid hX0_law t n]
    _ = -1 + ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
          (-1 : ℝ) ^ k * Real.exp ((t : ℝ) - k) * ((t : ℝ) - k) ^ k /
            (Nat.factorial k : ℝ) := uniformArrivalTailSeries_closedForm t

/-- Textbook positive-real phrasing of Exercise 5.5.2, obtained by specializing the canonical
`NNReal`-time theorem to `Real.toNNReal T`. -/
theorem uniform_unit_renewal_count_mean_of_pos
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P)
    {T : ℝ} (hT : 0 < T) :
    P[fun ω ↦ (renewalCountingProcess X (Real.toNNReal T) ω : ℝ)] =
      -1 + ∑ k ∈ Finset.range (Nat.floor T + 1),
        (-1 : ℝ) ^ k * Real.exp (T - k) * (T - k) ^ k / (Nat.factorial k : ℝ) := by
  simpa [Real.toNNReal_of_nonneg hT.le] using
    uniform_unit_renewal_count_mean P X hX_iid hX0_law (Real.toNNReal T)
