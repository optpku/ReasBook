/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_33

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u}

/-- The `n`th arrival time attached to a `0`-indexed interarrival sequence `W`, defined as the sum
`W 0 + ⋯ + W (n - 1)`. This is the chapter's canonical `0`-indexed version of the textbook
partial-sum arrival times. -/
def arrivalTime (W : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  ∑ i ∈ Finset.range n, W i

/-- The initial arrival time is `0`. -/
@[simp] theorem arrivalTime_zero (W : ℕ → Ω → ℝ) : arrivalTime W 0 = 0 := by
  -- Proof comment: the empty partial sum is zero.
  simp [arrivalTime]

/-- The next arrival time is obtained by adding the next interarrival time. -/
@[simp] theorem arrivalTime_succ (W : ℕ → Ω → ℝ) (n : ℕ) :
    arrivalTime W (n + 1) = arrivalTime W n + W n := by
  -- Proof comment: split the range sum at its last index.
  simp [arrivalTime, Finset.sum_range_succ]

/-- Helper for Theorem 5.36: splitting at time `m`, the later arrival time `T_(m+n)` is the
initial prefix `T_m` plus the sum over the contiguous block of interarrivals starting at `m`. -/
theorem arrivalTime_add (W : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) :
    arrivalTime W (m + n) ω = arrivalTime W m ω + ∑ i ∈ Finset.range n, W (m + i) ω := by
  -- Proof comment: rewrite the long partial sum as the sum over the first `m` terms plus the
  -- shifted tail block of length `n`.
  simpa [arrivalTime] using (Finset.sum_range_add (fun i ↦ W i ω) m n)

/-- The raw textbook renewal count attached to an interarrival sequence `W`, defined by the
infimum of the indices whose next arrival time strictly exceeds `t`. -/
noncomputable def rawRenewalCountingProcess (W : ℕ → Ω → ℝ) : NNReal → Ω → ℕ :=
  by
    classical
    exact fun t ω ↦ sInf { n : ℕ | t < arrivalTime W (n + 1) ω }

/-- Helper for Theorem 5.36: the raw renewal count shifted by its time-`0` value. This bridge
starts at `0` on every sample path and agrees with the raw textbook count on genuine renewal
paths. -/
noncomputable def normalizedRenewalCountingProcess (W : ℕ → Ω → ℝ) : NNReal → Ω → ℕ :=
  fun t ω ↦ rawRenewalCountingProcess W t ω - rawRenewalCountingProcess W 0 ω

/-- The public renewal counting process is the canonical representative of the textbook renewal
count: on genuine renewal paths, it is the raw `sInf` count, and on the exceptional nongenuine
paths it is reset to the zero process. This is the chapter's `IsPoissonProcess` representative of
the textbook renewal count used in Theorem 5.36. -/
noncomputable def renewalCountingProcess (W : ℕ → Ω → ℝ) : NNReal → Ω → ℕ :=
  by
    classical
    exact fun t ω ↦
      if h_good :
          0 < arrivalTime W 1 ω ∧
            Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop then
        rawRenewalCountingProcess W t ω
      else
        0

/-- On a genuine renewal path, the public renewal count agrees with the raw textbook `sInf`
count. -/
theorem renewalCountingProcess_eq_rawRenewalCountingProcess
    (W : ℕ → Ω → ℝ) {t : NNReal} {ω : Ω}
    (h_first_arrival : 0 < arrivalTime W 1 ω)
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) :
    renewalCountingProcess W t ω = rawRenewalCountingProcess W t ω := by
  -- Proof comment: on a genuine renewal path, the public process takes the raw `sInf` branch.
  rw [renewalCountingProcess]
  split_ifs with h_good
  · rfl
  · exact (h_good ⟨h_first_arrival, h_arrival_tendsto⟩).elim

/-- On a genuine renewal path whose first arrival is strictly after `0`, the normalized
zero-started count agrees with the raw textbook renewal count. -/
theorem normalizedRenewalCountingProcess_eq_rawRenewalCountingProcess
    (W : ℕ → Ω → ℝ) {t : NNReal} {ω : Ω}
    (h_first_arrival : 0 < arrivalTime W 1 ω) :
    normalizedRenewalCountingProcess W t ω = rawRenewalCountingProcess W t ω := by
  have hraw_zero : rawRenewalCountingProcess W 0 ω = 0 := by
    -- Proof comment: the first arrival already occurs strictly after `0`, so `0` belongs to the
    -- defining set and forces the `Nat.sInf` to be zero.
    rw [rawRenewalCountingProcess, Nat.sInf_eq_zero]
    exact Or.inl (by simpa using h_first_arrival)
  -- Proof comment: the normalized count subtracts the raw count at time `0`, which vanishes on
  -- genuine renewal paths.
  simp [normalizedRenewalCountingProcess, hraw_zero]

/-- On a genuine renewal path, the public renewal counting process is exactly the textbook `sInf`
count. -/
@[simp] theorem renewalCountingProcess_eq_sInf
    (W : ℕ → Ω → ℝ) {t : NNReal} {ω : Ω}
    (h_first_arrival : 0 < arrivalTime W 1 ω)
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) :
    renewalCountingProcess W t ω = sInf { n : ℕ | t < arrivalTime W (n + 1) ω } := by
  -- Proof comment: expand the raw renewal count after moving to the genuine-path branch.
  rw [renewalCountingProcess_eq_rawRenewalCountingProcess W h_first_arrival h_arrival_tendsto,
    rawRenewalCountingProcess]

/-- If the arrival times along a sample path diverge to `∞`, then `renewalCountingProcess W t ω`
is characterized by the usual inequalities `T_N(ω) ≤ t < T_(N+1)(ω)`. This is the public bridge
from the concrete `sInf`-definition to the textbook renewal-count inequalities. -/
theorem renewalCountingProcess_spec
    (W : ℕ → Ω → ℝ) {t : NNReal} {ω : Ω}
    (h_first_arrival : 0 < arrivalTime W 1 ω)
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) :
    arrivalTime W (renewalCountingProcess W t ω) ω ≤ t ∧
      t < arrivalTime W (renewalCountingProcess W t ω + 1) ω := by
  let S : Set ℕ := {n : ℕ | t < arrivalTime W (n + 1) ω}
  have h_nonempty : S.Nonempty := by
    obtain ⟨N, hN⟩ := (tendsto_atTop.1 h_arrival_tendsto ((t : ℝ) + 1)).exists
    have hN_pos : 0 < N := by
      by_contra hN_zero
      have ht_nonneg : 0 ≤ (t : ℝ) := t.2
      have hN_eq_zero : N = 0 := Nat.eq_zero_of_not_pos hN_zero
      have hle_zero : (t : ℝ) + 1 ≤ 0 := by
        simpa [hN_eq_zero, arrivalTime] using hN
      linarith
    refine ⟨N - 1, ?_⟩
    have hlt : (t : ℝ) < arrivalTime W N ω := by
      have hle : (t : ℝ) + 1 ≤ arrivalTime W N ω := hN
      linarith
    have hpred : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hN_pos)
    exact (show (t : ℝ) < arrivalTime W ((N - 1) + 1) ω by simpa [hpred] using hlt)
  have hupper :
      t < arrivalTime W (renewalCountingProcess W t ω + 1) ω := by
    -- Proof comment: `Nat.sInf_mem` puts the renewal count itself in the defining strict-inequality
    -- set.
    have hmem : sInf S ∈ S := Nat.sInf_mem h_nonempty
    simpa [S, renewalCountingProcess_eq_sInf W h_first_arrival h_arrival_tendsto] using hmem
  have hlower :
      arrivalTime W (renewalCountingProcess W t ω) ω ≤ t := by
    -- Proof comment: if the lower endpoint were already above `t`, then the predecessor index
    -- would also belong to the defining set, contradicting minimality of the `Nat.sInf`.
    rcases hcount : renewalCountingProcess W t ω with _ | n
    · have ht_nonneg : 0 ≤ (t : ℝ) := t.2
      simpa [arrivalTime_zero] using ht_nonneg
    · by_contra hnot
      have hpred_mem : n ∈ S := by
        have hlt : t < arrivalTime W (n + 1) ω := lt_of_not_ge hnot
        exact hlt
      have hsInf_le : sInf S ≤ n := Nat.sInf_le hpred_mem
      have hsInf_eq : sInf S = n + 1 := by
        calc
          sInf S = renewalCountingProcess W t ω := by
            simpa [S] using
              (renewalCountingProcess_eq_sInf W h_first_arrival h_arrival_tendsto).symm
          _ = n + 1 := hcount
      have : ¬ sInf S ≤ n := by
        rw [hsInf_eq]
        exact Nat.not_succ_le_self n
      exact this hsInf_le
  exact ⟨hlower, hupper⟩

/-- On a sample path whose first arrival is strictly after `0`, the renewal counting process starts
from `0`. -/
theorem renewalCountingProcess_zero
    (W : ℕ → Ω → ℝ) (ω : Ω)
    (h_first_arrival : 0 < arrivalTime W 1 ω) :
    renewalCountingProcess W 0 ω = 0 := by
  by_cases h_good :
      0 < arrivalTime W 1 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop
  · have hraw_zero : rawRenewalCountingProcess W 0 ω = 0 := by
      -- Proof comment: the first arrival occurs after time `0`, so the defining set already
      -- contains `0`.
      rw [rawRenewalCountingProcess, Nat.sInf_eq_zero]
      exact Or.inl (by simpa using h_first_arrival)
    rw [renewalCountingProcess, dif_pos h_good]
    exact hraw_zero
  · -- Proof comment: off the genuine-path branch, the public process is reset to zero by
    -- definition.
    rw [renewalCountingProcess, dif_neg h_good]

/-- Helper for Theorem 5.36: on a genuine renewal path, the counting process is monotone in time.
-/
theorem renewalCountingProcess_mono
    (W : ℕ → Ω → ℝ) {ω : Ω}
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) :
    Monotone (fun t : NNReal ↦ renewalCountingProcess W t ω) := by
  classical
  intro s t hst
  by_cases h_good :
      0 < arrivalTime W 1 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop
  · let S : NNReal → Set ℕ := fun u ↦ {n : ℕ | u < arrivalTime W (n + 1) ω}
    have h_nonempty : ∀ u : NNReal, (S u).Nonempty := by
      intro u
      obtain ⟨N, hN⟩ := (tendsto_atTop.1 h_arrival_tendsto ((u : ℝ) + 1)).exists
      have hN_pos : 0 < N := by
        by_contra hN_zero
        have hu_nonneg : 0 ≤ (u : ℝ) := u.2
        have hN_eq_zero : N = 0 := Nat.eq_zero_of_not_pos hN_zero
        have hle_zero : (u : ℝ) + 1 ≤ 0 := by
          simpa [hN_eq_zero, arrivalTime] using hN
        linarith
      refine ⟨N - 1, ?_⟩
      have hlt : (u : ℝ) < arrivalTime W N ω := by
        have hle : (u : ℝ) + 1 ≤ arrivalTime W N ω := hN
        linarith
      have hpred : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hN_pos)
      exact (show (u : ℝ) < arrivalTime W ((N - 1) + 1) ω by simpa [hpred] using hlt)
    have ht_mem : sInf (S t) ∈ S s := by
      have hsInf_mem : sInf (S t) ∈ S t := Nat.sInf_mem (h_nonempty t)
      have hsInf_lt : t < arrivalTime W (sInf (S t) + 1) ω := hsInf_mem
      have hst_real : (s : ℝ) ≤ t := hst
      exact lt_of_le_of_lt hst_real hsInf_lt
    -- Proof comment: the witnessing index for time `t` still lies in the strict-inequality set
    -- for every earlier time `s`.
    change renewalCountingProcess W s ω ≤ renewalCountingProcess W t ω
    have hs_eq :
        renewalCountingProcess W s ω = rawRenewalCountingProcess W s ω :=
      renewalCountingProcess_eq_rawRenewalCountingProcess W h_good.1 h_good.2
    have ht_eq :
        renewalCountingProcess W t ω = rawRenewalCountingProcess W t ω :=
      renewalCountingProcess_eq_rawRenewalCountingProcess W h_good.1 h_good.2
    rw [hs_eq, ht_eq, rawRenewalCountingProcess, rawRenewalCountingProcess]
    exact Nat.sInf_le ht_mem
  · change
      (if 0 < arrivalTime W 1 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop then
          rawRenewalCountingProcess W s ω
        else 0) ≤
        (if 0 < arrivalTime W 1 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop then
          rawRenewalCountingProcess W t ω
        else 0)
    have h_bad0 : ¬ (0 < W 0 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) := by
      intro h
      apply h_good
      simpa [arrivalTime_succ, arrivalTime_zero] using h
    simp [renewalCountingProcess, arrivalTime_succ, arrivalTime_zero, h_bad0]

/-- Helper for Theorem 5.36: on a genuine renewal path, the counting process equals `n` exactly on
the strip `T_n ≤ t < T_(n+1)`. -/
theorem renewalCountingProcess_eq_iff_arrival_strip
    (W : ℕ → Ω → ℝ) {t : NNReal} {ω : Ω} {n : ℕ}
    (h_arrival_strict : StrictMono (fun m ↦ arrivalTime W m ω))
    (h_arrival_tendsto : Tendsto (fun m ↦ arrivalTime W m ω) atTop atTop) :
    renewalCountingProcess W t ω = n ↔
      arrivalTime W n ω ≤ t ∧ t < arrivalTime W (n + 1) ω := by
  have h_first_arrival : 0 < arrivalTime W 1 ω := by
    -- Proof comment: strict growth from `0` to `1` forces the first arrival time to be positive.
    simpa [arrivalTime_zero] using h_arrival_strict (show 0 < 1 by omega)
  constructor
  · intro hN
    -- Proof comment: apply the strip characterization to the actual renewal count and rewrite
    -- using the prescribed value `n`.
    have h_spec :
        arrivalTime W (renewalCountingProcess W t ω) ω ≤ t ∧
          t < arrivalTime W (renewalCountingProcess W t ω + 1) ω :=
      renewalCountingProcess_spec W h_first_arrival h_arrival_tendsto
    simpa [hN] using
      h_spec
  · intro hn_strip
    let N := renewalCountingProcess W t ω
    have hN_strip :
        arrivalTime W N ω ≤ t ∧ t < arrivalTime W (N + 1) ω :=
      renewalCountingProcess_spec W h_first_arrival h_arrival_tendsto
    have hN_le_n : N ≤ n := by
      by_contra hnot
      have hn_lt : n < N := Nat.lt_of_not_ge hnot
      have hstep : n + 1 ≤ N := Nat.succ_le_of_lt hn_lt
      exact not_lt_of_ge (le_trans (h_arrival_strict.monotone hstep) hN_strip.1) hn_strip.2
    have hn_le_N : n ≤ N := by
      by_contra hnot
      have hN_lt : N < n := Nat.lt_of_not_ge hnot
      have hstep : N + 1 ≤ n := Nat.succ_le_of_lt hN_lt
      exact not_lt_of_ge (le_trans (h_arrival_strict.monotone hstep) hn_strip.1) hN_strip.2
    exact le_antisymm hN_le_n hn_le_N

section

variable [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.36: for a monotone `ℕ`-valued path started at `0`, prescribing all
adjacent increments is equivalent to prescribing all endpoint values by cumulative sums. -/
theorem nat_increment_event_iff_endpoint_counts
    {X k : ℕ → ℕ} (hX0 : X 0 = 0) (hXmono : Monotone X) :
    (∀ i, X (i + 1) - X i = k i) ↔ ∀ j, X j = ∑ i ∈ Finset.range j, k i := by
  constructor
  · intro hk
    intro j
    induction j with
    | zero =>
        -- Proof comment: the endpoint count at `0` is the prescribed zero anchor.
        simp [hX0]
    | succ j ih =>
        -- Proof comment: recover the next endpoint by adding the prescribed increment to the
        -- previous cumulative count.
        rw [Finset.sum_range_succ, ← ih]
        have hle : X j ≤ X (j + 1) := hXmono (Nat.le_succ j)
        have hstep : X (j + 1) = k j + X j := by
          exact (Nat.sub_eq_iff_eq_add hle).1 (hk j)
        rw [hstep, add_comm]
  · intro hX
    intro i
    -- Proof comment: consecutive cumulative sums differ by exactly the next increment.
    rw [hX (i + 1), hX i, Finset.sum_range_succ]
    omega

/-- Helper for Theorem 5.36: every coordinate of the i.i.d. interarrival sequence has the same
exponential law as the distinguished coordinate `W 0`. -/
theorem interarrival_hasLaw_of_iid_exponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ) (n : ℕ) :
    HasLaw (W n) (expMeasure α) μ := by
  -- Proof comment: identical distribution transports the distinguished exponential law to every
  -- coordinate.
  exact (hW_iid.identDistrib 0 n).hasLaw hW0_law

/-- Helper for Theorem 5.36: every finite prefix of the i.i.d. interarrival sequence has the
finite product of exponential laws as its distribution. -/
theorem iid_exponential_prefix_hasLaw_pi
    (μ : Measure Ω) [IsProbabilityMeasure μ] (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ) (n : ℕ) :
    HasLaw (fun ω ↦ fun i : Fin n ↦ W i ω) (Measure.pi (fun _ : Fin n ↦ expMeasure α)) μ := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: finite coordinate vectors are almost everywhere measurable coordinatewise.
    exact aemeasurable_pi_lambda _ fun i : Fin n ↦
      (interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law i).aemeasurable
  · have h_prefix_iIndep : iIndepFun (fun i : Fin n ↦ W i) μ :=
      hW_iid.iIndepFun.precomp Fin.val_injective
    -- Proof comment: the `Fin n`-indexed prefix inherits independence from the ambient i.i.d.
    -- sequence.
    rw [(
      iIndepFun_iff_map_fun_eq_pi_map
        (fun i : Fin n ↦
          (interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law i).aemeasurable)).1
      h_prefix_iIndep]
    have h_marginals :
        (fun i : Fin n ↦ Measure.map (W i) μ) = fun _ : Fin n ↦ expMeasure α := by
      funext i
      exact (interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law i).map_eq
    -- Proof comment: every marginal of the prefix vector is the same exponential law.
    rw [h_marginals]

/-- Helper for Theorem 5.36: every contiguous finite block of the i.i.d. interarrival sequence has
the corresponding finite product exponential law. -/
theorem iid_exponential_contiguous_block_hasLaw_pi
    (μ : Measure Ω) [IsProbabilityMeasure μ] (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ) (a n : ℕ) :
    HasLaw (fun ω ↦ fun i : Fin n ↦ W (a + i) ω)
      (Measure.pi (fun _ : Fin n ↦ expMeasure α)) μ := by
  let Wshift : ℕ → Ω → ℝ := fun i ω ↦ W (a + i) ω
  have hshift_iid : IsIID Wshift μ := by
    refine ⟨hW_iid.iIndepFun.precomp ?_, ?_⟩
    · intro i j hij
      exact Nat.add_left_cancel hij
    · intro i j
      exact hW_iid.identDistrib (a + i) (a + j)
  have hshift0_law : HasLaw (Wshift 0) (expMeasure α) μ := by
    -- Proof comment: the shifted zeroth coordinate is the original coordinate `W a`.
    simpa [Wshift] using interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law a
  -- Proof comment: apply the finite-prefix law to the shifted i.i.d. family.
  simpa [Wshift] using iid_exponential_prefix_hasLaw_pi μ α Wshift hshift_iid hshift0_law n

/-- Helper for Theorem 5.36: every interarrival is almost surely strictly positive under the
exponential-law hypothesis. -/
theorem ae_interarrival_pos_of_iid_exponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    ∀ᵐ ω ∂μ, ∀ n, 0 < W n ω := by
  letI : IsProbabilityMeasure (expMeasure α) := isProbabilityMeasure_expMeasure hα
  have h_pos_exp : ∀ᵐ x ∂expMeasure α, 0 < x := by
    -- Proof comment: the exponential law assigns zero mass to the nonpositive half-line.
    rw [ae_iff]
    have h_nonpos_zero : expMeasure α {x : ℝ | ¬ 0 < x} = 0 := by
      rw [show {x : ℝ | ¬ 0 < x} = Set.Iic 0 by ext x; simp]
      have h_zero_iff :
          (expMeasure α).real (Set.Iic 0) = 0 ↔ expMeasure α (Set.Iic 0) = 0 :=
        measureReal_eq_zero_iff
      apply h_zero_iff.1
      have h_cdf_real : cdf (expMeasure α) 0 = (expMeasure α).real (Set.Iic 0) :=
        ProbabilityTheory.cdf_eq_real (expMeasure α) 0
      rw [← h_cdf_real]
      have hcdf_zero : cdf (expMeasure α) 0 = 0 := by
        simpa using (ProbabilityTheory.cdf_expMeasure_eq hα 0)
      simpa using hcdf_zero
    simpa using h_nonpos_zero
  refine ae_all_iff.2 fun n ↦ ?_
  have hWn_law := interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law n
  -- Proof comment: transport almost-sure positivity through the law of `W n`.
  exact (hWn_law.ae_iff (by fun_prop)).2 h_pos_exp

/-- Helper for Theorem 5.36: the exponential tail above a nonnegative threshold has real mass
`exp (-(θ * t))`. -/
private theorem expMeasure_real_Ioi_eq_exp_of_nonneg {θ t : ℝ} (hθ : 0 < θ) (ht : 0 ≤ t) :
    (expMeasure θ).real (Set.Ioi t) = Real.exp (-(θ * t)) := by
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hIic :
      (expMeasure θ).real (Set.Iic t) = 1 - Real.exp (-(θ * t)) := by
    have h_cdf_real : cdf (expMeasure θ) t = (expMeasure θ).real (Set.Iic t) :=
      ProbabilityTheory.cdf_eq_real (expMeasure θ) t
    rw [← h_cdf_real, ProbabilityTheory.cdf_expMeasure_eq hθ t, if_pos ht]
  calc
    (expMeasure θ).real (Set.Ioi t) = 1 - (expMeasure θ).real (Set.Iic t) := by
      have h_compl :
          (expMeasure θ).real (Set.Iic t)ᶜ = 1 - (expMeasure θ).real (Set.Iic t) :=
        @MeasureTheory.probReal_compl_eq_one_sub ℝ _ (expMeasure θ) (Set.Iic t) _
          measurableSet_Iic
      simpa using h_compl
    _ = Real.exp (-(θ * t)) := by
      rw [hIic]
      ring

/-- Helper for Theorem 5.36: rewrite integration against `expMeasure θ` as integration against its
real-valued density. -/
private theorem integralExpMeasure_eq_integral_density {θ : ℝ} (hθ : 0 < θ) {f : ℝ → ℝ} :
    ∫ x, f x ∂expMeasure θ = ∫ x, exponentialPDFReal θ x * f x := by
  -- Proof comment: unfold `expMeasure` as a `withDensity` measure and simplify the scalar density
  -- on `ℝ`.
  rw [expMeasure, gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul (μ := volume) (f := gammaPDF 1 θ)
      (measurable_gammaPDFReal 1 θ).ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp [gammaPDF, exponentialPDFReal, gammaPDFReal_nonneg zero_lt_one hθ x, smul_eq_mul]

/-- Helper for Theorem 5.36: the exponential tail is multiplicative on nonnegative shifts, which
is the concrete memoryless identity used in the increment-mass computation. -/
private theorem expMeasureRealIoi_add_eq_mul {θ r s : ℝ}
    (hθ : 0 < θ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (expMeasure θ).real (Set.Ioi (r + s)) =
      (expMeasure θ).real (Set.Ioi r) * (expMeasure θ).real (Set.Ioi s) := by
  -- Proof comment: rewrite every tail by the explicit exponential formula, then use
  -- `exp (a + b) = exp a * exp b`.
  rw [expMeasure_real_Ioi_eq_exp_of_nonneg hθ (add_nonneg hr hs)]
  rw [expMeasure_real_Ioi_eq_exp_of_nonneg hθ hr, expMeasure_real_Ioi_eq_exp_of_nonneg hθ hs]
  have hadd : -(θ * (r + s)) = -(θ * r) + -(θ * s) := by
    ring
  rw [hadd, Real.exp_add]

/-- Helper for Theorem 5.36: the finite prefix-sum map on `Fin n → ℝ` is measurable. -/
private theorem prefixSum_measurable (n : ℕ) :
    Measurable (fun z : Fin n → ℝ ↦ ∑ i, z i) := by
  -- Proof comment: a finite sum of measurable coordinate projections is measurable.
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  exact measurable_pi_apply i

/-- Helper for Theorem 5.36: the sum of the indicator vector of a finite subset of `Fin m`
equals the subset cardinality. -/
private theorem indicatorFinsetOne_sum (m : ℕ) (s : Finset (Fin m)) :
    ∑ i : Fin m, (if i ∈ s then (1 : ℝ) else 0) = s.card := by
  -- Proof comment: extending the constant function `1` by zero outside `s` turns the full sum
  -- into the sum over the subset itself.
  rw [Finset.sum_ite_mem_eq]
  simp

/-- Helper for Theorem 5.36: the positive-simplex sublevel in `Fin m → ℝ` is measurable. -/
private theorem positiveSimplex_measurableSet (m : ℕ) (a : ℝ) :
    MeasurableSet {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} := by
  have hnonneg : MeasurableSet {z : Fin m → ℝ | ∀ i, 0 ≤ z i} := by
    -- Proof comment: coordinatewise nonnegativity is a finite intersection of measurable
    -- half-spaces.
    rw [show {z : Fin m → ℝ | ∀ i, 0 ≤ z i} = ⋂ i, {z : Fin m → ℝ | 0 ≤ z i} by
      ext z
      simp]
    exact MeasurableSet.iInter fun i ↦ measurable_pi_apply i measurableSet_Ici
  have hsum : MeasurableSet {z : Fin m → ℝ | ∑ i, z i ≤ a} := by
    -- Proof comment: the sum map is measurable, so its closed sublevel is measurable.
    exact (prefixSum_measurable m) measurableSet_Iic
  -- Proof comment: the simplex is the intersection of the nonnegative orthant with a sum
  -- sublevel.
  simpa [Set.setOf_and] using hnonneg.inter hsum

/-- Helper for Theorem 5.36: translating by the indicator vector of `s` identifies the simplex
intersection with the coordinate lower bounds `1 ≤ z i` as a smaller-threshold simplex. -/
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
      · -- Proof comment: on constrained coordinates, subtracting the unit shift leaves a
        -- nonnegative coordinate because the translated point lies in `{z | 1 ≤ z i}`.
        have hcoord : 1 ≤ z i + 1 := by
          simpa [hi] using hz_lower i hi
        linarith
      · -- Proof comment: outside `s`, the translation does not change the coordinate.
        simpa [hi] using hz_simplex.1 i
    · -- Proof comment: the shift adds exactly `s.card` to the total sum.
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
        · -- Proof comment: outside `s`, the translated coordinate is unchanged.
          simpa [hi] using hz_nonneg i
      · -- Proof comment: adding the indicator vector raises the total sum by `s.card`.
        have hsum_split :
            ∑ i, (z i + if i ∈ s then 1 else 0) =
              ∑ i, z i + ∑ i : Fin m, (if i ∈ s then (1 : ℝ) else 0) := by
          simp [Finset.sum_add_distrib]
        rw [hsum_split, indicatorFinsetOne_sum]
        linarith
    · intro i hi
      -- Proof comment: every shifted coordinate in `s` is at least `1`.
      have hz_i : 0 ≤ z i := hz_nonneg i
      have : 1 ≤ z i + 1 := by
        linarith
      simpa [hi] using this

/-- Helper for Theorem 5.36: the translated simplex intersection has the same real volume as the
smaller-threshold simplex obtained after subtracting the indicator shift. -/
private theorem positiveSimplexShift_real
    (m : ℕ) (s : Finset (Fin m)) (t : ℝ) :
    volume.real
        ({z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ t} ∩
          ⋂ i ∈ s, {z : Fin m → ℝ | 1 ≤ z i}) =
      volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ t - (s.card : ℝ)} := by
  -- Proof comment: translation preserves Lebesgue measure, and the previous lemma identifies the
  -- translated preimage with the smaller simplex.
  rw [measureReal_def]
  rw [← measure_preimage_add_right
    (volume : Measure (Fin m → ℝ))
    (fun i : Fin m ↦ if i ∈ s then 1 else 0)
    ({z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ t} ∩
      ⋂ i ∈ s, {z : Fin m → ℝ | 1 ≤ z i})]
  rw [positiveSimplex_shift_preimage]
  rw [measureReal_def]

/-- Helper for Theorem 5.36: a positive-simplex sublevel with negative threshold is empty, so its
real volume is `0`. -/
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
  -- Proof comment: once the simplex is empty, its real volume vanishes.
  rw [hEmpty]
  simp

/-- Helper for Theorem 5.36: splitting off coordinate `0` with `piFinSuccAbove` rewrites
positive-simplex membership into a head/tail condition. -/
private theorem positiveSimplex_piFinSuccAbove_symm_mem_iff
    (m : ℕ) (a x : ℝ) (y : Fin m → ℝ) :
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm (x, y) ∈
      {z : Fin (m + 1) → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a}) ↔
      0 ≤ x ∧ (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x := by
  -- Proof comment: `piFinSuccAbove` isolates the zeroth coordinate, and the total sum splits as
  -- the head plus the tail sum.
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

/-- Helper for Theorem 5.36: transporting the positive simplex through `piFinSuccAbove` gives the
stable head/tail set used in the slicing argument. -/
private theorem positiveSimplexTransport_preimage_eq
    (m : ℕ) (a : ℝ) :
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm ⁻¹'
        {z : Fin (m + 1) → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a}) =
      {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ a - p.1} := by
  -- Proof comment: this is exactly the membership equivalence from the previous lemma.
  ext p
  rcases p with ⟨x, y⟩
  simpa [Set.mem_preimage] using positiveSimplex_piFinSuccAbove_symm_mem_iff m a x y

/-- Helper for Theorem 5.36: the head/tail simplex fiber over a fixed first coordinate is either
the lower-dimensional simplex with threshold `a - x` or the empty set. -/
private theorem positiveSimplexSection_preimage_eq
    (m : ℕ) (a x : ℝ) :
    Prod.mk x ⁻¹'
        {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ a - p.1} =
      if 0 ≤ x then
        {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}
      else ∅ := by
  -- Proof comment: once the first coordinate is fixed, only the sign of `x` decides whether a
  -- nonempty fiber remains.
  ext y
  by_cases hx : 0 ≤ x
  · simp [hx]
  · simp [hx]

/-- Helper for Theorem 5.36: the real volume of a head/tail fiber is the simplex-section
integrand supported on `Set.Icc 0 a`. -/
private theorem positiveSimplexSection_real_eq_indicator
    (m : ℕ) (a x : ℝ) :
    volume.real
        (Prod.mk x ⁻¹'
          {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ a - p.1}) =
      (Set.Icc (0 : ℝ) a).indicator
        (fun x ↦ volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}) x := by
  -- Proof comment: the `x < 0` fibers are empty, the `0 ≤ x ≤ a` fibers are the lower-dimensional
  -- simplices, and the `x > a` fibers have negative threshold and hence zero volume.
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

/-- Helper for Theorem 5.36: slicing the `(m + 1)`-dimensional positive simplex by its first
coordinate turns its real volume into a one-dimensional interval integral of lower-dimensional
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
    -- Proof comment: the ambient simplex is measurable by the earlier simplex measurability lemma.
    simpa [simplex] using positiveSimplex_measurableSet (m + 1) a
  have htransport : e ⁻¹' simplex = headTailSet := by
    -- Proof comment: freeze the `piFinSuccAbove` transport once so the main proof can stay in the
    -- stable head/tail coordinates.
    simpa [e, simplex, headTailSet] using positiveSimplexTransport_preimage_eq m a
  have hheadTail : MeasurableSet headTailSet := by
    rw [← htransport]
    exact hsimplex.preimage e.measurable
  have hsimplex_subset_box :
      simplex ⊆ Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ a) := by
    -- Proof comment: every coordinate is nonnegative and bounded by the full coordinate sum.
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
    -- Proof comment: transport through the volume-preserving equivalence preserves finite mass.
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
    -- Proof comment: convert the half-open set integral to the standard interval integral.
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
  -- Route correction: use a transported indicator integral and a single Fubini step, then rewrite
  -- the fibers explicitly.
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

/-- Helper for Theorem 5.36: the `m`-dimensional positive simplex with threshold `a ≥ 0` has real
volume `a^m / m!`. -/
private theorem positiveSimplexReal_eq_pow_div_factorial
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} =
      a ^ m / (Nat.factorial m : ℝ) := by
  induction m generalizing a with
  | zero =>
      -- Proof comment: in dimension `0`, the simplex is the unique point, whose real volume is
      -- `1`.
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
        -- Proof comment: every section over `0 < x ≤ a` has a nonnegative threshold, so the
        -- induction hypothesis applies pointwise.
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

/-- Helper for Theorem 5.36: an i.i.d. exponential interarrival sequence almost surely has
strictly increasing arrival times and arrival times diverging to `∞`. -/
private theorem ae_arrivalTime_strictMono_and_tendsto_of_iid_exponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    ∀ᵐ ω ∂μ,
      StrictMono (fun n ↦ arrivalTime W n ω) ∧
        Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop := by
  letI : IsProbabilityMeasure (expMeasure α) := isProbabilityMeasure_expMeasure hα
  letI : IsProbabilityMeasure μ := hW0_law.isProbabilityMeasure
  let F : ℝ → ℝ := Set.indicator (Set.Ioi (1 : ℝ)) (fun _ ↦ (1 : ℝ))
  let Y : ℕ → Ω → ℝ := fun n ω ↦ F (W n ω)
  have hF_meas : Measurable F := by
    -- Proof comment: the large-gap indicator is measurable because `Ioi 1` is measurable.
    simpa [F] using (measurable_indicator_const_iff (1 : ℝ)).2 measurableSet_Ioi
  have hF_law : HasLaw F (Measure.map F (expMeasure α)) (expMeasure α) := by
    exact
      (show MeasurePreserving F (expMeasure α) (Measure.map F (expMeasure α)) from
        ⟨hF_meas, rfl⟩).hasLaw
  have hF_integrable : Integrable F (expMeasure α) := by
    -- Proof comment: the large-gap indicator is bounded by the constant `1`.
    simpa [F] using (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  have hY_iIndep : iIndepFun Y μ := by
    -- Proof comment: independence is preserved under measurable postcomposition.
    simpa [Y] using hW_iid.iIndepFun.comp (fun _ ↦ F) (fun _ ↦ hF_meas)
  have hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ := by
    -- Proof comment: each large-gap indicator has the same law because the interarrivals are
    -- identically distributed.
    intro n
    simpa [Y] using (hW_iid.identDistrib n 0).comp hF_meas
  have hY0_ident : IdentDistrib (Y 0) F μ (expMeasure α) := by
    have hY0_law : HasLaw (Y 0) (Measure.map F (expMeasure α)) μ := by
      -- Proof comment: push the law of `W 0` forward through the indicator map `F`.
      simpa [Y] using hF_law.fun_comp hW0_law
    exact hY0_law.identDistrib hF_law
  have hY0_integrable : Integrable (Y 0) μ := by
    -- Proof comment: integrability transfers across identical distribution.
    exact hY0_ident.integrable_iff.2 hF_integrable
  have hY0_expectation : μ[Y 0] = Real.exp (-(α : ℝ)) := by
    have hα_real : 0 < (α : ℝ) := by
      exact_mod_cast hα
    -- Proof comment: the mean of the large-gap indicator is the exponential tail probability
    -- `P[W 0 > 1] = exp (-α)`.
    calc
      μ[Y 0] = ∫ x, F x ∂expMeasure α := by
        simpa [Y] using hW0_law.integral_comp hF_meas.aestronglyMeasurable
      _ = (expMeasure α).real (Set.Ioi (1 : ℝ)) := by
        simp [F, integral_indicator_const, measurableSet_Ioi, smul_eq_mul]
      _ = Real.exp (-((α : ℝ) * 1)) := by
        rw [expMeasure_real_Ioi_eq_exp_of_nonneg hα_real zero_le_one]
      _ = Real.exp (-(α : ℝ)) := by ring_nf
  have hY0_expectation_pos : 0 < μ[Y 0] := by
    rw [hY0_expectation]
    exact Real.exp_pos _
  have hY_limit :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Y i ω) / n) atTop
        (𝓝 (μ[Y 0])) := by
    -- Proof comment: apply the strong law to the i.i.d. indicator process.
    exact ProbabilityTheory.strong_law_ae_real Y hY0_integrable
      (fun i j hij ↦ hY_iIndep.indepFun hij) hY_ident
  have hW_pos : ∀ᵐ ω ∂μ, ∀ n, 0 < W n ω :=
    ae_interarrival_pos_of_iid_exponential μ α W hW_iid hW0_law hα
  filter_upwards [hW_pos, hY_limit] with ω hW_pos_ω hY_limit_ω
  refine ⟨?_, ?_⟩
  · -- Proof comment: strictly positive interarrivals force strict growth of the arrival-time
    -- partial sums.
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    rw [arrivalTime_succ]
    exact lt_add_of_pos_right _ (hW_pos_ω n)
  · -- Route correction: instead of summing the exponential interarrivals directly, compare them
    -- with the count of gaps larger than `1`. The strong law yields a positive linear frequency of
    -- such gaps, and each such gap contributes at least `1` to the arrival-time sum.
    have hYsum_le_arrival :
        ∀ n, (∑ i ∈ Finset.range n, Y i ω) ≤ arrivalTime W n ω := by
      intro n
      calc
        ∑ i ∈ Finset.range n, Y i ω ≤ ∑ i ∈ Finset.range n, W i ω := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          by_cases hlarge : (1 : ℝ) < W i ω
          · have hbound : (1 : ℝ) ≤ W i ω := le_of_lt hlarge
            simpa [Y, F, hlarge] using hbound
          · have hnonneg : 0 ≤ W i ω := (hW_pos_ω i).le
            simpa [Y, F, hlarge] using hnonneg
        _ = arrivalTime W n ω := by
          simp [arrivalTime]
    have hhalf_pos : 0 < μ[Y 0] / 2 := by
      linarith
    have hhalf_lt : μ[Y 0] / 2 < μ[Y 0] := by
      linarith
    have havg_eventually :
        ∀ᶠ n : ℕ in atTop, μ[Y 0] / 2 < (∑ i ∈ Finset.range n, Y i ω) / n := by
      -- Proof comment: the strong-law limit is positive, so the empirical frequency is
      -- eventually bounded below by half of that limit.
      exact hY_limit_ω.eventually (Ioi_mem_nhds hhalf_lt)
    have hlinear_le_sumY :
        (fun n : ℕ ↦ (μ[Y 0] / 2) * (n : ℝ)) ≤ᶠ[atTop] fun n ↦ ∑ i ∈ Finset.range n, Y i ω := by
      -- Proof comment: multiply the eventual lower bound on empirical frequencies by `n`.
      filter_upwards [havg_eventually] with n hn
      by_cases hzero : n = 0
      · subst hzero
        simp
      · have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero)
        exact le_of_lt ((lt_div_iff₀ hn_pos).mp hn)
    have hlinear_tendsto :
        Tendsto (fun n : ℕ ↦ (μ[Y 0] / 2) * (n : ℝ)) atTop atTop := by
      -- Proof comment: a positive multiple of `n` still diverges to `∞`.
      exact Filter.Tendsto.const_mul_atTop' hhalf_pos tendsto_natCast_atTop_atTop
    have harrival_lower :
        (fun n : ℕ ↦ (μ[Y 0] / 2) * (n : ℝ)) ≤ᶠ[atTop] fun n ↦ arrivalTime W n ω := by
      filter_upwards [hlinear_le_sumY] with n hn
      exact le_trans hn (hYsum_le_arrival n)
    -- Proof comment: eventual domination by a divergent linear function forces the arrival times
    -- themselves to diverge to `∞`.
    exact tendsto_atTop_mono' atTop harrival_lower hlinear_tendsto

/-- Helper for Theorem 5.36: an i.i.d. exponential interarrival sequence almost surely has
strictly increasing arrival times. -/
theorem ae_arrivalTime_strictMono_of_iid_exponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    ∀ᵐ ω ∂μ, StrictMono (fun n ↦ arrivalTime W n ω) := by
  filter_upwards [ae_interarrival_pos_of_iid_exponential μ α W hW_iid hW0_law hα] with ω hω
  -- Proof comment: strictly positive interarrivals force strict growth of the arrival-time
  -- partial sums.
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  rw [arrivalTime_succ]
  exact lt_add_of_pos_right _ (hω n)

/-- Helper for Theorem 5.36: an i.i.d. exponential interarrival sequence almost surely has arrival
times diverging to `∞`. -/
theorem ae_arrivalTime_tendsto_of_iid_exponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop := by
  filter_upwards
    [ae_arrivalTime_strictMono_and_tendsto_of_iid_exponential μ α W hW_iid hW0_law hα]
    with ω hω
  -- Proof comment: the combined almost-sure statement already contains the required divergence.
  exact hω.2

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.36: along a zero-anchored monotone time grid on a genuine renewal path,
prescribing the increment vector is equivalent to prescribing the endpoint counts by cumulative
sums. -/
theorem renewal_increment_event_iff_endpoint_counts_zero_anchored
    (W : ℕ → Ω → ℝ) {ω : Ω}
    (h_arrival_strict : StrictMono (fun n ↦ arrivalTime W n ω))
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop)
    {u : ℕ → NNReal} (hu0 : u 0 = 0) (hu : Monotone u) (k : ℕ → ℕ) :
    (∀ i, renewalCountingProcess W (u (i + 1)) ω - renewalCountingProcess W (u i) ω = k i) ↔
      ∀ j, renewalCountingProcess W (u j) ω = ∑ i ∈ Finset.range j, k i := by
  have h_first_arrival : 0 < arrivalTime W 1 ω := by
    -- Proof comment: strict growth gives the genuine-path start condition `T_1 > 0`.
    simpa [arrivalTime_zero] using h_arrival_strict (show 0 < 1 by omega)
  have hX0 : renewalCountingProcess W (u 0) ω = 0 := by
    simpa [hu0] using renewalCountingProcess_zero W ω h_first_arrival
  have hXmono : Monotone fun j : ℕ ↦ renewalCountingProcess W (u j) ω := by
    intro i j hij
    exact renewalCountingProcess_mono W h_arrival_tendsto (hu hij)
  -- Proof comment: apply the abstract cumulative-sum equivalence to the sampled endpoint path
  -- `j ↦ N_(u j)(ω)`.
  simpa using
    (nat_increment_event_iff_endpoint_counts hX0 hXmono)

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.36: along a genuine renewal path, endpoint counts are equivalent to the
corresponding arrival-time strip conditions. -/
theorem renewal_endpoint_counts_iff_arrival_strips
    (W : ℕ → Ω → ℝ) {ω : Ω}
    (h_arrival_strict : StrictMono (fun n ↦ arrivalTime W n ω))
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop)
    (u : ℕ → NNReal) (K : ℕ → ℕ) :
    (∀ j, renewalCountingProcess W (u j) ω = K j) ↔
      ∀ j, arrivalTime W (K j) ω ≤ u j ∧ u j < arrivalTime W (K j + 1) ω := by
  constructor
  · intro hK j
    -- Proof comment: rewrite each prescribed endpoint count through the strip characterization.
    have h_strip :
        renewalCountingProcess W (u j) ω = K j ↔
          arrivalTime W (K j) ω ≤ u j ∧ u j < arrivalTime W (K j + 1) ω :=
      renewalCountingProcess_eq_iff_arrival_strip W h_arrival_strict h_arrival_tendsto
    simpa [hK j] using h_strip.1 (hK j)
  · intro hK j
    -- Proof comment: conversely, each strip condition pins down the corresponding endpoint count.
    have h_strip :
        renewalCountingProcess W (u j) ω = K j ↔
          arrivalTime W (K j) ω ≤ u j ∧ u j < arrivalTime W (K j + 1) ω :=
      renewalCountingProcess_eq_iff_arrival_strip W h_arrival_strict h_arrival_tendsto
    exact h_strip.2 (hK j)

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.36: extending a finite zero-anchored grid constantly after its last point
reduces the finite increment event to the nat-indexed cumulative-count API already proved above.
-/
theorem renewalIncrementFinGrid_iff_endpointCounts
    (W : ℕ → Ω → ℝ) {ω : Ω}
    (h_arrival_strict : StrictMono (fun n ↦ arrivalTime W n ω))
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop)
    {m : ℕ} {u : Fin (m + 1) → NNReal} (hu0 : u 0 = 0) (hu : Monotone u) (k : Fin m → ℕ) :
    (∀ i : Fin m,
        renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω = k i) ↔
      ∀ j : Fin (m + 1),
        renewalCountingProcess W (u j) ω =
          ∑ i ∈ Finset.range j.1, if hi : i < m then k ⟨i, hi⟩ else 0 := by
  let uNat : ℕ → NNReal := fun n ↦ u ⟨min n m, Nat.lt_succ_of_le (Nat.min_le_right n m)⟩
  let kNat : ℕ → ℕ := fun n ↦ if hn : n < m then k ⟨n, hn⟩ else 0
  have huNat0 : uNat 0 = 0 := by
    -- Proof comment: the constant extension still starts at the zero anchor of the finite grid.
    simpa [uNat, hu0]
  have huNat : Monotone uNat := by
    -- Proof comment: the extension is `u` composed with `n ↦ min n m`, so monotonicity is
    -- inherited from the original finite grid.
    intro a b hab
    have hmin : min a m ≤ min b m := by
      omega
    exact hu (show (⟨min a m, Nat.lt_succ_of_le (Nat.min_le_right a m)⟩ : Fin (m + 1)) ≤
        ⟨min b m, Nat.lt_succ_of_le (Nat.min_le_right b m)⟩ by
      exact hmin)
  constructor
  · intro hinc
    have hincNat :
        ∀ i : ℕ,
          renewalCountingProcess W (uNat (i + 1)) ω - renewalCountingProcess W (uNat i) ω =
            kNat i := by
      intro i
      by_cases hi : i < m
      · have hi_le : i ≤ m := Nat.le_of_lt hi
        have hi_succ_le : i + 1 ≤ m := by
          omega
        -- Proof comment: before the last grid cell, the constant extension agrees verbatim with
        -- the original finite grid.
        simpa [uNat, kNat, hi, Nat.min_eq_left hi_le, Nat.min_eq_left hi_succ_le] using
          hinc ⟨i, hi⟩
      · have hm_le : m ≤ i := Nat.le_of_not_gt hi
        have hconst :
            renewalCountingProcess W (uNat (i + 1)) ω =
              renewalCountingProcess W (uNat i) ω := by
          -- Proof comment: after the last finite grid point, the extension is constant, so every
          -- further increment is deterministically zero.
          simp [uNat, Nat.min_eq_right hm_le,
            Nat.min_eq_right (le_trans hm_le (Nat.le_succ i))]
        simp [kNat, hi, hconst]
    have hendpointNat :
        ∀ j : ℕ, renewalCountingProcess W (uNat j) ω = ∑ i ∈ Finset.range j, kNat i :=
      (renewal_increment_event_iff_endpoint_counts_zero_anchored
        W h_arrival_strict h_arrival_tendsto huNat0 huNat kNat).1 hincNat
    intro j
    -- Proof comment: on the original finite grid indices, the constant extension recovers the
    -- desired cumulative-count formula unchanged.
    have hmin : min j.1 m = j.1 := by
      omega
    simpa [uNat, kNat, hmin] using hendpointNat j.1
  · intro hcount
    intro i
    have hi_mono :
        renewalCountingProcess W (u i.castSucc) ω ≤ renewalCountingProcess W (u i.succ) ω :=
      renewalCountingProcess_mono W h_arrival_tendsto (hu (show i.castSucc ≤ i.succ by
        exact Nat.le_succ i.1))
    have hi_prev :
        renewalCountingProcess W (u i.castSucc) ω =
          ∑ j ∈ Finset.range i.1, if hj : j < m then k ⟨j, hj⟩ else 0 :=
      hcount i.castSucc
    have hi_next :
        renewalCountingProcess W (u i.succ) ω =
          k i + ∑ j ∈ Finset.range i.1, if hj : j < m then k ⟨j, hj⟩ else 0 := by
      -- Proof comment: the next cumulative count adds exactly the current increment label `k i`.
      simpa [Finset.sum_range_succ, kNat, i.2, add_assoc, add_left_comm, add_comm] using
        hcount i.succ
    have hsum :
        renewalCountingProcess W (u i.succ) ω =
          k i + renewalCountingProcess W (u i.castSucc) ω := by
      calc
        renewalCountingProcess W (u i.succ) ω
            = k i + ∑ j ∈ Finset.range i.1, if hj : j < m then k ⟨j, hj⟩ else 0 := hi_next
        _ = k i + renewalCountingProcess W (u i.castSucc) ω := by
              rw [hi_prev]
    -- Proof comment: subtract the previous endpoint count from the next cumulative count.
    exact (Nat.sub_eq_iff_eq_add hi_mono).2 hsum

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.36: the finite increment event on a zero-anchored monotone grid is
equivalent to the corresponding cumulative arrival-strip conditions with the cumulative counts
`∑_{i < j} k_i`. -/
theorem renewalIncrementFinGrid_iff_arrivalStrips
    (W : ℕ → Ω → ℝ) {ω : Ω}
    (h_arrival_strict : StrictMono (fun n ↦ arrivalTime W n ω))
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop)
    {m : ℕ} {u : Fin (m + 1) → NNReal} (hu0 : u 0 = 0) (hu : Monotone u) (k : Fin m → ℕ) :
    (∀ i : Fin m,
        renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω = k i) ↔
      ∀ j : Fin (m + 1),
        arrivalTime W (∑ i ∈ Finset.range j.1, if hi : i < m then k ⟨i, hi⟩ else 0) ω ≤ u j ∧
          u j <
            arrivalTime W
              ((∑ i ∈ Finset.range j.1, if hi : i < m then k ⟨i, hi⟩ else 0) + 1) ω := by
  have hcount :=
    renewalIncrementFinGrid_iff_endpointCounts
      W h_arrival_strict h_arrival_tendsto hu0 hu k
  constructor
  · intro hinc
    have hcount' := hcount.1 hinc
    intro j
    -- Proof comment: once the endpoint count is known, the strip theorem identifies the matching
    -- arrival interval at that grid time.
    exact (renewalCountingProcess_eq_iff_arrival_strip W h_arrival_strict h_arrival_tendsto).1
      (hcount' j)
  · intro hstrip
    have hcount' :
        ∀ j : Fin (m + 1),
          renewalCountingProcess W (u j) ω =
            ∑ i ∈ Finset.range j.1, if hi : i < m then k ⟨i, hi⟩ else 0 := by
      intro j
      -- Proof comment: each strip condition pins down the endpoint count uniquely.
      exact (renewalCountingProcess_eq_iff_arrival_strip W h_arrival_strict h_arrival_tendsto).2
        (hstrip j)
    exact hcount.2 hcount'

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.36: on a genuine renewal path, fixing the count at time `s` and the
increment over `[s,t]` is equivalent to prescribing the two textbook arrival strips at `s` and
`t`. -/
theorem renewal_increment_two_time_iff_arrival_strips
    (W : ℕ → Ω → ℝ) {ω : Ω}
    (h_arrival_strict : StrictMono (fun n ↦ arrivalTime W n ω))
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop)
    {s t : NNReal} (hst : s ≤ t) {k l : ℕ} :
    (renewalCountingProcess W s ω = k ∧
        renewalCountingProcess W t ω - renewalCountingProcess W s ω = l) ↔
      (arrivalTime W k ω ≤ s ∧
        s < arrivalTime W (k + 1) ω ∧
        arrivalTime W (k + l) ω ≤ t ∧
        t < arrivalTime W (k + l + 1) ω) := by
  constructor
  · rintro ⟨hs_count, hinc⟩
    have hs_strip :
        arrivalTime W k ω ≤ s ∧ s < arrivalTime W (k + 1) ω :=
      (renewalCountingProcess_eq_iff_arrival_strip W h_arrival_strict h_arrival_tendsto).1 hs_count
    have ht_count : renewalCountingProcess W t ω = k + l := by
      have hmono : renewalCountingProcess W s ω ≤ renewalCountingProcess W t ω :=
        renewalCountingProcess_mono W h_arrival_tendsto hst
      have hsum : renewalCountingProcess W t ω = l + renewalCountingProcess W s ω :=
        (Nat.sub_eq_iff_eq_add hmono).1 hinc
      simpa [hs_count, add_assoc, add_comm, add_left_comm] using hsum
    have ht_strip :
        arrivalTime W (k + l) ω ≤ t ∧ t < arrivalTime W (k + l + 1) ω :=
      (renewalCountingProcess_eq_iff_arrival_strip W h_arrival_strict h_arrival_tendsto).1 ht_count
    -- Proof comment: specifying `N_s = k` and the increment `N_t - N_s = l` is exactly the same
    -- as specifying the two endpoint strips for counts `k` and `k + l`.
    exact ⟨hs_strip.1, hs_strip.2, ht_strip.1, ht_strip.2⟩
  · rintro ⟨hs_lower, hs_upper, ht_lower, ht_upper⟩
    have hs_count :
        renewalCountingProcess W s ω = k :=
      (renewalCountingProcess_eq_iff_arrival_strip W h_arrival_strict h_arrival_tendsto).2
        ⟨hs_lower, hs_upper⟩
    have ht_count :
        renewalCountingProcess W t ω = k + l :=
      (renewalCountingProcess_eq_iff_arrival_strip W h_arrival_strict h_arrival_tendsto).2
        ⟨ht_lower, ht_upper⟩
    -- Proof comment: once the two endpoint counts are fixed, the increment is their difference.
    refine ⟨hs_count, ?_⟩
    omega

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.36: after fixing the count `N_s = k`, the increment over `[s,t]` is
equivalent to a strip condition for the contiguous block of interarrivals starting at `k`,
measured relative to the `k`th arrival time `T_k`. This is the correct block rewrite for the
textbook event; the threshold is `(t - T_k)`, not merely `(t - s)`. -/
theorem renewal_increment_two_time_iff_relative_block_strip
    (W : ℕ → Ω → ℝ) {ω : Ω}
    (h_arrival_strict : StrictMono (fun n ↦ arrivalTime W n ω))
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop)
    {s t : NNReal} (hst : s ≤ t) {k l : ℕ} :
    (renewalCountingProcess W s ω = k ∧
        renewalCountingProcess W t ω - renewalCountingProcess W s ω = l) ↔
      (arrivalTime W k ω ≤ s ∧
        s < arrivalTime W (k + 1) ω ∧
        (∑ i ∈ Finset.range l, W (k + i) ω) ≤ (t : ℝ) - arrivalTime W k ω ∧
        (t : ℝ) - arrivalTime W k ω <
          ∑ i ∈ Finset.range (l + 1), W (k + i) ω) := by
  constructor
  · intro hinc
    have h_strip :
        (renewalCountingProcess W s ω = k ∧
            renewalCountingProcess W t ω - renewalCountingProcess W s ω = l) ↔
          (arrivalTime W k ω ≤ s ∧
            s < arrivalTime W (k + 1) ω ∧
            arrivalTime W (k + l) ω ≤ t ∧
            t < arrivalTime W (k + l + 1) ω) :=
      renewal_increment_two_time_iff_arrival_strips W h_arrival_strict h_arrival_tendsto hst
    rcases
      h_strip.1 hinc with
      ⟨hs_lower, hs_upper, ht_lower, ht_upper⟩
    have hblock_lower :
        (∑ i ∈ Finset.range l, W (k + i) ω) ≤ (t : ℝ) - arrivalTime W k ω := by
      have hrewrite : arrivalTime W (k + l) ω =
          arrivalTime W k ω + ∑ i ∈ Finset.range l, W (k + i) ω := arrivalTime_add W k l ω
      linarith
    have hblock_upper :
        (t : ℝ) - arrivalTime W k ω < ∑ i ∈ Finset.range (l + 1), W (k + i) ω := by
      have hrewrite :
          arrivalTime W (k + l + 1) ω =
            arrivalTime W k ω + ∑ i ∈ Finset.range (l + 1), W (k + i) ω := by
        simpa [Nat.add_assoc] using arrivalTime_add W k (l + 1) ω
      linarith
    -- Proof comment: rewrite the second strip relative to the `k`th arrival using the block-sum
    -- decomposition `T_(k+m) = T_k + Σ_{i< m} W_(k+i)`.
    exact ⟨hs_lower, hs_upper, hblock_lower, hblock_upper⟩
  · rintro ⟨hs_lower, hs_upper, hblock_lower, hblock_upper⟩
    have h_strip :
        (renewalCountingProcess W s ω = k ∧
            renewalCountingProcess W t ω - renewalCountingProcess W s ω = l) ↔
          (arrivalTime W k ω ≤ s ∧
            s < arrivalTime W (k + 1) ω ∧
            arrivalTime W (k + l) ω ≤ t ∧
            t < arrivalTime W (k + l + 1) ω) :=
      renewal_increment_two_time_iff_arrival_strips W h_arrival_strict h_arrival_tendsto hst
    have ht_lower : arrivalTime W (k + l) ω ≤ t := by
      have hrewrite : arrivalTime W (k + l) ω =
          arrivalTime W k ω + ∑ i ∈ Finset.range l, W (k + i) ω := arrivalTime_add W k l ω
      linarith
    have ht_upper : t < arrivalTime W (k + l + 1) ω := by
      have hrewrite :
          arrivalTime W (k + l + 1) ω =
            arrivalTime W k ω + ∑ i ∈ Finset.range (l + 1), W (k + i) ω := by
        simpa [Nat.add_assoc] using arrivalTime_add W k (l + 1) ω
      linarith
    -- Proof comment: after reconstructing the second strip from the relative block inequalities,
    -- appeal to the already established two-time strip equivalence.
    exact h_strip.2 ⟨hs_lower, hs_upper, ht_lower, ht_upper⟩

/-- Helper for Theorem 5.36: each finite arrival time `arrivalTime W n` is measurable once the
interarrival coordinates are measurable. -/
theorem arrivalTime_measurable
    (W : ℕ → Ω → ℝ) (hW_meas : ∀ n, Measurable (W n)) (n : ℕ) :
    Measurable (arrivalTime W n) := by
  -- Proof comment: build the partial sums inductively using `arrivalTime_succ`.
  induction n with
  | zero =>
      simpa [arrivalTime] using (measurable_zero : Measurable (0 : Ω → ℝ))
  | succ n ih =>
      simpa [arrivalTime_succ] using ih.add (hW_meas n)

/-- Helper for Theorem 5.36: if the arrival times tend to `∞`, then the defining set for the raw
renewal count is nonempty. -/
private theorem rawRenewalDefiningSet_nonempty_of_tendsto
    (W : ℕ → Ω → ℝ) {t : NNReal} {ω : Ω}
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) :
    ({n : ℕ | t < arrivalTime W (n + 1) ω} : Set ℕ).Nonempty := by
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 h_arrival_tendsto) ((t : ℝ) + 1)
  have hN_pos : 0 < N := by
    by_contra hN_zero
    have hN_eq_zero : N = 0 := Nat.eq_zero_of_not_pos hN_zero
    have ht_nonneg : 0 ≤ (t : ℝ) := t.2
    have hle_zero : (t : ℝ) + 1 ≤ 0 := by
      simpa [hN_eq_zero, arrivalTime_zero] using hN N (le_refl N)
    linarith
  refine ⟨N - 1, ?_⟩
  have hlt : (t : ℝ) < arrivalTime W N ω := by
    have hle : (t : ℝ) + 1 ≤ arrivalTime W N ω := hN N (le_refl N)
    linarith
  have hpred : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hN_pos)
  exact (show (t : ℝ) < arrivalTime W ((N - 1) + 1) ω by simpa [hpred] using hlt)

/-- Helper for Theorem 5.36: once the raw renewal defining set is nonempty, the value of
`rawRenewalCountingProcess W t ω` is exactly the first index whose next arrival time exceeds `t`.
-/
private theorem rawRenewalCountingProcess_eq_iff
    (W : ℕ → Ω → ℝ) {t : NNReal} {ω : Ω} {n : ℕ}
    (h_nonempty : ({m : ℕ | t < arrivalTime W (m + 1) ω} : Set ℕ).Nonempty) :
    rawRenewalCountingProcess W t ω = n ↔
      (∀ m < n, arrivalTime W (m + 1) ω ≤ t) ∧ t < arrivalTime W (n + 1) ω := by
  let S : Set ℕ := {m : ℕ | t < arrivalTime W (m + 1) ω}
  have hS_nonempty : S.Nonempty := by
    simpa [S] using h_nonempty
  have hsInf_mem : sInf S ∈ S := Nat.sInf_mem hS_nonempty
  constructor
  · intro hraw
    have hsInf_eq : sInf S = n := by
      simpa [S, rawRenewalCountingProcess] using hraw
    have hn_mem : n ∈ S := by
      simpa [hsInf_eq] using hsInf_mem
    refine ⟨?_, hn_mem⟩
    intro m hm
    by_contra hm_bad
    have hm_mem : m ∈ S := by
      exact lt_of_not_ge hm_bad
    have hsInf_le : sInf S ≤ m := Nat.sInf_le hm_mem
    have hsInf_eq : sInf S = n := by
      simpa [S, rawRenewalCountingProcess] using hraw
    exact (Nat.not_le_of_gt hm) (hsInf_eq ▸ hsInf_le)
  · rintro ⟨h_before, hn_mem⟩
    have hsInf_le : sInf S ≤ n := Nat.sInf_le hn_mem
    have hn_le : n ≤ sInf S := by
      by_contra hn_lt
      have hsInf_lt : sInf S < n := Nat.lt_of_not_ge hn_lt
      exact (not_le_of_gt hsInf_mem) (h_before (sInf S) hsInf_lt)
    exact by
      simpa [S, rawRenewalCountingProcess] using le_antisymm hsInf_le hn_le

/-- Helper for Theorem 5.36: the event that the arrival times diverge to `∞` is measurable. -/
private theorem measurableSet_arrivalTime_tendsto
    (W : ℕ → Ω → ℝ) (hW_meas : ∀ n, Measurable (W n)) :
    MeasurableSet {ω | Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop} := by
  let A : ℕ → Ω → Prop := fun m ω ↦ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (m : ℝ) ≤ arrivalTime W n ω
  have hA_meas : ∀ m : ℕ, MeasurableSet {ω | A m ω} := by
    intro m
    have h_tail_meas :
        ∀ N : ℕ, MeasurableSet {ω | ∀ n : ℕ, N ≤ n → (m : ℝ) ≤ arrivalTime W n ω} := by
      intro N
      let B : ℕ → Set Ω := fun n ↦
        if hN : N ≤ n then {ω | (m : ℝ) ≤ arrivalTime W n ω} else Set.univ
      have hB_meas : ∀ n : ℕ, MeasurableSet (B n) := by
        intro n
        by_cases hN : N ≤ n
        · simpa [B, hN, Set.preimage] using
            (arrivalTime_measurable W hW_meas n) measurableSet_Ici
        · simp [B, hN]
      have hEq :
          {ω | ∀ n : ℕ, N ≤ n → (m : ℝ) ≤ arrivalTime W n ω} = ⋂ n : ℕ, B n := by
        ext ω
        constructor
        · intro hω
          refine Set.mem_iInter.2 fun n ↦ ?_
          by_cases hN : N ≤ n
          · simpa [B, hN] using hω n hN
          · simp [B, hN]
        · intro hω n hN
          have hn_mem : ω ∈ B n := Set.mem_iInter.1 hω n
          simpa [B, hN] using hn_mem
      rw [hEq]
      exact MeasurableSet.iInter hB_meas
    have hEq :
        {ω | A m ω} =
          ⋃ N : ℕ, {ω | ∀ n : ℕ, N ≤ n → (m : ℝ) ≤ arrivalTime W n ω} := by
      ext ω
      simp [A]
    rw [hEq]
    exact MeasurableSet.iUnion h_tail_meas
  have hEq :
      {ω | Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop} = ⋂ m : ℕ, {ω | A m ω} := by
    ext ω
    have htendsto_nat :
        Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop ↔
          ∀ m : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (m : ℝ) ≤ arrivalTime W n ω := by
      rw [tendsto_atTop_atTop]
      constructor
      · intro h m
        rcases h (m : ℝ) with ⟨N, hN⟩
        exact ⟨N, hN⟩
      · intro h b
        obtain ⟨m, hm⟩ := exists_nat_ge b
        rcases h m with ⟨N, hN⟩
        exact ⟨N, fun n hn ↦ le_trans hm (hN n hn)⟩
    simp [A, htendsto_nat]
  rw [hEq]
  exact MeasurableSet.iInter hA_meas

/-- Helper for Theorem 5.36: each coordinate of the public renewal counting process is measurable
once the interarrival coordinates are measurable. -/
theorem renewalCountingProcess_measurable
    (W : ℕ → Ω → ℝ) (hW_meas : ∀ n, Measurable (W n)) (t : NNReal) :
    Measurable (renewalCountingProcess W t) := by
  classical
  let Good : Set Ω :=
    {ω |
      0 < arrivalTime W 1 ω ∧
        Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop}
  have hGood_meas : MeasurableSet Good := by
    -- Proof comment: the good-path predicate is the intersection of the measurable first-arrival
    -- positivity event and the measurable divergence event.
    have hFirst_meas : MeasurableSet {ω | 0 < arrivalTime W 1 ω} := by
      exact (arrivalTime_measurable W hW_meas 1) measurableSet_Ioi
    change MeasurableSet {ω |
      0 < arrivalTime W 1 ω ∧
        Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop}
    exact hFirst_meas.inter (measurableSet_arrivalTime_tendsto W hW_meas)
  refine measurable_to_countable' ?_
  intro n
  let Before : Set Ω := {ω | ∀ m < n, arrivalTime W (m + 1) ω ≤ t}
  have hBefore_meas : MeasurableSet Before := by
    let C : Fin n → Set Ω := fun i ↦ {ω | arrivalTime W (i.1 + 1) ω ≤ t}
    have hC_meas : ∀ i : Fin n, MeasurableSet (C i) := by
      intro i
      simpa [C, Set.preimage] using
        (arrivalTime_measurable W hW_meas (i.1 + 1)) measurableSet_Iic
    have hEq : Before = ⋂ i : Fin n, C i := by
      ext ω
      constructor
      · intro hω
        exact Set.mem_iInter.2 fun i ↦ hω i.1 i.2
      · intro hω m hm
        exact Set.mem_iInter.1 hω ⟨m, hm⟩
    rw [hEq]
    exact MeasurableSet.iInter hC_meas
  let Hit : Set Ω := {ω | t < arrivalTime W (n + 1) ω}
  have hHit_meas : MeasurableSet Hit := by
    -- Proof comment: the terminal strict inequality is measurable as a coordinate preimage of
    -- `Set.Ioi t`.
    simpa [Hit, Set.preimage] using
      (arrivalTime_measurable W hW_meas (n + 1)) measurableSet_Ioi
  let FirstHit : Set Ω := Before ∩ Hit
  have hFirstHit_meas : MeasurableSet FirstHit := hBefore_meas.inter hHit_meas
  by_cases hn : n = 0
  · subst hn
    have hEq :
        renewalCountingProcess W t ⁻¹' ({0} : Set ℕ) = Goodᶜ ∪ (Good ∩ FirstHit) := by
      ext ω
      constructor
      · intro hω
        have hω0 : renewalCountingProcess W t ω = 0 := by
          simpa using hω
        by_cases hgood : ω ∈ Good
        · right
          have hgood' :
              0 < arrivalTime W 1 ω ∧
                Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop := by
            simpa [Good] using hgood
          have h_nonempty :
              ({m : ℕ | t < arrivalTime W (m + 1) ω} : Set ℕ).Nonempty :=
            rawRenewalDefiningSet_nonempty_of_tendsto W hgood'.2
          have hraw : rawRenewalCountingProcess W t ω = 0 := by
            rw [← renewalCountingProcess_eq_rawRenewalCountingProcess W hgood'.1 hgood'.2]
            exact hω0
          exact ⟨hgood, (rawRenewalCountingProcess_eq_iff W h_nonempty).1 hraw⟩
        · exact Or.inl hgood
      · rintro (hbad | ⟨hgood, hfirst⟩)
        · have hbad' :
            ¬ (0 < arrivalTime W 1 ω ∧
                Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) := by
            simpa [Good] using hbad
          have hbad'' :
              ¬ (0 < W 0 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) := by
            simpa [arrivalTime_succ, arrivalTime_zero] using hbad'
          simp [renewalCountingProcess, arrivalTime_succ, arrivalTime_zero, hbad'']
        · have hgood' :
              0 < arrivalTime W 1 ω ∧
                Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop := by
            simpa [Good] using hgood
          have h_nonempty :
              ({m : ℕ | t < arrivalTime W (m + 1) ω} : Set ℕ).Nonempty :=
            rawRenewalDefiningSet_nonempty_of_tendsto W hgood'.2
          have hraw : rawRenewalCountingProcess W t ω = 0 :=
            (rawRenewalCountingProcess_eq_iff W h_nonempty).2 hfirst
          have hcount : renewalCountingProcess W t ω = 0 := by
            rw [renewalCountingProcess_eq_rawRenewalCountingProcess W hgood'.1 hgood'.2]
            exact hraw
          simpa [hcount]
    rw [hEq]
    exact hGood_meas.compl.union (hGood_meas.inter hFirstHit_meas)
  · have hEq : renewalCountingProcess W t ⁻¹' ({n} : Set ℕ) = Good ∩ FirstHit := by
      ext ω
      constructor
      · intro hω
        have hωn : renewalCountingProcess W t ω = n := by
          simpa using hω
        have hgood : ω ∈ Good := by
          by_contra hbad
          have hbad' :
              ¬ (0 < arrivalTime W 1 ω ∧
                  Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) := by
            simpa [Good] using hbad
          have hzero : renewalCountingProcess W t ω = 0 := by
            have hbad'' :
                ¬ (0 < W 0 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) := by
              simpa [arrivalTime_succ, arrivalTime_zero] using hbad'
            simp [renewalCountingProcess, arrivalTime_succ, arrivalTime_zero, hbad'']
          exact hn (hωn.symm.trans hzero)
        have hgood' :
            0 < arrivalTime W 1 ω ∧
              Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop := by
          simpa [Good] using hgood
        have h_nonempty :
            ({m : ℕ | t < arrivalTime W (m + 1) ω} : Set ℕ).Nonempty :=
          rawRenewalDefiningSet_nonempty_of_tendsto W hgood'.2
        have hraw : rawRenewalCountingProcess W t ω = n := by
          rw [← renewalCountingProcess_eq_rawRenewalCountingProcess W hgood'.1 hgood'.2]
          exact hωn
        exact ⟨hgood, (rawRenewalCountingProcess_eq_iff W h_nonempty).1 hraw⟩
      · rintro ⟨hgood, hfirst⟩
        have hgood' :
            0 < arrivalTime W 1 ω ∧
              Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop := by
          simpa [Good] using hgood
        have h_nonempty :
            ({m : ℕ | t < arrivalTime W (m + 1) ω} : Set ℕ).Nonempty :=
          rawRenewalDefiningSet_nonempty_of_tendsto W hgood'.2
        have hraw : rawRenewalCountingProcess W t ω = n :=
          (rawRenewalCountingProcess_eq_iff W h_nonempty).2 hfirst
        have hcount : renewalCountingProcess W t ω = n := by
          rw [renewalCountingProcess_eq_rawRenewalCountingProcess W hgood'.1 hgood'.2]
          exact hraw
        simpa [hcount]
    rw [hEq]
    exact hGood_meas.inter hFirstHit_meas

/-- Helper for Theorem 5.36: under measurable interarrivals, the public renewal counting process
is a stochastic process. -/
theorem renewalCountingProcess_isStochasticProcess
    (W : ℕ → Ω → ℝ) (hW_meas : ∀ n, Measurable (W n)) :
    IsStochasticProcess (renewalCountingProcess W) := by
  -- Proof comment: the stochastic-process interface is exactly coordinatewise measurability.
  intro t
  exact renewalCountingProcess_measurable W hW_meas t

/-- Helper for Theorem 5.36: the public renewal counting process starts at `0` on every sample
path. -/
theorem renewalCountingProcess_zero_eq (W : ℕ → Ω → ℝ) :
    renewalCountingProcess W 0 = 0 := by
  funext ω
  change renewalCountingProcess W 0 ω = (0 : ℕ)
  by_cases hgood :
      0 < arrivalTime W 1 ω ∧
        Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop
  · exact renewalCountingProcess_zero W ω hgood.1
  · have hbad :
        ¬ (0 < W 0 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) := by
      simpa [arrivalTime_succ, arrivalTime_zero] using hgood
    simp [renewalCountingProcess, arrivalTime_succ, arrivalTime_zero, hbad]

/-- Helper for Theorem 5.36: the public renewal counting process is monotone in time on every
sample path. -/
theorem renewalCountingProcess_monotone (W : ℕ → Ω → ℝ) :
    Monotone (renewalCountingProcess W) := by
  intro s t hst ω
  by_cases h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop
  · exact renewalCountingProcess_mono W h_arrival_tendsto hst
  · have hbad :
        ¬ (0 < arrivalTime W 1 ω ∧
            Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) := by
      intro hgood
      exact h_arrival_tendsto hgood.2
    have hs_zero : renewalCountingProcess W s ω = 0 := by
      have hbad' :
          ¬ (0 < W 0 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) := by
        simpa [arrivalTime_succ, arrivalTime_zero] using hbad
      simp [renewalCountingProcess, arrivalTime_succ, arrivalTime_zero, hbad']
    have ht_zero : renewalCountingProcess W t ω = 0 := by
      have hbad' :
          ¬ (0 < W 0 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) := by
        simpa [arrivalTime_succ, arrivalTime_zero] using hbad
      simp [renewalCountingProcess, arrivalTime_succ, arrivalTime_zero, hbad']
    rw [hs_zero, ht_zero]

/-- Helper for Theorem 5.36: after splitting off coordinate `0` from a finite function, the second
component is exactly the successor tail. -/
private theorem piFinSuccAbove_zero_snd_eq_tail
    {m : ℕ} :
    Prod.snd ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℕ) 0 =
      fun x : Fin (m + 1) → ℕ ↦ fun i : Fin m ↦ x i.succ := by
  funext x i
  rfl

/-- Helper for Theorem 5.36: after splitting off coordinate `0` from a real-valued finite block,
the second component is exactly the successor tail. -/
private theorem piFinSuccAbove_zero_snd_eq_tail_real
    {m : ℕ} :
    Prod.snd ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0 =
      fun x : Fin (m + 1) → ℝ ↦ fun i : Fin m ↦ x i.succ := by
  funext x i
  rfl

/-- Helper for Theorem 5.36: after splitting off the last coordinate from a finite block tuple,
the second component is exactly the prefix obtained via `Fin.castSucc`. -/
private theorem piFinSuccAbove_last_snd_eq_castSucc
    {m : ℕ} :
    Prod.snd ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m) =
      fun x : Fin (m + 1) → ℝ ↦ fun i : Fin m ↦ x i.castSucc := by
  funext x i
  -- Proof comment: removing the terminal coordinate leaves precisely the `castSucc` prefix.
  simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def]

/-- Helper for Theorem 5.36: on a countable target space, null-measurable singleton fibers already
give almost-everywhere measurability of the function. -/
private theorem aemeasurable_of_countable_preimage_singleton_nullMeasurableSet
    {β : Type*} [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    {f : Ω → β} {μ : Measure Ω}
    (hfiber : ∀ x : β, NullMeasurableSet (f ⁻¹' ({x} : Set β)) μ) :
    AEMeasurable f μ := by
  have hmeas : @Measurable (NullMeasurableSpace Ω μ) β _ _ f := by
    -- Proof comment: in the completed measure space, null-measurable singleton fibers become
    -- genuinely measurable singleton fibers, so `measurable_to_countable'` applies.
    refine measurable_to_countable' ?_
    intro x
    exact hfiber x
  have hnull : NullMeasurable f μ := hmeas
  -- Proof comment: measurable maps on the completed space are null measurable for `μ`, and
  -- countably generated target spaces upgrade null measurability to a.e.-measurability.
  exact hnull.aemeasurable

/-- Helper for Theorem 5.36: if a countable-valued random variable has null-measurable singleton
fibers with the correct singleton masses, then those singleton masses determine its full law. -/
private theorem hasLaw_of_countable_preimage_singleton
    {β : Type*} [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    {f : Ω → β} {μ : Measure Ω} {ν : Measure β}
    (hfiber : ∀ x : β, NullMeasurableSet (f ⁻¹' ({x} : Set β)) μ)
    (hmass : ∀ x : β, μ (f ⁻¹' ({x} : Set β)) = ν ({x} : Set β)) :
    HasLaw f ν μ := by
  have hf : AEMeasurable f μ :=
    aemeasurable_of_countable_preimage_singleton_nullMeasurableSet hfiber
  refine ⟨hf, ?_⟩
  refine Measure.ext_of_singleton (μ := Measure.map f μ) (ν := ν) ?_
  intro x
  -- Proof comment: on a countable discrete codomain, equality of all singleton masses determines
  -- the whole pushforward measure.
  rw [Measure.map_apply_of_aemeasurable hf (measurableSet_singleton x)]
  exact hmass x

/-- Helper for Theorem 5.36: the singleton mass of `poissonMeasure r` is the explicit Poisson
weight `poissonPMFReal r n`. -/
private lemma poissonMeasure_apply_singleton (r : NNReal) (n : ℕ) :
    poissonMeasure r ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r n) := by
  -- Proof comment: rewrite the Poisson measure as the measure associated to its PMF.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF r) n (measurableSet_singleton n))

/-- Helper for Theorem 5.36: every singleton fiber of the finite increment vector is
null-measurable. The route passes through measurable modifications of the interarrivals, because
`HasLaw` only gives almost-everywhere measurability of the coordinates. -/
private theorem renewalIncrementFinGrid_singletonFiber_nullMeasurable_of_iid_exponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    {m : ℕ} (u : Fin (m + 1) → NNReal) (k : Fin m → ℕ) :
    NullMeasurableSet
      ({ω |
          (fun i : Fin m ↦
            renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω) = k})
      μ := by
  let Wm : ℕ → Ω → ℝ :=
    fun n ↦ (interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law n).aemeasurable.mk (W n)
  have hWm_meas : ∀ n, Measurable (Wm n) := by
    intro n
    -- Proof comment: each measurable modification is the `mk` representative of the corresponding
    -- interarrival coordinate.
    exact (interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law n).aemeasurable.measurable_mk
  let f : Ω → Fin m → ℕ := fun ω i ↦
    renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω
  let fm : Ω → Fin m → ℕ := fun ω i ↦
    renewalCountingProcess Wm (u i.succ) ω - renewalCountingProcess Wm (u i.castSucc) ω
  have hfm_meas : Measurable fm := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    have hpair :
        Measurable
          (fun ω ↦
            (renewalCountingProcess Wm (u i.succ) ω, renewalCountingProcess Wm (u i.castSucc) ω)) :=
      (renewalCountingProcess_measurable Wm hWm_meas (u i.succ)).prodMk
        (renewalCountingProcess_measurable Wm hWm_meas (u i.castSucc))
    have hsub : Measurable (fun p : ℕ × ℕ ↦ p.1 - p.2) := measurable_of_countable _
    -- Proof comment: subtraction on `ℕ × ℕ` is measurable because the domain is countable.
    exact hsub.comp hpair
  have hf_ae_eq : f =ᵐ[μ] fm := by
    have hWm_ae :
        ∀ᵐ ω ∂μ, ∀ n : ℕ, W n ω = Wm n ω := by
      refine ae_all_iff.2 fun n ↦ ?_
      exact (interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law n).aemeasurable.ae_eq_mk
    filter_upwards [hWm_ae] with ω hω
    funext i
    have harrival : ∀ n : ℕ, arrivalTime W n ω = arrivalTime Wm n ω := by
      intro n
      simp [arrivalTime, hω]
    have hpath :
        ∀ t : NNReal, renewalCountingProcess W t ω = renewalCountingProcess Wm t ω := by
      intro t
      have hgood_iff :
          (0 < arrivalTime W 1 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) ↔
            (0 < arrivalTime Wm 1 ω ∧ Tendsto (fun n ↦ arrivalTime Wm n ω) atTop atTop) := by
        constructor
        · intro hgood
          refine ⟨?_, ?_⟩
          · simpa [harrival 1] using hgood.1
          · simpa [funext harrival] using hgood.2
        · intro hgood
          refine ⟨?_, ?_⟩
          · simpa [harrival 1] using hgood.1
          · simpa [funext harrival] using hgood.2
      have hraw :
          rawRenewalCountingProcess W t ω = rawRenewalCountingProcess Wm t ω := by
        have hset :
            ({n : ℕ | t < arrivalTime W (n + 1) ω} : Set ℕ) =
              {n : ℕ | t < arrivalTime Wm (n + 1) ω} := by
          ext n
          change (t : ℝ) < arrivalTime W (n + 1) ω ↔ (t : ℝ) < arrivalTime Wm (n + 1) ω
          rw [harrival (n + 1)]
        rw [rawRenewalCountingProcess, rawRenewalCountingProcess, hset]
      by_cases hgood :
          0 < arrivalTime W 1 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop
      · have hgoodm :
            0 < arrivalTime Wm 1 ω ∧ Tendsto (fun n ↦ arrivalTime Wm n ω) atTop atTop :=
          hgood_iff.mp hgood
        by_cases h1 :
            0 < arrivalTime W 1 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop
        · by_cases h2 :
              0 < arrivalTime Wm 1 ω ∧ Tendsto (fun n ↦ arrivalTime Wm n ω) atTop atTop
          · -- Proof comment: on genuine renewal paths for both sequences, the public count uses
            -- the raw branch, and the raw counts already agree.
            have hw0 : 0 < W 0 ω := by
              simpa [arrivalTime_succ, arrivalTime_zero] using h1.1
            have hwm0 : 0 < Wm 0 ω := by
              simpa [arrivalTime_succ, arrivalTime_zero] using h2.1
            simpa [renewalCountingProcess, arrivalTime_succ, arrivalTime_zero, h1, h2, hraw,
              hw0, hwm0]
          · exact (h2 hgoodm).elim
        · exact (h1 hgood).elim
      · have hgoodm :
            ¬ (0 < arrivalTime Wm 1 ω ∧ Tendsto (fun n ↦ arrivalTime Wm n ω) atTop atTop) :=
          by
            intro hcontra
            exact hgood (hgood_iff.mpr hcontra)
        by_cases h1 :
            0 < arrivalTime W 1 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop
        · exact (hgood h1).elim
        · by_cases h2 :
              0 < arrivalTime Wm 1 ω ∧ Tendsto (fun n ↦ arrivalTime Wm n ω) atTop atTop
          · exact (hgoodm h2).elim
          · -- Proof comment: off the genuine-renewal event, both public representatives are reset
            -- to the zero process.
            have hbad0 :
                ¬ (0 < W 0 ω ∧ Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) := by
              simpa [arrivalTime_succ, arrivalTime_zero] using h1
            have hbadm0 :
                ¬ (0 < Wm 0 ω ∧ Tendsto (fun n ↦ arrivalTime Wm n ω) atTop atTop) := by
              simpa [arrivalTime_succ, arrivalTime_zero] using h2
            simpa [renewalCountingProcess, arrivalTime_succ, arrivalTime_zero, hbad0, hbadm0]
    -- Proof comment: once the whole interarrival path agrees pointwise, the public renewal count
    -- agrees at every time, hence so does the finite increment vector.
    simpa [f, fm, hpath (u i.succ), hpath (u i.castSucc)]
  have hf_ae : AEMeasurable f μ := hfm_meas.aemeasurable.congr hf_ae_eq.symm
  -- Proof comment: an a.e.-measurable countable-valued map has null-measurable singleton fibers.
  simpa [f, Set.preimage, Set.setOf_eq_eq_singleton] using
    hf_ae.nullMeasurableSet_preimage (measurableSet_singleton k)

/-- Helper for Theorem 5.36: for the public renewal-count representative, a zero-anchored finite
increment prescription already determines the endpoint counts by cumulative sums on every sample
path. Unlike the earlier arrival-strip route, this uses only the global zero-start and monotonicity
of `renewalCountingProcess`. -/
private theorem renewalIncrementFinGrid_iff_endpointCounts_public
    (W : ℕ → Ω → ℝ) {ω : Ω}
    {m : ℕ} {u : Fin (m + 1) → NNReal} (hu0 : u 0 = 0) (hu : Monotone u) (k : Fin m → ℕ) :
    (∀ i : Fin m,
        renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω = k i) ↔
      ∀ j : Fin (m + 1),
        renewalCountingProcess W (u j) ω =
          ∑ i ∈ Finset.range j.1, if hi : i < m then k ⟨i, hi⟩ else 0 := by
  let uNat : ℕ → NNReal := fun n ↦ u ⟨min n m, Nat.lt_succ_of_le (Nat.min_le_right n m)⟩
  let kNat : ℕ → ℕ := fun n ↦ if hn : n < m then k ⟨n, hn⟩ else 0
  have huNat0 : uNat 0 = 0 := by
    -- Proof comment: the constant extension of the finite grid preserves the zero anchor.
    simpa [uNat, hu0]
  have huNat : Monotone uNat := by
    -- Proof comment: the extension is `u` composed with `n ↦ min n m`, so monotonicity is
    -- inherited from the original finite grid.
    intro a b hab
    have hmin : min a m ≤ min b m := by
      omega
    exact hu (show (⟨min a m, Nat.lt_succ_of_le (Nat.min_le_right a m)⟩ : Fin (m + 1)) ≤
        ⟨min b m, Nat.lt_succ_of_le (Nat.min_le_right b m)⟩ by
      exact hmin)
  constructor
  · intro hinc
    have hX0 : renewalCountingProcess W (uNat 0) ω = 0 := by
      -- Proof comment: the public representative starts from `0` on every sample path.
      simpa [uNat, hu0] using congrFun (renewalCountingProcess_zero_eq W) ω
    have hXmono : Monotone (fun j : ℕ ↦ renewalCountingProcess W (uNat j) ω) := by
      -- Proof comment: the constant grid extension preserves time monotonicity of the public
      -- counting process.
      intro a b hab
      exact renewalCountingProcess_monotone W (huNat hab) ω
    have hincNat :
        ∀ i : ℕ,
          renewalCountingProcess W (uNat (i + 1)) ω - renewalCountingProcess W (uNat i) ω =
            kNat i := by
      intro i
      by_cases hi : i < m
      · have hi_le : i ≤ m := Nat.le_of_lt hi
        have hi_succ_le : i + 1 ≤ m := by
          omega
        -- Proof comment: before the last grid point, the extension agrees verbatim with the
        -- original finite grid.
        simpa [uNat, kNat, hi, Nat.min_eq_left hi_le, Nat.min_eq_left hi_succ_le] using
          hinc ⟨i, hi⟩
      · have hm_le : m ≤ i := Nat.le_of_not_gt hi
        have hconst :
            renewalCountingProcess W (uNat (i + 1)) ω =
              renewalCountingProcess W (uNat i) ω := by
          -- Proof comment: after the last finite grid point, the extension is constant, so every
          -- further increment vanishes.
          simp [uNat, Nat.min_eq_right hm_le,
            Nat.min_eq_right (le_trans hm_le (Nat.le_succ i))]
        simp [kNat, hi, hconst]
    have hendpointNat :
        ∀ j : ℕ, renewalCountingProcess W (uNat j) ω = ∑ i ∈ Finset.range j, kNat i :=
      (nat_increment_event_iff_endpoint_counts hX0 hXmono).1 hincNat
    intro j
    -- Proof comment: on the original finite grid indices, the constant extension recovers the
    -- desired endpoint-count formula unchanged.
    have hmin : min j.1 m = j.1 := by
      omega
    simpa [uNat, kNat, hmin] using hendpointNat j.1
  · intro hcount
    intro i
    have hi_mono :
        renewalCountingProcess W (u i.castSucc) ω ≤ renewalCountingProcess W (u i.succ) ω :=
      renewalCountingProcess_monotone W (hu (show i.castSucc ≤ i.succ by
        exact Nat.le_succ i.1)) ω
    have hi_prev :
        renewalCountingProcess W (u i.castSucc) ω =
          ∑ j ∈ Finset.range i.1, if hj : j < m then k ⟨j, hj⟩ else 0 :=
      hcount i.castSucc
    have hi_next :
        renewalCountingProcess W (u i.succ) ω =
          k i + ∑ j ∈ Finset.range i.1, if hj : j < m then k ⟨j, hj⟩ else 0 := by
      -- Proof comment: the next endpoint count adds exactly the current increment label `k i`.
      simpa [Finset.sum_range_succ, i.2, add_assoc, add_left_comm, add_comm] using
        hcount i.succ
    have hsum :
        renewalCountingProcess W (u i.succ) ω =
          k i + renewalCountingProcess W (u i.castSucc) ω := by
      calc
        renewalCountingProcess W (u i.succ) ω
            = k i + ∑ j ∈ Finset.range i.1, if hj : j < m then k ⟨j, hj⟩ else 0 := hi_next
        _ = k i + renewalCountingProcess W (u i.castSucc) ω := by
              rw [hi_prev]
    -- Proof comment: subtract the previous endpoint count from the next one.
    exact (Nat.sub_eq_iff_eq_add hi_mono).2 hsum

/-- Helper for Theorem 5.36: on a zero-anchored finite grid, the increment prescription fixes the
count at the last grid point to the cumulative sum of the prescribed increments. -/
private theorem zeroAnchoredRenewalIncrementPrefixCount_public
    (W : ℕ → Ω → ℝ) {ω : Ω}
    {m : ℕ} {u : Fin (m + 1) → NNReal} (hu0 : u 0 = 0) (hu : Monotone u) (k : Fin m → ℕ)
    (hinc : ∀ i : Fin m,
      renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω = k i) :
    renewalCountingProcess W (u (Fin.last m)) ω = ∑ i : Fin m, k i := by
  have hendpoint :=
    (renewalIncrementFinGrid_iff_endpointCounts_public W (ω := ω) hu0 hu k).1 hinc (Fin.last m)
  -- Proof comment: specialize the endpoint-count identity to the terminal grid point and rewrite
  -- the range sum as a `Fin`-indexed sum.
  calc
    renewalCountingProcess W (u (Fin.last m)) ω
        = ∑ i ∈ Finset.range m, if hi : i < m then k ⟨i, hi⟩ else 0 := hendpoint
    _ = ∑ i : Fin m, k i := by
          rw [← Fin.sum_univ_eq_sum_range]
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [hi]

/-- Helper for Theorem 5.36: in the snoc step, the prefix increments determine the count at the
penultimate grid point by their cumulative sum. This removes the remaining grid bookkeeping from
the final singleton-mass argument. -/
private theorem zeroAnchoredRenewalIncrementPenultimateCount_public
    (W : ℕ → Ω → ℝ) {ω : Ω}
    {m : ℕ} {u : Fin (m + 2) → NNReal} (hu0 : u 0 = 0) (hu : Monotone u)
    (k : Fin (m + 1) → ℕ)
    (hinc : ∀ i : Fin (m + 1),
      renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω = k i) :
    renewalCountingProcess W (u (Fin.castSucc (Fin.last m))) ω =
      ∑ i : Fin m, k i.castSucc := by
  let uPrefix : Fin (m + 1) → NNReal := fun j ↦ u j.castSucc
  have huPrefix0 : uPrefix 0 = 0 := by
    -- Proof comment: dropping the last grid point preserves the zero anchor.
    simpa [uPrefix] using hu0
  have huPrefix : Monotone uPrefix := by
    -- Proof comment: the prefix grid is the original grid precomposed with `Fin.castSucc`.
    intro a b hab
    exact hu (show a.castSucc ≤ b.castSucc by simpa using hab)
  have hprefix :
      ∀ i : Fin m,
        renewalCountingProcess W (uPrefix i.succ) ω -
            renewalCountingProcess W (uPrefix i.castSucc) ω =
          (fun i : Fin m ↦ k i.castSucc) i := by
    intro i
    -- Proof comment: the prefix increments are exactly the nonterminal coordinates of the snoc
    -- increment vector.
    simpa [uPrefix] using hinc i.castSucc
  -- Proof comment: apply the previous cumulative-count lemma to the prefix grid.
  simpa [uPrefix] using
    zeroAnchoredRenewalIncrementPrefixCount_public
      W (ω := ω) (u := uPrefix) huPrefix0 huPrefix (fun i : Fin m ↦ k i.castSucc) hprefix

/-- Helper for Theorem 5.36: splitting the first `K + l + 1` interarrivals into the prefix block
`W 0, ..., W (K - 1)` and the contiguous block `W K, ..., W (K + l)` gives the corresponding
product exponential law. -/
private theorem prefixBlockPairHasLawOfIidExponential
    (μ : Measure Ω) [IsProbabilityMeasure μ] (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α)
    (K l : ℕ) :
    HasLaw
      (fun ω ↦ ((fun i : Fin K ↦ W i ω), fun i : Fin (l + 1) ↦ W (K + i) ω))
      ((Measure.pi (fun _ : Fin K ↦ expMeasure α)).prod
        (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α))) μ := by
  letI : IsProbabilityMeasure (expMeasure α) := isProbabilityMeasure_expMeasure hα
  let e₁ : (Fin (K + (l + 1)) → ℝ) ≃ᵐ ((Fin K ⊕ Fin (l + 1)) → ℝ) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (K + (l + 1)) ↦ ℝ) finSumFinEquiv).symm
  let e₂ : ((Fin K ⊕ Fin (l + 1)) → ℝ) ≃ᵐ (Fin K → ℝ) × (Fin (l + 1) → ℝ) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin K ⊕ Fin (l + 1) ↦ ℝ)
  have hFullLaw :
      HasLaw
        (fun ω ↦ fun i : Fin (K + (l + 1)) ↦ W i ω)
        (Measure.pi (fun _ : Fin (K + (l + 1)) ↦ expMeasure α)) μ :=
    iid_exponential_prefix_hasLaw_pi μ α W hW_iid hW0_law (K + (l + 1))
  have hReindexLaw :
      HasLaw
        e₁
        (Measure.pi (fun _ : Fin K ⊕ Fin (l + 1) ↦ expMeasure α))
        (Measure.pi (fun _ : Fin (K + (l + 1)) ↦ expMeasure α)) := by
    -- Proof comment: reindex the first `K + l + 1` coordinates by the canonical
    -- `Fin K ⊕ Fin (l + 1) ≃ Fin (K + l + 1)` equivalence.
    exact
      ((measurePreserving_piCongrLeft
        (fun _ : Fin (K + (l + 1)) ↦ expMeasure α)
        finSumFinEquiv).symm).hasLaw
  have hSplitLaw :
      HasLaw
        e₂
        ((Measure.pi (fun _ : Fin K ↦ expMeasure α)).prod
          (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)))
        (Measure.pi (fun _ : Fin K ⊕ Fin (l + 1) ↦ expMeasure α)) := by
    -- Proof comment: after reindexing, separate the sum-indexed function space into its prefix
    -- and tail components once.
    exact
      (measurePreserving_sumPiEquivProdPi
        (fun _ : Fin K ⊕ Fin (l + 1) ↦ expMeasure α)).hasLaw
  refine (hSplitLaw.fun_comp (hReindexLaw.fun_comp hFullLaw)).congr ?_
  filter_upwards [] with ω
  apply Prod.ext
  · funext i
    -- Proof comment: the left component is exactly the first `K` coordinates.
    change W (Fin.castAdd (l + 1) i) ω = W i ω
    rfl
  · funext i
    -- Proof comment: the right component is the contiguous block starting at coordinate `K`.
    change W (Fin.natAdd K i) ω = W (K + i) ω
    rfl

/-- Helper for Theorem 5.36: subtracting the residual gap from the first coordinate of a block
tuple transports the shifted relative strip to the zero-anchored strip. -/
private theorem relativeBlockStrip_headShift_preimage_eq_zeroAnchored
    (l : ℕ) (r d : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    let shiftHead : (Fin (l + 1) → ℝ) → Fin (l + 1) → ℝ :=
      fun y ↦ Function.update y 0 (y 0 - r)
    shiftHead ⁻¹'
        {z : Fin (l + 1) → ℝ |
          0 < z 0 ∧ (∑ i : Fin l, z i.castSucc) ≤ d ∧ d < ∑ i : Fin (l + 1), z i} =
      {y : Fin (l + 1) → ℝ |
        r < y 0 ∧ (∑ i : Fin l, y i.castSucc) ≤ r + d ∧ r + d < ∑ i : Fin (l + 1), y i} := by
  classical
  dsimp
  cases l with
  | zero =>
      ext y
      change
        (0 < Function.update y 0 (y 0 - r) 0 ∧
            (∑ i : Fin 0, Function.update y 0 (y 0 - r) i.castSucc) ≤ d ∧
            d < ∑ i : Fin 1, Function.update y 0 (y 0 - r) i) ↔
          (r < y 0 ∧ (∑ i : Fin 0, y i.castSucc) ≤ r + d ∧ r + d < ∑ i : Fin 1, y i)
      -- Proof comment: in dimension `1`, the prefix sums vanish and only the shifted head
      -- coordinate remains.
      simp [hd]
      intro hy0
      constructor
      · intro hyd
        refine ⟨?_, ?_⟩
        · linarith [hr, hd]
        · linarith
      · rintro ⟨_, hyd⟩
        linarith
  | succ l =>
      ext y
      let shiftHead : Fin (Nat.succ (Nat.succ l)) → ℝ := Function.update y 0 (y 0 - r)
      have hhead : shiftHead 0 = y 0 - r := by
        simp [shiftHead]
      have hsucc :
          ∀ i : Fin (Nat.succ l), shiftHead i.succ = y i.succ := by
        intro i
        simp [shiftHead]
      have htailSucc :
          ∑ i : Fin (Nat.succ l), shiftHead i.succ =
            ∑ i : Fin (Nat.succ l), y i.succ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact hsucc i
      have htotal :
          ∑ i : Fin (Nat.succ (Nat.succ l)), shiftHead i =
            ∑ i : Fin (Nat.succ (Nat.succ l)), y i - r := by
        have hsumShift :
            ∑ i : Fin (Nat.succ (Nat.succ l)), shiftHead i =
              shiftHead 0 + ∑ i : Fin (Nat.succ l), shiftHead i.succ := by
          simpa [add_comm, add_left_comm, add_assoc] using Fin.sum_univ_succ shiftHead
        have hsumY :
            ∑ i : Fin (Nat.succ (Nat.succ l)), y i =
              y 0 + ∑ i : Fin (Nat.succ l), y i.succ := by
          simpa [add_comm, add_left_comm, add_assoc] using Fin.sum_univ_succ y
        -- Proof comment: the head update only subtracts `r` from coordinate `0`; all successor
        -- coordinates stay unchanged.
        rw [hsumShift, hsumY, hhead, htailSucc]
        ring
      have hlast :
          shiftHead (Fin.last (Nat.succ l)) = y (Fin.last (Nat.succ l)) := by
        have hne : (0 : Fin (Nat.succ (Nat.succ l))) ≠ Fin.last (Nat.succ l) := by
          simpa using (Fin.castSucc_ne_last (0 : Fin (Nat.succ l)))
        -- Proof comment: once the block has at least two coordinates, the head shift leaves the
        -- terminal coordinate unchanged.
        simp [shiftHead, hne]
      have hprefix :
          ∑ i : Fin (Nat.succ l), shiftHead i.castSucc =
            ∑ i : Fin (Nat.succ l), y i.castSucc - r := by
        have hsumShift :
            ∑ i : Fin (Nat.succ (Nat.succ l)), shiftHead i =
              ∑ i : Fin (Nat.succ l), shiftHead i.castSucc +
                shiftHead (Fin.last (Nat.succ l)) := by
          simpa [add_comm, add_left_comm, add_assoc] using Fin.sum_univ_castSucc shiftHead
        have hsumY :
            ∑ i : Fin (Nat.succ (Nat.succ l)), y i =
              ∑ i : Fin (Nat.succ l), y i.castSucc + y (Fin.last (Nat.succ l)) := by
          simpa [add_comm, add_left_comm, add_assoc] using Fin.sum_univ_castSucc y
        -- Proof comment: the shift lowers the total block sum by `r` and keeps the last
        -- coordinate fixed, so the prefix sum lowers by exactly `r`.
        linarith
      change
        (0 < shiftHead 0 ∧
            (∑ i : Fin (Nat.succ l), shiftHead i.castSucc) ≤ d ∧
            d < ∑ i : Fin (Nat.succ (Nat.succ l)), shiftHead i) ↔
          (r < y 0 ∧
            (∑ i : Fin (Nat.succ l), y i.castSucc) ≤ r + d ∧
            r + d < ∑ i : Fin (Nat.succ (Nat.succ l)), y i)
      constructor
      · rintro ⟨hy0, hyprefix, hsum⟩
        -- Proof comment: rewrite the shifted head, prefix sum, and total sum once, then finish by
        -- linear arithmetic.
        have hy0' : 0 < y 0 - r := by simpa [hhead] using hy0
        have hyprefix' : ∑ i : Fin (Nat.succ l), y i.castSucc - r ≤ d := by
          simpa [hprefix] using hyprefix
        have hsum' : d < ∑ i : Fin (Nat.succ (Nat.succ l)), y i - r := by
          simpa [htotal] using hsum
        refine ⟨?_, ?_, ?_⟩
        · linarith
        · linarith
        · linarith
      · rintro ⟨hy0, hyprefix, hsum⟩
        -- Proof comment: the converse direction uses the same three rewrite identities.
        have hy0' : 0 < y 0 - r := by
          linarith
        have hyprefix' : ∑ i : Fin (Nat.succ l), y i.castSucc - r ≤ d := by
          linarith
        have hsum' : d < ∑ i : Fin (Nat.succ (Nat.succ l)), y i - r := by
          linarith
        have hy0'' : 0 < shiftHead 0 := by
          simpa [hhead] using hy0'
        have hyprefix'' : ∑ i : Fin (Nat.succ l), shiftHead i.castSucc ≤ d := by
          simpa [hprefix] using hyprefix'
        have hsum'' : d < ∑ i : Fin (Nat.succ (Nat.succ l)), shiftHead i := by
          simpa [htotal] using hsum'
        exact ⟨hy0'', hyprefix'', hsum''⟩

/-- Helper for Theorem 5.36: after splitting off the terminal coordinate of a zero-anchored strip
with at least two coordinates, the remaining prefix is exactly the `castSucc` block. -/
private theorem zeroAnchoredBlockStrip_piFinLast_preimage_eq_succ
    (l : ℕ) (d : ℝ) :
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (l + 2) ↦ ℝ) (Fin.last (l + 1))).symm ⁻¹'
        {z : Fin (l + 2) → ℝ |
          0 < z 0 ∧ (∑ i : Fin (l + 1), z i.castSucc) ≤ d ∧ d < ∑ i : Fin (l + 2), z i}) =
      {p : ℝ × (Fin (l + 1) → ℝ) |
        0 < p.2 0 ∧ (∑ i, p.2 i) ≤ d ∧ d < p.1 + ∑ i, p.2 i} := by
  -- Route correction: the abandoned coordinate-`0` split normalized the wrong prefix sum
  -- (`Fin.castSucc` omits the last coordinate, not the head). The live route splits off the last
  -- coordinate and then analyzes genuine head sections on the remaining block.
  ext p
  rcases p with ⟨x, y⟩
  have hprefix :
      (∑ i : Fin (l + 1),
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (l + 2) ↦ ℝ) (Fin.last (l + 1))).symm
            (x, y)) i.castSucc) =
        ∑ i : Fin (l + 1), y i := by
    -- Proof comment: after splitting off the last coordinate, the `castSucc` prefix is exactly
    -- the remaining `Fin (l + 1)` block.
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.snoc_castSucc]
  have htotal :
      (∑ i : Fin (l + 2),
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (l + 2) ↦ ℝ) (Fin.last (l + 1))).symm
            (x, y)) i) =
        ∑ i : Fin (l + 1), y i + x := by
    -- Proof comment: the total block sum is the prefix sum plus the split terminal coordinate.
    simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.snoc_castSucc,
      Fin.snoc_last, add_comm, add_left_comm, add_assoc] using
      (Fin.sum_univ_castSucc (f := Fin.snoc y x))
  -- Proof comment: once the prefix and total sums are normalized, the transported strip is the
  -- explicit last-split head/tail region.
  simp [Set.mem_preimage, Set.mem_setOf_eq, hprefix, htotal, add_comm, add_left_comm, add_assoc]

/-- Helper for Theorem 5.36: for a fixed tail, the zero-anchored head section is the single tail
set `Ioi (d - ∑ i, y i)` exactly on the simplex branch `∑ i, y i ≤ d`. -/
private theorem zeroAnchoredBlockStrip_headSection_eq
    (l : ℕ) (d : ℝ) (y : Fin l → ℝ) :
    (fun x : ℝ ↦ (x, y)) ⁻¹'
        {p : ℝ × (Fin l → ℝ) | 0 < p.1 ∧ (∑ i, p.2 i) ≤ d ∧ d < p.1 + ∑ i, p.2 i} =
      if hsum : ∑ i, y i ≤ d then Set.Ioi (d - ∑ i, y i) else ∅ := by
  ext x
  by_cases hsum : ∑ i, y i ≤ d
  · constructor
    · intro hx
      change (x, y) ∈
          {p : ℝ × (Fin l → ℝ) | 0 < p.1 ∧ (∑ i, p.2 i) ≤ d ∧ d < p.1 + ∑ i, p.2 i} at hx
      simp only [Set.mem_setOf_eq] at hx
      have hx' : d - ∑ i, y i < x := by
        linarith [hx.2.2]
      simpa [hsum] using hx'
    · intro hx
      have hx' : d - ∑ i, y i < x := by
        simpa [hsum] using hx
      have hx0 : 0 < x := by
        linarith
      have hxd : d < x + ∑ i, y i := by
        linarith
      change (x, y) ∈
          {p : ℝ × (Fin l → ℝ) | 0 < p.1 ∧ (∑ i, p.2 i) ≤ d ∧ d < p.1 + ∑ i, p.2 i}
      simp [hx0, hsum, hxd]
  · simp [Set.mem_preimage, Set.mem_setOf_eq, hsum]

/-- Helper for Theorem 5.36: the one-dimensional section of the zero-anchored strip has the
explicit exponential tail mass on the simplex branch and vanishes off that branch. -/
private theorem zeroAnchoredBlockStrip_headSection_real
    {α : ℝ} (hα : 0 < α) (l : ℕ) (d : ℝ) (y : Fin l → ℝ) :
    (expMeasure α).real
      ((fun x : ℝ ↦ (x, y)) ⁻¹'
        {p : ℝ × (Fin l → ℝ) | 0 < p.1 ∧ (∑ i, p.2 i) ≤ d ∧ d < p.1 + ∑ i, p.2 i}) =
      if hsum : ∑ i, y i ≤ d then Real.exp (-(α * (d - ∑ i, y i))) else 0 := by
  -- Proof comment: first identify the section as a single exponential tail on the active simplex
  -- branch, and as the empty set off that branch.
  rw [zeroAnchoredBlockStrip_headSection_eq]
  by_cases hsum : ∑ i, y i ≤ d
  · have hdiff_nonneg : 0 ≤ d - ∑ i, y i := sub_nonneg.mpr hsum
    simp [hsum, expMeasure_real_Ioi_eq_exp_of_nonneg hα hdiff_nonneg]
  · simp [hsum]

/-- Helper for Theorem 5.36: a volume-preserving measurable equivalence transports a
`withDensity` measure by precomposing the density with the inverse equivalence. -/
private lemma mapWithDensityOfVolumePreserving {α β : Type*}
    [MeasureSpace α] [MeasureSpace β]
    (e : α ≃ᵐ β) (hpres : MeasurePreserving e volume volume)
    (g : α → ENNReal) (hg : Measurable g) :
    Measure.map e (volume.withDensity g) =
      volume.withDensity (fun y : β ↦ g (e.symm y)) := by
  refine Measure.ext fun s hs ↦ ?_
  -- Proof comment: evaluate both measures on the same measurable set and move the density through
  -- the volume-preserving equivalence once.
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ hs,
    withDensity_apply _ (e.measurable hs)]
  simpa using hpres.setLIntegral_comp_preimage hs (hg.comp e.symm.measurable)

/-- Helper for Theorem 5.36: on `Fin n`, the product of one-dimensional `withDensity` measures is
the `withDensity` measure of the coordinatewise product density. -/
private lemma piMarginalDensitiesFin_eq_withDensity_prodDensity {n : ℕ}
    (g : Fin n → ℝ → ENNReal) (hg : ∀ i, Measurable (g i))
    [∀ i, IsFiniteMeasure (volume.withDensity (g i))] :
    Measure.pi (fun i ↦ volume.withDensity (g i)) =
      volume.withDensity (fun x : Fin n → ℝ ↦ ∏ i, g i (x i)) := by
  induction n with
  | zero =>
      -- Proof comment: in dimension `0`, both measures are the unit mass on the unique point.
      calc
        Measure.pi (fun i : Fin 0 ↦ volume.withDensity (g i))
            = Measure.dirac (fun i ↦ i.elim0) := by
                simpa using
                  (Measure.pi_of_empty
                    (μ := fun i : Fin 0 ↦ volume.withDensity (g i))
                    (x := fun i ↦ i.elim0))
        _ = (volume : Measure (Fin 0 → ℝ)) := by
              simpa using
                (Measure.volume_pi_eq_dirac
                  (α := fun _ : Fin 0 ↦ ℝ) (x := fun i ↦ i.elim0)).symm
        _ = volume.withDensity (fun x : Fin 0 → ℝ ↦ ∏ i : Fin 0, g i (x i)) := by
              simp
  | succ n ihn =>
      let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0
      have htail_meas :
          Measurable (fun x : Fin n → ℝ ↦ ∏ i : Fin n, g i.succ (x i)) := by
        exact Finset.measurable_prod Finset.univ fun i _ ↦
          (hg i.succ).comp (continuous_apply i).measurable
      have hprod_meas :
          Measurable (fun x : Fin (n + 1) → ℝ ↦ ∏ i : Fin (n + 1), g i (x i)) := by
        exact Finset.measurable_prod Finset.univ fun i _ ↦
          (hg i).comp (continuous_apply i).measurable
      -- Route correction: decompose the finite product measure into head and tail coordinates
      -- before transporting the product density back to `Fin (n + 1)`.
      apply (MeasurableEmbedding.map_injective e.measurableEmbedding)
      calc
        Measure.map e (Measure.pi (fun i : Fin (n + 1) ↦ volume.withDensity (g i)))
            = (volume.withDensity (g 0)).prod
                (Measure.pi (fun i : Fin n ↦ volume.withDensity (g i.succ))) := by
              simpa [e] using
                (measurePreserving_piFinSuccAbove
                  (fun i : Fin (n + 1) ↦ volume.withDensity (g i)) 0).map_eq
        _ = (volume.withDensity (g 0)).prod
              (volume.withDensity (fun x : Fin n → ℝ ↦ ∏ i : Fin n, g i.succ (x i))) := by
              rw [ihn (g := fun i : Fin n ↦ g i.succ) (hg := fun i ↦ hg i.succ)]
        _ = ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))).withDensity
              (fun z : ℝ × (Fin n → ℝ) ↦ g 0 z.1 * ∏ i : Fin n, g i.succ (z.2 i)) := by
              rw [prod_withDensity (hg 0) htail_meas]
        _ = Measure.map e
              (volume.withDensity (fun x : Fin (n + 1) → ℝ ↦ ∏ i : Fin (n + 1), g i (x i))) := by
              symm
              simpa [e, hprod_meas, htail_meas, MeasurableEquiv.piFinSuccAbove_symm_apply,
                Fin.insertNthEquiv, Fin.prod_univ_succ, Fin.insertNth_zero, Fin.zero_succAbove,
                cast_eq, Fin.cons_zero, Fin.cons_succ] using
                mapWithDensityOfVolumePreserving
                  (e := e)
                  (hpres := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0)
                  (g := fun x : Fin (n + 1) → ℝ ↦ ∏ i : Fin (n + 1), g i (x i))
                  hprod_meas

/-- Helper for Theorem 5.36: the finite product exponential law on `Fin n` is the ambient volume
measure with density given by the coordinatewise product of exponential densities. -/
private theorem piExpMeasureFin_eq_withDensity_exponentialDensity
    {α : ℝ} (hα : 0 < α) (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ expMeasure α) =
      volume.withDensity
        (fun x : Fin n → ℝ ↦ ENNReal.ofReal (∏ i : Fin n, exponentialPDFReal α (x i))) := by
  letI : IsProbabilityMeasure (expMeasure α) := isProbabilityMeasure_expMeasure hα
  let g : Fin n → ℝ → ENNReal := fun _ ↦ exponentialPDF α
  let hfinite : ∀ i : Fin n, IsFiniteMeasure (volume.withDensity (g i)) := fun _ ↦ by
    -- Proof comment: each coordinate density is definitionally the exponential law, hence finite.
    simpa [g, expMeasure, gammaMeasure] using
      (inferInstance : IsFiniteMeasure (expMeasure α))
  -- Proof comment: package the finite product of one-dimensional exponential laws as a single
  -- `withDensity` measure via the existing finite-dimensional product-density lemma.
  have hpi :
      Measure.pi (fun i ↦ volume.withDensity (g i)) =
        volume.withDensity (fun x : Fin n → ℝ ↦ ∏ i : Fin n, g i (x i)) := by
    exact
      @piMarginalDensitiesFin_eq_withDensity_prodDensity n g
        (fun _ ↦ (measurable_exponentialPDFReal α).ennreal_ofReal) hfinite
  rw [expMeasure, gammaMeasure]
  -- Proof comment: after unfolding `expMeasure`, the remaining density is definitionally the
  -- exponential density.
  have hpi' :
      Measure.pi (fun _ : Fin n ↦ volume.withDensity (gammaPDF 1 α)) =
        volume.withDensity (fun x : Fin n → ℝ ↦ ∏ i : Fin n, exponentialPDF α (x i)) := by
    simpa [g, exponentialPDF, exponentialPDFReal] using hpi
  calc
    Measure.pi (fun _ : Fin n ↦ volume.withDensity (gammaPDF 1 α))
        = volume.withDensity (fun x : Fin n → ℝ ↦ ∏ i : Fin n, exponentialPDF α (x i)) := hpi'
    _ =
        volume.withDensity
          (fun x : Fin n → ℝ ↦ ENNReal.ofReal (∏ i : Fin n, exponentialPDFReal α (x i))) := by
            refine withDensity_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
            simpa [exponentialPDF] using
              (ENNReal.ofReal_prod_of_nonneg
                (s := Finset.univ)
                (f := fun i : Fin n ↦ exponentialPDFReal α (x i))
                (fun i _ ↦ exponentialPDFReal_nonneg hα (x i))).symm

/-- Helper for Theorem 5.36: integrate against the `Fin n` product exponential law by multiplying
with the explicit coordinatewise density against ambient volume. -/
private theorem integralPiExpMeasureFin_eq_integral_density
    {α : ℝ} (hα : 0 < α) {n : ℕ} {f : (Fin n → ℝ) → ℝ} :
    ∫ x, f x ∂(Measure.pi (fun _ : Fin n ↦ expMeasure α)) =
      ∫ x, (∏ i : Fin n, exponentialPDFReal α (x i)) * f x := by
  have hprod_meas :
      Measurable (fun x : Fin n → ℝ ↦ ∏ i : Fin n, exponentialPDFReal α (x i)) := by
    exact Finset.measurable_prod Finset.univ fun i _ ↦
      (measurable_exponentialPDFReal α).comp (continuous_apply i).measurable
  -- Proof comment: rewrite the product exponential law as a single `withDensity` measure, then
  -- collapse the real-valued density factor pointwise.
  rw [piExpMeasureFin_eq_withDensity_exponentialDensity hα]
  rw [integral_withDensity_eq_integral_toReal_smul (μ := volume)
    (f := fun x : Fin n → ℝ ↦ ENNReal.ofReal (∏ i : Fin n, exponentialPDFReal α (x i)))
    hprod_meas.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards with x
  have hnonneg : 0 ≤ ∏ i : Fin n, exponentialPDFReal α (x i) := by
    refine Finset.prod_nonneg fun i _ ↦ ?_
    exact exponentialPDFReal_nonneg hα (x i)
  simp [hnonneg, smul_eq_mul]

/-- Helper for Theorem 5.36: the transported head-tail zero-anchored strip is measurable. -/
private theorem measurableSet_zeroAnchoredHeadTailStrip
    (l : ℕ) (d : ℝ) :
    MeasurableSet
      {p : ℝ × (Fin l → ℝ) | 0 < p.1 ∧ (∑ i, p.2 i) ≤ d ∧ d < p.1 + ∑ i, p.2 i} := by
  have htailSum : Measurable (fun p : ℝ × (Fin l → ℝ) ↦ ∑ i : Fin l, p.2 i) :=
    (prefixSum_measurable l).comp measurable_snd
  have htotal : Measurable (fun p : ℝ × (Fin l → ℝ) ↦ p.1 + ∑ i : Fin l, p.2 i) :=
    measurable_fst.add htailSum
  -- Proof comment: each coordinate inequality is measurable because the head coordinate and tail
  -- sum are measurable real-valued functions.
  refine (measurable_fst measurableSet_Ioi).inter ?_
  refine (htailSum measurableSet_Iic).inter ?_
  exact htotal measurableSet_Ioi

/-- Helper for Theorem 5.36: in the one-dimensional base case, the zero-anchored strip mass is
the single exponential tail appearing on the right-hand side of the section formula. -/
private theorem zeroAnchoredBlockStrip_realMass_eq_tailIntegral_zero
    {α : ℝ} (hα : 0 < α) (d : ℝ) :
    (Measure.pi (fun _ : Fin 1 ↦ expMeasure α)).real
      {z : Fin 1 → ℝ | 0 < z 0 ∧ (∑ i : Fin 0, z i.castSucc) ≤ d ∧
          d < ∑ i : Fin 1, z i} =
        ∫ y : Fin 0 → ℝ,
          (if hsum : ∑ i, y i ≤ d then Real.exp (-(α * (d - ∑ i, y i))) else 0)
          ∂(Measure.pi (fun _ : Fin 0 ↦ expMeasure α)) := by
  let strip : Set (Fin 1 → ℝ) :=
    {z : Fin 1 → ℝ | 0 < z 0 ∧ (∑ i : Fin 0, z i.castSucc) ≤ d ∧ d < ∑ i : Fin 1, z i}
  let ray : Set ℝ := if hd : 0 ≤ d then Set.Ioi d else ∅
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.piUnique (fun _ : Fin 1 ↦ ℝ)
  have hem :
      MeasurePreserving e (Measure.pi (fun _ : Fin 1 ↦ expMeasure α)) (expMeasure α) := by
    simpa [e] using measurePreserving_piUnique (fun _ : Fin 1 ↦ expMeasure α)
  have htransport : e ⁻¹' ray = strip := by
    ext z
    -- Proof comment: on `Fin 1`, the unique coordinate is both the head and the total sum.
    by_cases hd : 0 ≤ d
    · constructor
      · intro hz
        have hz' : d < z 0 := by simpa [ray, e, hd] using hz
        have hpos : 0 < z 0 := by linarith
        simpa [strip, hd] using ⟨hpos, hz'⟩
      · intro hz
        have hz' : d < z 0 := by simpa [strip, hd] using hz.2
        simpa [ray, e, hd] using hz'
    · simp [ray, strip, e, hd]
  have hray_meas : MeasurableSet ray := by
    by_cases hd : 0 ≤ d
    · simp [ray, hd]
    · simp [ray, hd]
  have hmeasure :
      (Measure.pi (fun _ : Fin 1 ↦ expMeasure α)) strip = (expMeasure α) ray := by
    calc
      (Measure.pi (fun _ : Fin 1 ↦ expMeasure α)) strip
          = (Measure.pi (fun _ : Fin 1 ↦ expMeasure α)) (e ⁻¹' ray) := by
              rw [htransport]
      _ = Measure.map e (Measure.pi (fun _ : Fin 1 ↦ expMeasure α)) ray := by
            rw [Measure.map_apply e.measurable hray_meas]
      _ = (expMeasure α) ray := by
            rw [hem.map_eq]
  by_cases hd : 0 ≤ d
  · have hray_eq : ray = Set.Ioi d := by simp [ray, hd]
    have hpi0_univ : (Measure.pi (fun _ : Fin 0 ↦ expMeasure α)).real Set.univ = 1 := by
      rw [measureReal_def]
      simp
    -- Proof comment: for `d ≥ 0`, the strip is exactly the tail event `{x > d}` under the
    -- unique-coordinate equivalence.
    rw [measureReal_def, hmeasure, hray_eq, ← measureReal_def,
      expMeasure_real_Ioi_eq_exp_of_nonneg hα hd]
    simpa [hd, hpi0_univ]
  · have hray_eq : ray = ∅ := by
      simp [ray, hd]
    have hd_not : ¬ 0 ≤ d := hd
    -- Proof comment: for `d < 0`, both the strip and the right-hand integrand vanish.
    rw [measureReal_def, hmeasure, hray_eq]
    simp [hd_not]

/-- Helper for Theorem 5.36: the real mass of the zero-anchored strip is the outer tail integral
of the explicit one-dimensional head-section mass. -/
private theorem zeroAnchoredBlockStrip_realMass_eq_tailIntegral
    {α : ℝ} (hα : 0 < α) (l : ℕ) (d : ℝ) :
    (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)).real
      {z : Fin (l + 1) → ℝ | 0 < z 0 ∧ (∑ i : Fin l, z i.castSucc) ≤ d ∧
          d < ∑ i : Fin (l + 1), z i} =
        ∫ y : Fin l → ℝ,
          (if hsum : ∑ i, y i ≤ d then Real.exp (-(α * (d - ∑ i, y i))) else 0)
          ∂(Measure.pi (fun _ : Fin l ↦ expMeasure α)) := by
  cases l with
  | zero =>
      simpa using zeroAnchoredBlockStrip_realMass_eq_tailIntegral_zero hα d
  | succ l =>
      let μtail : Measure (Fin (l + 1) → ℝ) :=
        Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)
      let μprod : Measure (ℝ × (Fin (l + 1) → ℝ)) := (expMeasure α).prod μtail
      let strip : Set (Fin (l + 2) → ℝ) :=
        {z : Fin (l + 2) → ℝ |
          0 < z 0 ∧ (∑ i : Fin (l + 1), z i.castSucc) ≤ d ∧ d < ∑ i : Fin (l + 2), z i}
      let headTailSet : Set (ℝ × (Fin (l + 1) → ℝ)) :=
        {p : ℝ × (Fin (l + 1) → ℝ) | 0 < p.2 0 ∧ (∑ i, p.2 i) ≤ d ∧ d < p.1 + ∑ i, p.2 i}
      let e : (ℝ × (Fin (l + 1) → ℝ)) ≃ᵐ (Fin (l + 2) → ℝ) :=
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (l + 2) ↦ ℝ) (Fin.last (l + 1))).symm
      letI : IsProbabilityMeasure (expMeasure α) := isProbabilityMeasure_expMeasure hα
      letI : IsProbabilityMeasure μtail := by infer_instance
      letI : IsFiniteMeasure μprod := by infer_instance
      have hem :
          MeasurePreserving e μprod (Measure.pi (fun _ : Fin (l + 2) ↦ expMeasure α)) := by
        simpa [e, μtail, μprod] using
          ((measurePreserving_piFinSuccAbove
            (fun _ : Fin (l + 2) ↦ expMeasure α) (Fin.last (l + 1))).symm)
      have htransport : e ⁻¹' strip = headTailSet := by
        -- Proof comment: the `Fin.last` split turns the `castSucc` prefix into the full tail block.
        simpa [e, strip, headTailSet] using zeroAnchoredBlockStrip_piFinLast_preimage_eq_succ l d
      have htransport_symm : e.symm ⁻¹' headTailSet = strip := by
        -- Proof comment: invert the `Fin.last` transport once so measurability can be read on the
        -- original strip without any further rewrites.
        ext z
        have hz := Set.ext_iff.mp htransport (e.symm z)
        simpa [Set.mem_preimage] using hz.symm
      have hheadTail : MeasurableSet headTailSet := by
        have hprefixHead : Measurable (fun p : ℝ × (Fin (l + 1) → ℝ) ↦ p.2 0) :=
          (measurable_pi_apply 0).comp measurable_snd
        have htailSum :
            Measurable (fun p : ℝ × (Fin (l + 1) → ℝ) ↦ ∑ i : Fin (l + 1), p.2 i) :=
          (prefixSum_measurable (l + 1)).comp measurable_snd
        have htotal :
            Measurable (fun p : ℝ × (Fin (l + 1) → ℝ) ↦ p.1 + ∑ i : Fin (l + 1), p.2 i) :=
          measurable_fst.add htailSum
        -- Proof comment: after the `Fin.last` split, the positivity test lives on the first
        -- prefix coordinate `y 0`, while the other inequalities depend on the total tail sum.
        refine (hprefixHead measurableSet_Ioi).inter ?_
        refine (htailSum measurableSet_Iic).inter ?_
        exact htotal measurableSet_Ioi
      have hstrip : MeasurableSet strip := by
        rw [← htransport_symm]
        exact hheadTail.preimage e.symm.measurable
      have hindicator :
          Integrable (headTailSet.indicator (fun _ : ℝ × (Fin (l + 1) → ℝ) ↦ (1 : ℝ))) μprod := by
        -- Proof comment: the transported strip lives inside a finite product probability space.
        exact
          (integrableOn_const (μ := μprod) (s := headTailSet) (measure_ne_top _ _)).integrable_indicator
            hheadTail
      have h_pos_exp : ∀ᵐ x ∂expMeasure α, 0 < x := by
        rw [ae_iff]
        have h_nonpos_zero : expMeasure α {x : ℝ | ¬ 0 < x} = 0 := by
          rw [show {x : ℝ | ¬ 0 < x} = Set.Iic 0 by ext x; simp]
          have h_zero_iff :
              (expMeasure α).real (Set.Iic 0) = 0 ↔ expMeasure α (Set.Iic 0) = 0 :=
            measureReal_eq_zero_iff
          apply h_zero_iff.1
          have h_cdf_real : cdf (expMeasure α) 0 = (expMeasure α).real (Set.Iic 0) :=
            ProbabilityTheory.cdf_eq_real (expMeasure α) 0
          rw [← h_cdf_real]
          simpa using (ProbabilityTheory.cdf_expMeasure_eq hα 0)
        simpa using h_nonpos_zero
      have htail_pos_ae : ∀ᵐ y ∂μtail, 0 < y 0 := by
        let hevalLaw :
            HasLaw (Function.eval (0 : Fin (l + 1))) (expMeasure α) μtail :=
          (measurePreserving_eval
            (fun _ : Fin (l + 1) ↦ expMeasure α) (0 : Fin (l + 1))).hasLaw
        simpa using (hevalLaw.ae_iff (by fun_prop)).2 h_pos_exp
      have hsection_real :
          ∀ y : Fin (l + 1) → ℝ,
            (expMeasure α).real ((fun x : ℝ ↦ (x, y)) ⁻¹' headTailSet) =
              if hy0 : 0 < y 0 then
                if hsum : ∑ i, y i ≤ d then Real.exp (-(α * (d - ∑ i, y i))) else 0
              else 0 := by
        intro y
        by_cases hy0 : 0 < y 0
        · have hsection_eq :
            ((fun x : ℝ ↦ (x, y)) ⁻¹' headTailSet) =
              ((fun x : ℝ ↦ (x, y)) ⁻¹'
                {p : ℝ × (Fin (l + 1) → ℝ) |
                  0 < p.1 ∧ (∑ i, p.2 i) ≤ d ∧ d < p.1 + ∑ i, p.2 i}) := by
              ext x
              constructor
              · intro hx
                change 0 < y 0 ∧ (∑ i, y i) ≤ d ∧ d < x + ∑ i, y i at hx
                change 0 < x ∧ (∑ i, y i) ≤ d ∧ d < x + ∑ i, y i
                rcases hx with ⟨_, hsum, hupper⟩
                have hx0 : 0 < x := by
                  linarith
                exact ⟨hx0, hsum, hupper⟩
              · intro hx
                change 0 < y 0 ∧ (∑ i, y i) ≤ d ∧ d < x + ∑ i, y i
                change 0 < x ∧ (∑ i, y i) ≤ d ∧ d < x + ∑ i, y i at hx
                exact ⟨hy0, hx.2.1, hx.2.2⟩
          -- Proof comment: once `y 0 > 0`, the transported head section is the same tail ray as
          -- in the zero-anchored section formula.
          rw [hsection_eq, zeroAnchoredBlockStrip_headSection_real hα (l + 1) d y]
          simp [hy0]
        · have hsection_eq : ((fun x : ℝ ↦ (x, y)) ⁻¹' headTailSet) = ∅ := by
            ext x
            simp [headTailSet, hy0]
          simp [hsection_eq, hy0]
      have hsection_indicator :
          ∀ y : Fin (l + 1) → ℝ,
            ∫ x, headTailSet.indicator (fun _ : ℝ × (Fin (l + 1) → ℝ) ↦ (1 : ℝ)) (x, y)
                ∂expMeasure α =
              (expMeasure α).real ((fun x : ℝ ↦ (x, y)) ⁻¹' headTailSet) := by
        intro y
        have hsection_eq :
            (fun x : ℝ ↦
              headTailSet.indicator (fun _ : ℝ × (Fin (l + 1) → ℝ) ↦ (1 : ℝ)) (x, y)) =
              ((fun x : ℝ ↦ (x, y)) ⁻¹' headTailSet).indicator (fun _ : ℝ ↦ (1 : ℝ)) := by
          -- Proof comment: at fixed `y`, the product-space indicator is exactly the indicator of
          -- the one-dimensional head fiber.
          funext x
          simp [Set.indicator, Set.mem_preimage]
        have hsection_meas : MeasurableSet ((fun x : ℝ ↦ (x, y)) ⁻¹' headTailSet) := by
          exact hheadTail.preimage (by fun_prop)
        simpa [hsection_eq] using
          (integral_indicator_one
            (μ := expMeasure α)
            (s := ((fun x : ℝ ↦ (x, y)) ⁻¹' headTailSet))
            hsection_meas)
      -- Proof comment: transport the strip to the last-coordinate product space, apply Fubini
      -- once, then rewrite the one-dimensional head fibers by the closed section formula.
      calc
        (Measure.pi (fun _ : Fin (l + 2) ↦ expMeasure α)).real strip =
            ∫ z, strip.indicator (fun _ : Fin (l + 2) → ℝ ↦ (1 : ℝ)) z
              ∂(Measure.pi (fun _ : Fin (l + 2) ↦ expMeasure α)) := by
              simpa using
                (integral_indicator_one
                  (μ := Measure.pi (fun _ : Fin (l + 2) ↦ expMeasure α))
                  (s := strip)
                  hstrip).symm
        _ =
            ∫ p, strip.indicator (fun _ : Fin (l + 2) → ℝ ↦ (1 : ℝ)) (e p) ∂μprod := by
              rw [← hem.integral_comp' (strip.indicator (fun _ : Fin (l + 2) → ℝ ↦ (1 : ℝ)))]
        _ =
            ∫ p, headTailSet.indicator (fun _ : ℝ × (Fin (l + 1) → ℝ) ↦ (1 : ℝ)) p ∂μprod := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun p ↦ ?_
              by_cases hp : p ∈ headTailSet
              · have hpe : e p ∈ strip := by
                  have hp' : p ∈ e ⁻¹' strip := by
                    rw [htransport]
                    exact hp
                  simpa [Set.mem_preimage] using hp'
                simp [Set.indicator, hp, hpe]
              · have hpe : e p ∉ strip := by
                  intro hpe
                  have hp' : p ∈ e ⁻¹' strip := by
                    simpa [Set.mem_preimage] using hpe
                  exact hp (by rw [htransport] at hp'; exact hp')
                simp [Set.indicator, hp, hpe]
        _ =
            ∫ y, ∫ x,
              headTailSet.indicator (fun _ : ℝ × (Fin (l + 1) → ℝ) ↦ (1 : ℝ)) (x, y)
                ∂expMeasure α ∂μtail := by
              rw [integral_prod_symm _ hindicator]
        _ = ∫ y, (expMeasure α).real ((fun x : ℝ ↦ (x, y)) ⁻¹' headTailSet) ∂μtail := by
              refine integral_congr_ae <| Filter.Eventually.of_forall hsection_indicator
        _ =
            ∫ y : Fin (l + 1) → ℝ,
              if hy0 : 0 < y 0 then
                if hsum : ∑ i, y i ≤ d then Real.exp (-(α * (d - ∑ i, y i))) else 0
              else 0 ∂μtail := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
              simpa using hsection_real y
        _ =
            ∫ y : Fin (l + 1) → ℝ,
              (if hsum : ∑ i, y i ≤ d then Real.exp (-(α * (d - ∑ i, y i))) else 0) ∂μtail := by
              refine integral_congr_ae ?_
              filter_upwards [htail_pos_ae] with y hy
              simp [hy]

/-- Helper for Theorem 5.36: multiplying the tail product density with the head-section mass
collapses to the constant Poisson factor times the simplex indicator. -/
private theorem tailDensity_mul_headSection_eq_simplexIndicator
    {α : ℝ} (hα : 0 < α) {l : ℕ} {d : ℝ} (hd : 0 ≤ d) (y : Fin l → ℝ) :
    (∏ i : Fin l, exponentialPDFReal α (y i)) *
        (if hsum : ∑ i, y i ≤ d then Real.exp (-(α * (d - ∑ i, y i))) else 0) =
      Real.exp (-(α * d)) * (α : ℝ) ^ l *
        Set.indicator
          {z : Fin l → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ d}
          (fun _ : Fin l → ℝ ↦ (1 : ℝ)) y := by
  by_cases hsum : ∑ i, y i ≤ d
  · by_cases hnonneg : ∀ i, 0 ≤ y i
    · have hy_mem :
          y ∈ {z : Fin l → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ d} := ⟨hnonneg, hsum⟩
      have hpdf :
          ∏ i : Fin l, exponentialPDFReal α (y i) =
            (α : ℝ) ^ l * Real.exp (-(α * ∑ i : Fin l, y i)) := by
        -- Proof comment: on the simplex branch every coordinate density is the positive
        -- exponential kernel `α * exp (-(α * y i))`, so the product factors into the constant
        -- `α^l` and the exponential of the summed exponent.
        calc
          ∏ i : Fin l, exponentialPDFReal α (y i)
              = ∏ i : Fin l, (α * Real.exp (-(α * y i))) := by
                  refine Finset.prod_congr rfl ?_
                  intro i hi
                  simp [exponentialPDFReal, gammaPDFReal, hnonneg i]
          _ = (∏ _ : Fin l, α) * ∏ i : Fin l, Real.exp (-(α * y i)) := by
                rw [Finset.prod_mul_distrib]
          _ = (α : ℝ) ^ l * ∏ i : Fin l, Real.exp (-(α * y i)) := by
                simp
          _ = (α : ℝ) ^ l * Real.exp (∑ i : Fin l, -(α * y i)) := by
                rw [← Real.exp_sum]
          _ = (α : ℝ) ^ l * Real.exp (-(α * ∑ i : Fin l, y i)) := by
                have hsum_exp :
                    ∑ i : Fin l, -(α * y i) = -(α * ∑ i : Fin l, y i) := by
                  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
                rw [hsum_exp]
      have hmain :
          (∏ i : Fin l, exponentialPDFReal α (y i)) *
              Real.exp (-(α * (d - ∑ i : Fin l, y i))) =
            Real.exp (-(α * d)) * (α : ℝ) ^ l := by
        calc
          (∏ i : Fin l, exponentialPDFReal α (y i)) *
              Real.exp (-(α * (d - ∑ i : Fin l, y i)))
            =
              ((α : ℝ) ^ l * Real.exp (-(α * ∑ i : Fin l, y i))) *
                Real.exp (-(α * (d - ∑ i : Fin l, y i))) := by
                  rw [hpdf]
          _ =
              (α : ℝ) ^ l *
                (Real.exp (-(α * ∑ i : Fin l, y i)) *
                  Real.exp (-(α * (d - ∑ i : Fin l, y i)))) := by
                    ring
          _ =
              (α : ℝ) ^ l * Real.exp (-(α * d)) := by
                rw [← Real.exp_add]
                congr 2
                ring
          _ = Real.exp (-(α * d)) * (α : ℝ) ^ l := by
                ring
      simpa [hsum, Set.indicator_of_mem hy_mem] using hmain
    · have hy_not_mem :
          y ∉ {z : Fin l → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ d} := by
        simp [Set.mem_setOf_eq, hsum, hnonneg]
      push_neg at hnonneg
      rcases hnonneg with ⟨i, hi_neg⟩
      have hpdf_zero : exponentialPDFReal α (y i) = 0 := by
        simp [exponentialPDFReal, gammaPDFReal, hi_neg]
      -- Proof comment: a negative coordinate forces one exponential density factor to vanish, so
      -- the whole product density is zero while the simplex indicator is off.
      have hprod_zero : ∏ j : Fin l, exponentialPDFReal α (y j) = 0 := by
        simpa using
          (Finset.prod_eq_zero (s := Finset.univ) (i := i) (by simp) hpdf_zero)
      simpa [hsum, Set.indicator_of_notMem hy_not_mem, hprod_zero]
  · have hy_not_mem :
        y ∉ {z : Fin l → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ d} := by
      simp [Set.mem_setOf_eq, hsum]
    -- Proof comment: outside the simplex branch, both the head-section term and the indicator
    -- vanish immediately.
    simpa [hsum, Set.indicator_of_notMem hy_not_mem]

/-- Helper for Theorem 5.36: the real mass of the zero-anchored strip is the explicit Poisson
weight attached to the singleton `{l}`. -/
private theorem zeroAnchoredBlockStrip_real_eq_poissonWeight
    {α : ℝ} (hα : 0 < α) (l : ℕ) (d : NNReal) :
    (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)).real
      {z : Fin (l + 1) → ℝ | 0 < z 0 ∧ (∑ i : Fin l, z i.castSucc) ≤ d ∧
          d < ∑ i : Fin (l + 1), z i} =
        Real.exp (-(α * d)) * (α : ℝ) ^ l * (d : ℝ) ^ l / (Nat.factorial l : ℝ) := by
  have hd : 0 ≤ (d : ℝ) := d.2
  let simplex : Set (Fin l → ℝ) :=
    {z : Fin l → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ d}
  -- Route correction: package the density/Fubini calculation as a single strip-mass theorem,
  -- so the remaining snoc proof only has to transport the event and apply this closed formula.
  calc
    (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)).real
        {z : Fin (l + 1) → ℝ | 0 < z 0 ∧ (∑ i : Fin l, z i.castSucc) ≤ d ∧
            d < ∑ i : Fin (l + 1), z i}
      =
        ∫ y : Fin l → ℝ,
          (if hsum : ∑ i, y i ≤ d then Real.exp (-(α * (d - ∑ i, y i))) else 0)
          ∂(Measure.pi (fun _ : Fin l ↦ expMeasure α)) := by
          simpa using zeroAnchoredBlockStrip_realMass_eq_tailIntegral hα l d
    _ =
        ∫ y : Fin l → ℝ,
          (∏ i : Fin l, exponentialPDFReal α (y i)) *
            (if hsum : ∑ i, y i ≤ d then Real.exp (-(α * (d - ∑ i, y i))) else 0) := by
          rw [integralPiExpMeasureFin_eq_integral_density hα
            (f := fun y : Fin l → ℝ ↦
              if hsum : ∑ i, y i ≤ d then Real.exp (-(α * (d - ∑ i, y i))) else 0)]
    _ =
        ∫ y : Fin l → ℝ,
          Real.exp (-(α * d)) * (α : ℝ) ^ l *
            Set.indicator simplex (fun _ : Fin l → ℝ ↦ (1 : ℝ)) y := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
          simpa [simplex] using tailDensity_mul_headSection_eq_simplexIndicator hα hd y
    _ =
        Real.exp (-(α * d)) * (α : ℝ) ^ l *
          ∫ y : Fin l → ℝ, Set.indicator simplex (fun _ : Fin l → ℝ ↦ (1 : ℝ)) y := by
          rw [integral_const_mul]
    _ =
        Real.exp (-(α * d)) * (α : ℝ) ^ l * volume.real simplex := by
          have hindicator :
              ∫ y : Fin l → ℝ, Set.indicator simplex (fun _ : Fin l → ℝ ↦ (1 : ℝ)) y =
                volume.real simplex := by
            simpa using
              (integral_indicator_one
                (μ := (volume : Measure (Fin l → ℝ)))
                (s := simplex)
                (positiveSimplex_measurableSet l (d : ℝ)))
          rw [hindicator]
    _ =
        Real.exp (-(α * d)) * (α : ℝ) ^ l * ((d : ℝ) ^ l / (Nat.factorial l : ℝ)) := by
          rw [positiveSimplexReal_eq_pow_div_factorial l d hd]
    _ =
        Real.exp (-(α * d)) * (α : ℝ) ^ l * (d : ℝ) ^ l / (Nat.factorial l : ℝ) := by
          ring

/-- Helper for Theorem 5.36: the zero-anchored strip has exactly the singleton mass of the
Poisson law with parameter `α * d`. -/
private theorem zeroAnchoredBlockStrip_mass_eq_poissonSingleton
    {α : ℝ} (hα : 0 < α) (l : ℕ) (d : NNReal) :
    (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)).real
      {z : Fin (l + 1) → ℝ | 0 < z 0 ∧ (∑ i : Fin l, z i.castSucc) ≤ d ∧
          d < ∑ i : Fin (l + 1), z i} =
        (poissonMeasure (Real.toNNReal α * d)).real ({l} : Set ℕ) := by
  have hPoissonSingleton :
      (poissonMeasure (Real.toNNReal α * d)).real ({l} : Set ℕ) =
        poissonPMFReal (Real.toNNReal α * d) l := by
    -- Proof comment: a singleton real mass is the to-real of the corresponding Poisson PMF
    -- weight.
    rw [measureReal_def, poissonMeasure_apply_singleton,
      ENNReal.toReal_ofReal poissonPMFReal_nonneg]
  -- Proof comment: rewrite the singleton Poisson mass to the explicit PMF weight and compare it
  -- directly with the closed strip-mass formula.
  rw [measureReal_def]
  calc
    (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)).real
        {z : Fin (l + 1) → ℝ | 0 < z 0 ∧ (∑ i : Fin l, z i.castSucc) ≤ d ∧
            d < ∑ i : Fin (l + 1), z i}
      =
        Real.exp (-(α * d)) * (α : ℝ) ^ l * (d : ℝ) ^ l / (Nat.factorial l : ℝ) := by
          simpa using zeroAnchoredBlockStrip_real_eq_poissonWeight hα l d
    _ = poissonPMFReal (Real.toNNReal α * d) l := by
          have hαnn : ((Real.toNNReal α : NNReal) : ℝ) = α := by
            simp [Real.toNNReal, max_eq_left (le_of_lt hα)]
          rw [poissonPMFReal, NNReal.coe_mul, hαnn, mul_pow]
          ring
    _ = (poissonMeasure (Real.toNNReal α * d)).real ({l} : Set ℕ) := hPoissonSingleton.symm

/-- Helper for Theorem 5.36: the zero-anchored strip is measurable under the finite product
exponential law. -/
private theorem measurableSet_zeroAnchoredBlockStrip
    (l : ℕ) (d : ℝ) :
    MeasurableSet
      {z : Fin (l + 1) → ℝ | 0 < z 0 ∧ (∑ i : Fin l, z i.castSucc) ≤ d ∧
          d < ∑ i : Fin (l + 1), z i} := by
  have hhead : Measurable (fun z : Fin (l + 1) → ℝ ↦ z 0) := measurable_pi_apply 0
  have htail :
      Measurable (fun z : Fin (l + 1) → ℝ ↦ ∑ i : Fin l, z i.castSucc) := by
    exact Finset.measurable_sum Finset.univ fun i _ ↦ measurable_pi_apply i.castSucc
  have htotal : Measurable (fun z : Fin (l + 1) → ℝ ↦ ∑ i : Fin (l + 1), z i) :=
    prefixSum_measurable (l + 1)
  -- Proof comment: each strip inequality is the preimage of a measurable half-line under a
  -- coordinate sum map.
  refine (hhead measurableSet_Ioi).inter ?_
  refine (htail measurableSet_Iic).inter ?_
  exact htotal measurableSet_Ioi

/-- Helper for Theorem 5.36: translating the first coordinate of the finite exponential product
law by `r` multiplies the mass of sets supported on `{z | 0 < z 0}` by the exponential tail
factor `exp (-α r)`. -/
private theorem expProductHeadShift_measure_eq_expFactor_mul
    {α : ℝ} (hα : 0 < α) (l : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (s : Set (Fin (l + 1) → ℝ)) (hs : MeasurableSet s)
    (hs_head : s ⊆ {z : Fin (l + 1) → ℝ | 0 < z 0}) :
    (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α))
      ((fun y : Fin (l + 1) → ℝ ↦ Function.update y 0 (y 0 - r)) ⁻¹' s) =
      ENNReal.ofReal (Real.exp (-(α * r))) *
        (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)) s := by
  let shiftVec : Fin (l + 1) → ℝ := Function.update (0 : Fin (l + 1) → ℝ) 0 (-r)
  let e : (Fin (l + 1) → ℝ) ≃ᵐ (Fin (l + 1) → ℝ) := MeasurableEquiv.addRight shiftVec
  let density : (Fin (l + 1) → ℝ) → ENNReal :=
    fun x ↦ ENNReal.ofReal (∏ i : Fin (l + 1), exponentialPDFReal α (x i))
  have hdensity : Measurable density := by
    -- Proof comment: the product exponential density is a finite product of measurable
    -- coordinatewise densities.
    exact
      (Finset.measurable_prod Finset.univ fun i _ ↦
        (measurable_exponentialPDFReal α).comp (continuous_apply i).measurable).ennreal_ofReal
  have hshift :
      (fun y : Fin (l + 1) → ℝ ↦ Function.update y 0 (y 0 - r)) = fun y ↦ e y := by
    -- Proof comment: subtracting `r` from the zeroth coordinate is just right-translation by the
    -- vector `(-r, 0, ..., 0)`.
    funext y
    ext i
    by_cases hi : i = 0
    · subst hi
      simp [e, shiftVec, sub_eq_add_neg]
    · simp [e, shiftVec, hi]
  have hmapVolume :
      MeasurePreserving e (volume : Measure (Fin (l + 1) → ℝ)) volume := by
    -- Proof comment: ambient volume is translation invariant on the finite-dimensional function
    -- space.
    simpa [e] using
      (measurePreserving_add_right
        (μ := (volume : Measure (Fin (l + 1) → ℝ))) shiftVec)
  have hdensity_shift :
      ∀ y ∈ s,
        density (e.symm y) =
          ENNReal.ofReal (Real.exp (-(α * r))) * density y := by
    intro y hy
    have hy_head : 0 < y 0 := hs_head hy
    have hy0_nonneg : 0 ≤ y 0 := le_of_lt hy_head
    have hyr_nonneg : 0 ≤ y 0 + r := by
      linarith
    have hsymm :
        e.symm y = y + Function.update (0 : Fin (l + 1) → ℝ) 0 r := by
      -- Proof comment: the inverse translation adds back the removed gap in the zeroth
      -- coordinate.
      ext i
      by_cases hi : i = 0
      · subst hi
        simp [e, shiftVec]
      · simp [e, shiftVec, hi]
    have hheadDensity :
        exponentialPDFReal α (y 0 + r) =
          Real.exp (-(α * r)) * exponentialPDFReal α (y 0) := by
      calc
        exponentialPDFReal α (y 0 + r)
          = α * Real.exp (-(α * (y 0 + r))) := by
              simp [exponentialPDFReal, gammaPDFReal, hyr_nonneg]
        _ = α * (Real.exp (-(α * r)) * Real.exp (-(α * y 0))) := by
              congr 1
              rw [show -(α * (y 0 + r)) = -(α * r) + -(α * y 0) by ring, Real.exp_add]
        _ = Real.exp (-(α * r)) * exponentialPDFReal α (y 0) := by
              rw [show exponentialPDFReal α (y 0) = α * Real.exp (-(α * y 0)) by
                simp [exponentialPDFReal, gammaPDFReal, hy0_nonneg]]
              ring
    have htail :
        ∏ i : Fin l, exponentialPDFReal α ((e.symm y) i.succ) =
          ∏ i : Fin l, exponentialPDFReal α (y i.succ) := by
      -- Proof comment: the head translation leaves all tail coordinates unchanged.
      rw [hsymm]
      refine Finset.prod_congr rfl ?_
      intro i hi
      simp [shiftVec]
    have hprod :
        ∏ i : Fin (l + 1), exponentialPDFReal α ((e.symm y) i) =
          Real.exp (-(α * r)) * ∏ i : Fin (l + 1), exponentialPDFReal α (y i) := by
      -- Proof comment: after separating the zeroth coordinate, only the head density picks up
      -- the exponential factor.
      rw [hsymm, Fin.prod_univ_succ, Fin.prod_univ_succ]
      calc
        exponentialPDFReal α ((y + Function.update (0 : Fin (l + 1) → ℝ) 0 r) 0) *
            ∏ i : Fin l, exponentialPDFReal α ((y + Function.update (0 : Fin (l + 1) → ℝ) 0 r) i.succ)
          = exponentialPDFReal α (y 0 + r) *
              ∏ i : Fin l, exponentialPDFReal α (y i.succ) := by
                simp [shiftVec]
        _ = (Real.exp (-(α * r)) * exponentialPDFReal α (y 0)) *
              ∏ i : Fin l, exponentialPDFReal α (y i.succ) := by
                rw [hheadDensity]
        _ = Real.exp (-(α * r)) *
              (exponentialPDFReal α (y 0) * ∏ i : Fin l, exponentialPDFReal α (y i.succ)) := by
                ring
    have hprod_nonneg : 0 ≤ ∏ i : Fin (l + 1), exponentialPDFReal α (y i) := by
      refine Finset.prod_nonneg fun i _ ↦ exponentialPDFReal_nonneg hα (y i)
    have hexp_nonneg : 0 ≤ Real.exp (-(α * r)) := (Real.exp_pos _).le
    -- Proof comment: cast the real-valued density identity to `ENNReal` once the nonnegativity
    -- of both factors is known.
    simpa [density, ENNReal.ofReal_mul, hexp_nonneg, hprod_nonneg] using
      congrArg ENNReal.ofReal hprod
  rw [hshift, ← Measure.map_apply e.measurable hs]
  calc
    Measure.map e (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)) s
      = Measure.map e (volume.withDensity density) s := by
          rw [piExpMeasureFin_eq_withDensity_exponentialDensity hα]
    _ = (volume.withDensity (fun y : Fin (l + 1) → ℝ ↦ density (e.symm y))) s := by
          rw [mapWithDensityOfVolumePreserving e hmapVolume density hdensity]
    _ =
        ∫⁻ y in s, density (e.symm y) ∂(volume : Measure (Fin (l + 1) → ℝ)) := by
          rw [withDensity_apply _ hs]
    _ =
        ∫⁻ y in s, ENNReal.ofReal (Real.exp (-(α * r))) * density y
          ∂(volume : Measure (Fin (l + 1) → ℝ)) := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_mem hs] with y hy
          exact hdensity_shift y hy
    _ =
        ENNReal.ofReal (Real.exp (-(α * r))) *
          ∫⁻ y, density y ∂((volume : Measure (Fin (l + 1) → ℝ)).restrict s) := by
          simpa using
            (lintegral_const_mul'
              (μ := (volume : Measure (Fin (l + 1) → ℝ)).restrict s)
              (ENNReal.ofReal (Real.exp (-(α * r)))) density ENNReal.ofReal_ne_top)
    _ =
        ENNReal.ofReal (Real.exp (-(α * r))) *
          (volume.withDensity density) s := by
          rw [withDensity_apply _ hs]
    _ =
        ENNReal.ofReal (Real.exp (-(α * r))) *
          (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)) s := by
          rw [piExpMeasureFin_eq_withDensity_exponentialDensity hα]

/-- Helper for Theorem 5.36: under the product exponential law, the relative strip with residual
gap `r` has mass equal to the exponential tail above `r` times the matching Poisson singleton
mass. -/
private theorem relativeBlockStrip_mass_eq_headGap_mass_mul_poissonSingleton
    {α : ℝ} (hα : 0 < α) (l : ℕ) (r : ℝ) (hr : 0 ≤ r) (d : NNReal) :
    (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)).real
      {y : Fin (l + 1) → ℝ |
        r < y 0 ∧ (∑ i : Fin l, y i.castSucc) ≤ r + d ∧ r + d < ∑ i : Fin (l + 1), y i} =
      (expMeasure α).real (Set.Ioi r) *
        (poissonMeasure (Real.toNNReal α * d)).real ({l} : Set ℕ) := by
  letI : IsProbabilityMeasure (expMeasure α) := isProbabilityMeasure_expMeasure hα
  letI : IsFiniteMeasure (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)) := by infer_instance
  let zeroStrip : Set (Fin (l + 1) → ℝ) :=
    {z : Fin (l + 1) → ℝ | 0 < z 0 ∧ (∑ i : Fin l, z i.castSucc) ≤ d ∧
        d < ∑ i : Fin (l + 1), z i}
  have hzero_meas : MeasurableSet zeroStrip := measurableSet_zeroAnchoredBlockStrip l d
  have hzero_head : zeroStrip ⊆ {z : Fin (l + 1) → ℝ | 0 < z 0} := by
    intro z hz
    exact hz.1
  have hshift :
      ((fun y : Fin (l + 1) → ℝ ↦ Function.update y 0 (y 0 - r)) ⁻¹' zeroStrip) =
        {y : Fin (l + 1) → ℝ |
          r < y 0 ∧ (∑ i : Fin l, y i.castSucc) ≤ r + d ∧
            r + d < ∑ i : Fin (l + 1), y i} := by
    simpa [zeroStrip] using relativeBlockStrip_headShift_preimage_eq_zeroAnchored l r d hr d.2
  have hfactor :
      (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α))
        (((fun y : Fin (l + 1) → ℝ ↦ Function.update y 0 (y 0 - r)) ⁻¹' zeroStrip)) =
        ENNReal.ofReal (Real.exp (-(α * r))) *
          (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)) zeroStrip :=
    expProductHeadShift_measure_eq_expFactor_mul hα l r hr zeroStrip hzero_meas hzero_head
  have hmul_ne_top :
      ENNReal.ofReal (Real.exp (-(α * r))) *
          (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)) zeroStrip ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hexp_nonneg : 0 ≤ Real.exp (-(α * r)) := (Real.exp_pos _).le
  -- Proof comment: rewrite the relative strip as the first-coordinate head shift of the
  -- zero-anchored strip, then apply the closed zero-anchored singleton-mass formula.
  rw [← hshift, measureReal_def, hfactor, ENNReal.toReal_mul, ENNReal.toReal_ofReal hexp_nonneg,
    expMeasure_real_Ioi_eq_exp_of_nonneg hα hr]
  simpa [zeroStrip] using zeroAnchoredBlockStrip_mass_eq_poissonSingleton hα l d

/-- Helper for Theorem 5.36: the relative-strip factorization also holds at the level of the
actual product measure, not only after taking `Measure.real`. -/
private theorem relativeBlockStrip_measure_eq_headGap_measure_mul_poissonSingleton
    {α : NNReal} (hα : 0 < α) (l : ℕ) (r : ℝ) (hr : 0 ≤ r) (d : NNReal) :
    (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α))
      {y : Fin (l + 1) → ℝ |
        r < y 0 ∧ (∑ i : Fin l, y i.castSucc) ≤ r + d ∧ r + d < ∑ i : Fin (l + 1), y i} =
      (expMeasure α) (Set.Ioi r) * poissonMeasure (α * d) ({l} : Set ℕ) := by
  letI : IsProbabilityMeasure (expMeasure α) := isProbabilityMeasure_expMeasure hα
  letI : IsFiniteMeasure (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)) := by infer_instance
  have hα_real : 0 < (α : ℝ) := by
    exact_mod_cast hα
  have hmul_ne_top :
      (expMeasure α) (Set.Ioi r) * poissonMeasure (α * d) ({l} : Set ℕ) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  -- Proof comment: upgrade the already-proved real-mass identity by comparing `toReal` on both
  -- finite sides of the measure equality.
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hmul_ne_top, ENNReal.toReal_mul,
    ← measureReal_def, ← measureReal_def, ← measureReal_def]
  simpa using
    relativeBlockStrip_mass_eq_headGap_mass_mul_poissonSingleton
      (α := (α : ℝ)) hα_real l r hr d

/-- Helper for Theorem 5.36: under the finite product exponential law, the head-gap event depends
only on the zeroth coordinate and therefore has exactly the corresponding one-dimensional
exponential tail mass. -/
private theorem piExpMeasure_headGap_measure
    {α : NNReal} (hα : 0 < α) (l : ℕ) (r : ℝ) :
    (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α))
      {y : Fin (l + 1) → ℝ | r < y 0} =
      (expMeasure α) (Set.Ioi r) := by
  letI : IsProbabilityMeasure (expMeasure α) := isProbabilityMeasure_expMeasure hα
  have hpre :
      {y : Fin (l + 1) → ℝ | r < y 0} = (Function.eval (0 : Fin (l + 1))) ⁻¹' Set.Ioi r := by
    ext y
    simp [Set.preimage]
  -- Proof comment: push the product law forward by evaluation at the zeroth coordinate and use
  -- the canonical marginal law of that coordinate.
  calc
    (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α))
        {y : Fin (l + 1) → ℝ | r < y 0}
      = Measure.map (Function.eval (0 : Fin (l + 1)))
          (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)) (Set.Ioi r) := by
            rw [hpre, Measure.map_apply (measurable_pi_apply 0) measurableSet_Ioi]
    _ = (expMeasure α) (Set.Ioi r) := by
          simpa using
            congrArg (fun ν : Measure ℝ ↦ ν (Set.Ioi r))
              ((measurePreserving_eval
                (fun _ : Fin (l + 1) ↦ expMeasure α)
                (0 : Fin (l + 1))).map_eq)

/-- Helper for Theorem 5.36: fixing the prefix coordinate turns the split head-gap event into the
corresponding one-dimensional head event in the tail block. -/
private theorem prodMk_preimage_prefixHeadEvent
    {K l : ℕ} (prefixBase : Set (Fin K → ℝ)) (r : (Fin K → ℝ) → ℝ) (x : Fin K → ℝ) :
    Prod.mk x ⁻¹'
        {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) | p.1 ∈ prefixBase ∧ r p.1 < p.2 0} =
      {y : Fin (l + 1) → ℝ | x ∈ prefixBase ∧ r x < y 0} := by
  ext y
  -- Proof comment: fixing the prefix coordinate turns membership in the product head event into
  -- the same head-gap inequality with the fixed prefix datum `x`.
  simp

/-- Helper for Theorem 5.36: fixing the prefix coordinate turns the split strip event into the
corresponding residual relative strip in the tail block. -/
private theorem prodMk_preimage_prefixRelativeStrip
    {K l : ℕ} (d : NNReal) (prefixBase : Set (Fin K → ℝ))
    (r : (Fin K → ℝ) → ℝ) (x : Fin K → ℝ) :
    Prod.mk x ⁻¹'
        {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
          p.1 ∈ prefixBase ∧
            r p.1 < p.2 0 ∧
            (∑ i : Fin l, p.2 i.castSucc) ≤ r p.1 + d ∧
            r p.1 + d < ∑ i : Fin (l + 1), p.2 i} =
      {y : Fin (l + 1) → ℝ |
        x ∈ prefixBase ∧
          r x < y 0 ∧
          (∑ i : Fin l, y i.castSucc) ≤ r x + d ∧
          r x + d < ∑ i : Fin (l + 1), y i} := by
  ext y
  -- Proof comment: after fixing the prefix coordinate, the remaining fiber conditions are exactly
  -- the residual strip inequalities with the same prefix datum `x`.
  simp

/-- Helper for Theorem 5.36: pulling the split head-gap event back along a theorem-local
split-block map rewrites it to the corresponding prefix/head predicate on `Ω`. -/
private theorem splitBlock_preimage_prefixHeadEvent
    {Ω : Type*} {K l : ℕ}
    (splitBlock : Ω → (Fin K → ℝ) × (Fin (l + 1) → ℝ))
    (prefixBase : Set (Fin K → ℝ)) (r : (Fin K → ℝ) → ℝ) :
    splitBlock ⁻¹'
        {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) | p.1 ∈ prefixBase ∧ r p.1 < p.2 0} =
      {ω | (splitBlock ω).1 ∈ prefixBase ∧ r (splitBlock ω).1 < (splitBlock ω).2 0} := by
  ext ω
  -- Proof comment: the pulled-back head event is just the same conjunction evaluated on the two
  -- components of the split block at `ω`.
  simp

/-- Helper for Theorem 5.36: pulling the split relative-strip event back along a theorem-local
split-block map rewrites it to the corresponding prefix/strip predicate on `Ω`. -/
private theorem splitBlock_preimage_prefixRelativeStrip
    {Ω : Type*} {K l : ℕ} (d : NNReal)
    (splitBlock : Ω → (Fin K → ℝ) × (Fin (l + 1) → ℝ))
    (prefixBase : Set (Fin K → ℝ)) (r : (Fin K → ℝ) → ℝ) :
    splitBlock ⁻¹'
        {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
          p.1 ∈ prefixBase ∧
            r p.1 < p.2 0 ∧
            (∑ i : Fin l, p.2 i.castSucc) ≤ r p.1 + d ∧
            r p.1 + d < ∑ i : Fin (l + 1), p.2 i} =
      {ω |
        (splitBlock ω).1 ∈ prefixBase ∧
          r (splitBlock ω).1 < (splitBlock ω).2 0 ∧
          (∑ i : Fin l, (splitBlock ω).2 i.castSucc) ≤ r (splitBlock ω).1 + d ∧
          r (splitBlock ω).1 + d < ∑ i : Fin (l + 1), (splitBlock ω).2 i} := by
  ext ω
  -- Proof comment: the pulled-back strip event is the same relative-strip conjunction written in
  -- terms of the split prefix block and tail block at `ω`.
  simp

/-- Helper for Theorem 5.36: after fixing a measurable prefix base, the product exponential mass
of the residual relative-strip fibers factors through the matching head-gap event and the Poisson
singleton weight. -/
private theorem prefixBase_relativeStrip_prodMass_eq_mul_headGap
    {α : NNReal} (hα : 0 < α) {K l : ℕ} (d : NNReal)
    (prefixBase : Set (Fin K → ℝ)) (hprefixBase : MeasurableSet prefixBase)
    (r : (Fin K → ℝ) → ℝ) (hr_meas : Measurable r)
    (hr_nonneg : ∀ x ∈ prefixBase, 0 ≤ r x) :
    ((Measure.pi (fun _ : Fin K ↦ expMeasure α)).prod
      (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)))
      {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
        p.1 ∈ prefixBase ∧
          r p.1 < p.2 0 ∧
          (∑ i : Fin l, p.2 i.castSucc) ≤ r p.1 + d ∧
          r p.1 + d < ∑ i : Fin (l + 1), p.2 i} =
      (((Measure.pi (fun _ : Fin K ↦ expMeasure α)).prod
        (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)))
        {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
          p.1 ∈ prefixBase ∧ r p.1 < p.2 0}) *
        poissonMeasure (α * d) ({l} : Set ℕ) := by
  letI : IsProbabilityMeasure (expMeasure α) := isProbabilityMeasure_expMeasure hα
  let νPrefix : Measure (Fin K → ℝ) := Measure.pi (fun _ : Fin K ↦ expMeasure α)
  let νTail : Measure (Fin (l + 1) → ℝ) := Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)
  have hνPrefixFinite : IsFiniteMeasure νPrefix := by
    dsimp [νPrefix]
    infer_instance
  have hνTailFinite : IsFiniteMeasure νTail := by
    dsimp [νTail]
    infer_instance
  letI : IsFiniteMeasure νPrefix := hνPrefixFinite
  letI : IsFiniteMeasure νTail := hνTailFinite
  let stripEvent : Set ((Fin K → ℝ) × (Fin (l + 1) → ℝ)) :=
    {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
      p.1 ∈ prefixBase ∧
        r p.1 < p.2 0 ∧
        (∑ i : Fin l, p.2 i.castSucc) ≤ r p.1 + d ∧
        r p.1 + d < ∑ i : Fin (l + 1), p.2 i}
  let headEvent : Set ((Fin K → ℝ) × (Fin (l + 1) → ℝ)) :=
    {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) | p.1 ∈ prefixBase ∧ r p.1 < p.2 0}
  let headMass : (Fin K → ℝ) → ENNReal := fun x ↦ νTail {y : Fin (l + 1) → ℝ | r x < y 0}
  let poissonMass : ENNReal := poissonMeasure (α * d) ({l} : Set ℕ)
  have hprefixMeas : MeasurableSet {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) | p.1 ∈ prefixBase} := by
    simpa [Set.preimage] using hprefixBase.preimage measurable_fst
  have hheadCoord :
      Measurable (fun p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) ↦ p.2 0) :=
    (measurable_pi_apply 0).comp measurable_snd
  have htailSum :
      Measurable
        (fun p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) ↦ ∑ i : Fin l, p.2 i.castSucc) := by
    exact (Finset.measurable_sum Finset.univ fun i _ ↦
      (measurable_pi_apply i.castSucc).comp measurable_snd)
  have htotalSum :
      Measurable
        (fun p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) ↦ ∑ i : Fin (l + 1), p.2 i) :=
    (prefixSum_measurable (l + 1)).comp measurable_snd
  have hresidual : Measurable (fun p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) ↦ r p.1 + d) :=
    (hr_meas.comp measurable_fst).add measurable_const
  have hheadMeas : MeasurableSet headEvent := by
    have hgap :
        MeasurableSet {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) | r p.1 < p.2 0} := by
      have hdiff :
          Measurable (fun p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) ↦ p.2 0 - r p.1) :=
        hheadCoord.sub (hr_meas.comp measurable_fst)
      have hpre :
          {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) | r p.1 < p.2 0} =
            (fun p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) ↦ p.2 0 - r p.1) ⁻¹' Set.Ioi 0 := by
        ext p
        simp [sub_pos]
      rw [hpre]
      exact hdiff measurableSet_Ioi
    -- Proof comment: the split head event is the intersection of the measurable prefix base and
    -- the measurable head-gap inequality.
    have hheadEq :
        headEvent =
          {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) | p.1 ∈ prefixBase} ∩
            {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) | r p.1 < p.2 0} := by
      ext p
      simp [headEvent, and_assoc]
    rw [hheadEq]
    exact hprefixMeas.inter hgap
  have hstripMeas : MeasurableSet stripEvent := by
    have hlower :
        MeasurableSet
          {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
            (∑ i : Fin l, p.2 i.castSucc) ≤ r p.1 + d} := by
      have hpre :
          {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
            (∑ i : Fin l, p.2 i.castSucc) ≤ r p.1 + d} =
            (fun p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) ↦
              (∑ i : Fin l, p.2 i.castSucc) - (r p.1 + d)) ⁻¹' Set.Iic 0 := by
        ext p
        simp
      rw [hpre]
      exact (htailSum.sub hresidual) measurableSet_Iic
    have hupper :
        MeasurableSet
          {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
            r p.1 + d < ∑ i : Fin (l + 1), p.2 i} := by
      have hpre :
          {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
            r p.1 + d < ∑ i : Fin (l + 1), p.2 i} =
            (fun p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) ↦
              (∑ i : Fin (l + 1), p.2 i) - (r p.1 + d)) ⁻¹' Set.Ioi 0 := by
        ext p
        simp [sub_pos]
      rw [hpre]
      exact (htotalSum.sub hresidual) measurableSet_Ioi
    -- Proof comment: the full strip event adds two measurable tail-sum inequalities to the head
    -- event.
    have hstripEq :
        stripEvent =
          (headEvent ∩
            {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
              (∑ i : Fin l, p.2 i.castSucc) ≤ r p.1 + d}) ∩
            {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
              r p.1 + d < ∑ i : Fin (l + 1), p.2 i} := by
      ext p
      simp [stripEvent, headEvent, and_assoc]
    rw [hstripEq]
    exact (hheadMeas.inter hlower).inter hupper
  have hheadSection :
      ∀ x : Fin K → ℝ, νTail (Prod.mk x ⁻¹' headEvent) = Set.indicator prefixBase headMass x := by
    intro x
    classical
    by_cases hx : x ∈ prefixBase
    · -- Proof comment: once the prefix coordinate lies in the base, the section is exactly the
      -- one-dimensional head-gap event in the tail block.
      rw [prodMk_preimage_prefixHeadEvent prefixBase r x]
      simp [headMass, Set.indicator_of_mem, hx]
    · -- Proof comment: outside the prefix base, the section is empty and the indicator vanishes.
      rw [prodMk_preimage_prefixHeadEvent prefixBase r x]
      simp [headMass, Set.indicator_of_notMem, hx]
  have hstripSection :
      ∀ x : Fin K → ℝ,
        νTail (Prod.mk x ⁻¹' stripEvent) = poissonMass * Set.indicator prefixBase headMass x := by
    intro x
    classical
    by_cases hx : x ∈ prefixBase
    · -- Proof comment: on the active prefix base, the closed relative-strip mass formula turns
      -- the whole tail section into the head-gap mass times the constant Poisson singleton.
      rw [prodMk_preimage_prefixRelativeStrip d prefixBase r x]
      simp [hx]
      rw [relativeBlockStrip_measure_eq_headGap_measure_mul_poissonSingleton
        hα l (r x) (hr_nonneg x hx) d]
      rw [← piExpMeasure_headGap_measure hα l (r x)]
      simpa [poissonMass, headMass, νTail, mul_comm]
    · -- Proof comment: outside the prefix base, the strip section is empty and therefore zero.
      rw [prodMk_preimage_prefixRelativeStrip d prefixBase r x]
      simp [poissonMass, headMass, Set.indicator_of_notMem, hx]
  have hpoisson_ne_top : poissonMass ≠ ⊤ := measure_ne_top _ _
  -- Proof comment: apply `Measure.prod_apply` once on each product event, rewrite both section
  -- masses pointwise, and pull the constant Poisson factor outside the outer integral.
  change (νPrefix.prod νTail) stripEvent = ((νPrefix.prod νTail) headEvent) * poissonMass
  rw [Measure.prod_apply hstripMeas, Measure.prod_apply hheadMeas]
  calc
    ∫⁻ x, νTail (Prod.mk x ⁻¹' stripEvent) ∂νPrefix
      = ∫⁻ x, poissonMass * Set.indicator prefixBase headMass x ∂νPrefix := by
          refine lintegral_congr_ae <| Filter.Eventually.of_forall hstripSection
    _ = poissonMass * ∫⁻ x, Set.indicator prefixBase headMass x ∂νPrefix := by
          simpa using
            (lintegral_const_mul'
              (μ := νPrefix) poissonMass (Set.indicator prefixBase headMass) hpoisson_ne_top)
    _ = (∫⁻ x, νTail (Prod.mk x ⁻¹' headEvent) ∂νPrefix) * poissonMass := by
          rw [mul_comm]
          congr 1
          refine lintegral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
          symm
          exact hheadSection x

/-- Helper for Theorem 5.36: on a genuine renewal path, fixing `N_s = K` and the increment over
`[s,t]` rewrites directly to the relative tail strip for the split block
`W K, ..., W (K + l)`. -/
private theorem renewal_increment_two_time_iff_splitRelativeBlockStrip
    (W : ℕ → Ω → ℝ) {ω : Ω}
    (h_arrival_strict : StrictMono (fun n ↦ arrivalTime W n ω))
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop)
    {s t : NNReal} (hst : s ≤ t) {K l : ℕ} :
    let r : ℝ := (s : ℝ) - arrivalTime W K ω
    arrivalTime W K ω ≤ s ∧
      (fun i : Fin (l + 1) ↦ W (K + i) ω) ∈
        {y : Fin (l + 1) → ℝ |
          r < y 0 ∧ (∑ i : Fin l, y i.castSucc) ≤ r + (t - s : NNReal) ∧
            r + (t - s : NNReal) < ∑ i : Fin (l + 1), y i} ↔
      (renewalCountingProcess W s ω = K ∧
        renewalCountingProcess W t ω - renewalCountingProcess W s ω = l) := by
  dsimp
  have hthreshold :
      (s : ℝ) - arrivalTime W K ω + (t - s : NNReal) = (t : ℝ) - arrivalTime W K ω := by
    rw [NNReal.coe_sub hst]
    ring
  have hhead :
      (s : ℝ) - arrivalTime W K ω < W K ω ↔ s < arrivalTime W (K + 1) ω := by
    -- Proof comment: the residual-gap inequality is exactly the upper strip inequality at time
    -- `s` after rewriting `T_(K+1)` as `T_K + W_K`.
    constructor
    · intro h
      have hs : (s : ℝ) < arrivalTime W K ω + W K ω := by
        linarith
      simpa [arrivalTime_succ] using hs
    · intro h
      have hs : (s : ℝ) < arrivalTime W K ω + W K ω := by
        simpa [arrivalTime_succ] using h
      linarith
  have hprefixSum :
      (∑ i : Fin l, W (K + i) ω) =
        ∑ i ∈ Finset.range l, W (K + i) ω := by
    -- Proof comment: the `castSucc` block is the usual contiguous length-`l` tail block.
    simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ W (K + i) ω) l)
  have htotalSum :
      (∑ i : Fin (l + 1), W (K + i) ω) =
        ∑ i ∈ Finset.range (l + 1), W (K + i) ω := by
    -- Proof comment: the full `Fin (l + 1)` block sum is the standard `range (l + 1)` sum.
    simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ W (K + i) ω) (l + 1))
  constructor
  · rintro ⟨hKle, hmem⟩
    have hsplit :
        renewalCountingProcess W s ω = K ∧
          renewalCountingProcess W t ω - renewalCountingProcess W s ω = l := by
      have hrel :
          arrivalTime W K ω ≤ s ∧
            s < arrivalTime W (K + 1) ω ∧
            (∑ i ∈ Finset.range l, W (K + i) ω) ≤ (t : ℝ) - arrivalTime W K ω ∧
            (t : ℝ) - arrivalTime W K ω < ∑ i ∈ Finset.range (l + 1), W (K + i) ω := by
        rcases hmem with ⟨hgap, hlower, hupper⟩
        refine ⟨hKle, hhead.mp ?_, ?_, ?_⟩
        · simpa using hgap
        · rw [hprefixSum] at hlower
          linarith [hlower, hthreshold]
        · rw [htotalSum] at hupper
          linarith [hupper, hthreshold]
      exact
        (renewal_increment_two_time_iff_relative_block_strip
          W h_arrival_strict h_arrival_tendsto hst).2 hrel
    exact hsplit
  · intro hcount
    have hrel :
        arrivalTime W K ω ≤ s ∧
          s < arrivalTime W (K + 1) ω ∧
          (∑ i ∈ Finset.range l, W (K + i) ω) ≤ (t : ℝ) - arrivalTime W K ω ∧
          (t : ℝ) - arrivalTime W K ω < ∑ i ∈ Finset.range (l + 1), W (K + i) ω :=
      (renewal_increment_two_time_iff_relative_block_strip
        W h_arrival_strict h_arrival_tendsto hst).1 hcount
    refine ⟨hrel.1, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · exact hhead.mpr hrel.2.1
    · rw [hprefixSum]
      linarith [hrel.2.2.1, hthreshold]
    · rw [htotalSum]
      linarith [hrel.2.2.2, hthreshold]

/-- Helper for Theorem 5.36: the theorem-local prefix-arrival map on `Fin K → ℝ` is measurable. -/
private theorem splitPrefixArrival_measurable
    {K : ℕ} (n : ℕ) :
    Measurable
      (fun x : Fin K → ℝ ↦
        Finset.sum (Finset.range n) fun i ↦ if hi : i < K then x ⟨i, hi⟩ else 0) := by
  -- Proof comment: each term is either the corresponding coordinate projection or the zero
  -- function, so the finite prefix sum is measurable.
  refine Finset.measurable_sum (Finset.range n) fun i _ ↦ ?_
  by_cases hi : i < K
  · let j : Fin K := ⟨i, hi⟩
    have hterm :
        (fun x : Fin K → ℝ ↦ if hi' : i < K then x ⟨i, hi'⟩ else 0) =
          fun x : Fin K → ℝ ↦ x j := by
      funext x
      simp [j, hi]
    rw [hterm]
    exact measurable_pi_apply j
  · simp [hi]

/-- Helper for Theorem 5.36: every truncated cumulative count of a finite increment label vector is
bounded by the total count of that vector. This is the arithmetic bridge needed to represent the
relevant arrival times using only the first `K` interarrivals in the split-block proof. -/
private theorem prefixRangeSum_le_total
    {m : ℕ} (k : Fin m → ℕ) (j : Fin m) :
    (∑ i ∈ Finset.range j.1, if hi : i < m then k ⟨i, hi⟩ else 0) ≤ ∑ i : Fin m, k i := by
  have hsum :
      (∑ i ∈ Finset.range j.1, if hi : i < m then k ⟨i, hi⟩ else 0) ≤
        ∑ i ∈ Finset.range m, if hi : i < m then k ⟨i, hi⟩ else 0 := by
    -- Proof comment: the prefix range is a subset of the full range, and every summand is a
    -- nonnegative natural number.
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_of_lt j.2))
      fun i _ _ ↦ Nat.zero_le _
  have htotal :
      (∑ i ∈ Finset.range m, if hi : i < m then k ⟨i, hi⟩ else 0) = ∑ i : Fin m, k i := by
    simpa using
      (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ if hi : i < m then k ⟨i, hi⟩ else 0) m).symm
  rw [htotal] at hsum
  exact hsum

/-- Helper for Theorem 5.36: evaluating the theorem-local split-prefix sum on the concrete prefix
block `(W 0, ..., W (K - 1))` recovers the arrival time `T_n` whenever `n ≤ K`. -/
private theorem splitPrefixArrival_eval_eq_arrivalTime
    (W : ℕ → Ω → ℝ) {K n : ℕ} (ω : Ω) (hn : n ≤ K) :
    (∑ i ∈ Finset.range n, if hi : i < K then (fun j : Fin K ↦ W j ω) ⟨i, hi⟩ else 0) =
      arrivalTime W n ω := by
  -- Proof comment: under the bound `n ≤ K`, every index in `range n` lands in the stored prefix
  -- block, so the truncated prefix sum is exactly the usual arrival-time sum.
  have hEq :
      (∑ i ∈ Finset.range n, if hi : i < K then W i ω else 0) =
        ∑ i ∈ Finset.range n, W i ω := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hiK : i < K := lt_of_lt_of_le (Finset.mem_range.mp hi) hn
    simp [hiK]
  simpa [arrivalTime] using hEq

/-- Helper for Theorem 5.36: the zero-anchored increment-vector singleton masses are exactly the
singleton masses of the corresponding product Poisson law. -/
private theorem zeroAnchoredRenewalIncrementFinGrid_singletonMassOfIidExponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α)
    {m : ℕ} (u : Fin (m + 1) → NNReal) (hu0 : u 0 = 0) (hu : Monotone u)
    (k : Fin m → ℕ) :
    μ
      ({ω |
          (fun i : Fin m ↦
            renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω) = k})
      =
        (Measure.pi (fun i : Fin m ↦ poissonMeasure (α * (u i.succ - u i.castSucc))))
          ({k} : Set (Fin m → ℕ)) := by
  classical
  induction m with
  | zero =>
      letI : IsProbabilityMeasure (expMeasure α) := isProbabilityMeasure_expMeasure hα
      letI : IsProbabilityMeasure μ := hW0_law.isProbabilityMeasure
      -- Proof comment: for the empty grid there is only one increment vector, so both singleton
      -- events are the whole space.
      have hleft :
          ({ω |
              (fun i : Fin 0 ↦
                renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω) =
                  k} : Set Ω) = Set.univ := by
        ext ω
        constructor
        · intro _
          simp
        · intro _
          funext i
          exact Fin.elim0 i
      have hright : ({k} : Set (Fin 0 → ℕ)) = Set.univ := by
        ext x
        constructor
        · intro _
          simp
        · intro _
          funext i
          exact Fin.elim0 i
      calc
        μ
            ({ω |
                (fun i : Fin 0 ↦
                  renewalCountingProcess W (u i.succ) ω -
                    renewalCountingProcess W (u i.castSucc) ω) = k})
            = μ Set.univ := by rw [hleft]
        _ = 1 := measure_univ
        _ = (Measure.pi (fun i : Fin 0 ↦ poissonMeasure (α * (u i.succ - u i.castSucc))))
              ({k} : Set (Fin 0 → ℕ)) := by
              rw [hright]
              simp
  | succ m ih =>
      let uPrefix : Fin (m + 1) → NNReal := fun j ↦ u j.castSucc
      let kPrefix : Fin m → ℕ := fun i ↦ k i.castSucc
      let s : NNReal := u (Fin.castSucc (Fin.last m))
      let t : NNReal := u (Fin.last (m + 1))
      let K : ℕ := ∑ i : Fin m, k i.castSucc
      have huPrefix0 : uPrefix 0 = 0 := by
        -- Proof comment: removing the terminal grid point preserves the zero anchor.
        simpa [uPrefix] using hu0
      have huPrefix : Monotone uPrefix := by
        -- Proof comment: the prefix grid is the original grid precomposed with `Fin.castSucc`.
        intro a b hab
        exact hu (show a.castSucc ≤ b.castSucc by simpa using hab)
      have hPrefixMass :
          μ
            ({ω |
                (fun i : Fin m ↦
                  renewalCountingProcess W (uPrefix i.succ) ω -
                    renewalCountingProcess W (uPrefix i.castSucc) ω) = kPrefix})
            =
              (Measure.pi
                (fun i : Fin m ↦
                  poissonMeasure (α * (uPrefix i.succ - uPrefix i.castSucc))))
                ({kPrefix} : Set (Fin m → ℕ)) :=
        ih uPrefix huPrefix0 huPrefix kPrefix
      have hEventSplit :
          ({ω |
              (fun i : Fin (m + 1) ↦
                renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω) =
                  k} : Set Ω)
            =
              {ω |
                (fun i : Fin m ↦
                  renewalCountingProcess W (uPrefix i.succ) ω -
                    renewalCountingProcess W (uPrefix i.castSucc) ω) = kPrefix ∧
                  renewalCountingProcess W t ω - renewalCountingProcess W s ω =
                    k (Fin.last m)} := by
        ext ω
        constructor
        · intro hω
          refine ⟨?_, ?_⟩
          · funext i
            simpa [uPrefix, kPrefix] using congrFun hω i.castSucc
          · simpa [s, t] using congrFun hω (Fin.last m)
        · rintro ⟨hprefix, hlast⟩
          funext i
          refine Fin.lastCases ?_ ?_ i
          · simpa [s, t] using hlast
          · intro j
            simpa [uPrefix, kPrefix] using congrFun hprefix j
      have hEventWithCount :
          ({ω |
              (fun i : Fin m ↦
                renewalCountingProcess W (uPrefix i.succ) ω -
                  renewalCountingProcess W (uPrefix i.castSucc) ω) = kPrefix ∧
                renewalCountingProcess W t ω - renewalCountingProcess W s ω =
                  k (Fin.last m)} : Set Ω)
            =
              {ω |
                (fun i : Fin m ↦
                  renewalCountingProcess W (uPrefix i.succ) ω -
                    renewalCountingProcess W (uPrefix i.castSucc) ω) = kPrefix ∧
                renewalCountingProcess W s ω = K ∧
                  renewalCountingProcess W t ω - renewalCountingProcess W s ω =
                    k (Fin.last m)} := by
        ext ω
        constructor
        · rintro ⟨hprefix, hlast⟩
          have hinc :
              ∀ i : Fin (m + 1),
                renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω =
                  k i := by
            intro i
            refine Fin.lastCases ?_ ?_ i
            · simpa [s, t] using hlast
            · intro j
              simpa [uPrefix, kPrefix] using congrFun hprefix j
          refine ⟨hprefix, ?_, hlast⟩
          -- Proof comment: the prefix increment event fixes the penultimate count to the
          -- cumulative prefix sum `K`.
          simpa [K] using
            zeroAnchoredRenewalIncrementPenultimateCount_public
              W (ω := ω) (u := u) hu0 hu k hinc
        · rintro ⟨hprefix, _, hlast⟩
          exact ⟨hprefix, hlast⟩
      have hPoissonSplit :
          (Measure.pi (fun i : Fin (m + 1) ↦ poissonMeasure (α * (u i.succ - u i.castSucc))))
            ({k} : Set (Fin (m + 1) → ℕ))
            =
              (Measure.pi
                (fun i : Fin m ↦
                  poissonMeasure (α * (uPrefix i.succ - uPrefix i.castSucc))))
                ({kPrefix} : Set (Fin m → ℕ)) *
                poissonMeasure (α * (t - s)) ({k (Fin.last m)} : Set ℕ) := by
        -- Proof comment: split the product singleton mass into the prefix coordinates and the last
        -- coordinate once, using the canonical `Fin` product decomposition.
        rw [Measure.pi_singleton, Measure.pi_singleton, Fin.prod_univ_castSucc]
        simp [uPrefix, kPrefix, s, t]
      have hMassFactor :
          μ
            ({ω |
                (fun i : Fin m ↦
                  renewalCountingProcess W (uPrefix i.succ) ω -
                    renewalCountingProcess W (uPrefix i.castSucc) ω) = kPrefix ∧
                renewalCountingProcess W s ω = K ∧
                  renewalCountingProcess W t ω - renewalCountingProcess W s ω =
                    k (Fin.last m)})
            =
              μ
                ({ω |
                    (fun i : Fin m ↦
                      renewalCountingProcess W (uPrefix i.succ) ω -
                        renewalCountingProcess W (uPrefix i.castSucc) ω) = kPrefix}) *
                poissonMeasure (α * (t - s)) ({k (Fin.last m)} : Set ℕ) := by
        let l : ℕ := k (Fin.last m)
        let prefixEvent : Set Ω :=
          {ω |
            (fun i : Fin m ↦
              renewalCountingProcess W (uPrefix i.succ) ω -
                renewalCountingProcess W (uPrefix i.castSucc) ω) = kPrefix}
        let fullEvent : Set Ω :=
          {ω |
            (fun i : Fin m ↦
              renewalCountingProcess W (uPrefix i.succ) ω -
                renewalCountingProcess W (uPrefix i.castSucc) ω) = kPrefix ∧
            renewalCountingProcess W s ω = K ∧
              renewalCountingProcess W t ω - renewalCountingProcess W s ω = l}
        let splitBlock : Ω → (Fin K → ℝ) × (Fin (l + 1) → ℝ) :=
          fun ω ↦ ((fun i : Fin K ↦ W i ω), fun i : Fin (l + 1) ↦ W (K + i) ω)
        let prefixCount : Fin (m + 1) → ℕ :=
          fun j ↦ ∑ i ∈ Finset.range j.1, if hi : i < m then kPrefix ⟨i, hi⟩ else 0
        let prefixArrival : ℕ → (Fin K → ℝ) → ℝ :=
          fun n x ↦ ∑ i ∈ Finset.range n, if hi : i < K then x ⟨i, hi⟩ else 0
        let residualGap : (Fin K → ℝ) → ℝ :=
          fun x ↦ (s : ℝ) - prefixArrival K x
        let prefixBase : Set (Fin K → ℝ) :=
          {x |
            ∀ j : Fin (m + 1),
              prefixArrival (prefixCount j) x ≤ uPrefix j ∧
                if hlt : prefixCount j < K then
                  uPrefix j < prefixArrival (prefixCount j + 1) x
                else
                  True}
        let headEvent : Set ((Fin K → ℝ) × (Fin (l + 1) → ℝ)) :=
          {p | p.1 ∈ prefixBase ∧ residualGap p.1 < p.2 0}
        let stripEvent : Set ((Fin K → ℝ) × (Fin (l + 1) → ℝ)) :=
          {p |
            p.1 ∈ prefixBase ∧
              residualGap p.1 < p.2 0 ∧
              (∑ i : Fin l, p.2 i.castSucc) ≤ residualGap p.1 + ((t - s : NNReal) : ℝ) ∧
              residualGap p.1 + ((t - s : NNReal) : ℝ) < ∑ i : Fin (l + 1), p.2 i}
        let ν : Measure ((Fin K → ℝ) × (Fin (l + 1) → ℝ)) :=
          ((Measure.pi (fun _ : Fin K ↦ expMeasure α)).prod
            (Measure.pi (fun _ : Fin (l + 1) ↦ expMeasure α)))
        letI : IsProbabilityMeasure (expMeasure α) := isProbabilityMeasure_expMeasure hα
        letI : IsProbabilityMeasure μ := hW0_law.isProbabilityMeasure
        have hst : s ≤ t := by
          change u (Fin.castSucc (Fin.last m)) ≤ u (Fin.last (m + 1))
          exact hu (by simp [Fin.le_iff_val_le_val])
        have hprefixCount_last : prefixCount (Fin.last m) = K := by
          simpa [prefixCount, K, kPrefix] using
            (Fin.sum_univ_eq_sum_range
              (fun i : ℕ ↦ if hi : i < m then kPrefix ⟨i, hi⟩ else 0) m).symm
        have hprefixCount_le : ∀ j : Fin (m + 1), prefixCount j ≤ K := by
          intro j
          refine Fin.lastCases ?_ ?_ j
          · simpa [hprefixCount_last]
          · intro i
            simpa [prefixCount, K, kPrefix] using prefixRangeSum_le_total kPrefix i
        have huPrefix_le_s : ∀ j : Fin (m + 1), uPrefix j ≤ s := by
          intro j
          change u j.castSucc ≤ u (Fin.castSucc (Fin.last m))
          exact hu <| Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ j.2)
        have hprefixArrival_meas : ∀ n : ℕ, Measurable (prefixArrival n) := by
          intro n
          simpa [prefixArrival] using splitPrefixArrival_measurable (K := K) n
        have hprefixArrival_eval :
            ∀ {ω : Ω} {n : ℕ}, n ≤ K →
              prefixArrival n ((splitBlock ω).1) = arrivalTime W n ω := by
          intro ω n hn
          simpa [splitBlock, prefixArrival] using
            splitPrefixArrival_eval_eq_arrivalTime W (K := K) (n := n) ω hn
        have hheadGap_iff :
            ∀ {ω : Ω},
              residualGap ((splitBlock ω).1) < (splitBlock ω).2 0 ↔
                s < arrivalTime W (K + 1) ω := by
          intro ω
          have hprefixK : prefixArrival K ((splitBlock ω).1) = arrivalTime W K ω :=
            hprefixArrival_eval (ω := ω) (n := K) le_rfl
          have hresidual :
              residualGap ((splitBlock ω).1) = (s : ℝ) - arrivalTime W K ω := by
            simpa [residualGap] using congrArg (fun z ↦ (s : ℝ) - z) hprefixK
          have htail0 : (splitBlock ω).2 0 = W K ω := by
            simp [splitBlock]
          constructor
          · intro hgap
            rw [hresidual, htail0] at hgap
            have hs' : (s : ℝ) < arrivalTime W K ω + W K ω := by
              linarith
            simpa [arrivalTime_succ] using hs'
          · intro hsUpper
            have hs' : (s : ℝ) < arrivalTime W K ω + W K ω := by
              simpa [arrivalTime_succ] using hsUpper
            rw [hresidual, htail0]
            linarith
        -- Route correction: the abstract transport loop is replaced by one concrete theorem-local
        -- `prefixBase` whose missing upper strips are recovered from the common head-gap.
        have hprefixPathwise :
            ∀ {ω : Ω},
              StrictMono (fun n ↦ arrivalTime W n ω) →
              Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop →
              (ω ∈ prefixEvent ↔ splitBlock ω ∈ headEvent) := by
          intro ω hstrict htend
          have hstrips :
              (∀ i : Fin m,
                  renewalCountingProcess W (uPrefix i.succ) ω -
                    renewalCountingProcess W (uPrefix i.castSucc) ω = kPrefix i) ↔
                ∀ j : Fin (m + 1),
                  arrivalTime W (prefixCount j) ω ≤ uPrefix j ∧
                    uPrefix j < arrivalTime W (prefixCount j + 1) ω := by
            simpa [prefixCount] using
              (renewalIncrementFinGrid_iff_arrivalStrips
                W hstrict htend huPrefix0 huPrefix kPrefix)
          constructor
          · intro hω
            have hinc :
                ∀ i : Fin m,
                  renewalCountingProcess W (uPrefix i.succ) ω -
                    renewalCountingProcess W (uPrefix i.castSucc) ω = kPrefix i := by
              intro i
              simpa using congrFun hω i
            have hstrip := hstrips.1 hinc
            refine ⟨?_, ?_⟩
            · change
                ∀ j : Fin (m + 1),
                  prefixArrival (prefixCount j) ((splitBlock ω).1) ≤ uPrefix j ∧
                    if hlt : prefixCount j < K then
                      uPrefix j < prefixArrival (prefixCount j + 1) ((splitBlock ω).1)
                    else
                      True
              intro j
              refine ⟨?_, ?_⟩
              · rw [hprefixArrival_eval (ω := ω) (n := prefixCount j) (hprefixCount_le j)]
                exact (hstrip j).1
              · by_cases hlt : prefixCount j < K
                · have hupper :
                      uPrefix j < prefixArrival (prefixCount j + 1) ((splitBlock ω).1) := by
                    rw [hprefixArrival_eval (ω := ω) (n := prefixCount j + 1)
                      (Nat.succ_le_of_lt hlt)]
                    exact (hstrip j).2
                  simpa [hlt] using hupper
                · simp [hlt]
            · have hsUpper : s < arrivalTime W (K + 1) ω := by
                simpa [uPrefix, s, hprefixCount_last] using (hstrip (Fin.last m)).2
              exact (hheadGap_iff (ω := ω)).2 hsUpper
          · intro hω
            have hω' :
                (splitBlock ω).1 ∈ prefixBase ∧
                  residualGap ((splitBlock ω).1) < (splitBlock ω).2 0 := by
              simpa [headEvent] using hω
            rcases hω' with ⟨hbase, hgap⟩
            have hbase' :
                ∀ j : Fin (m + 1),
                  prefixArrival (prefixCount j) ((splitBlock ω).1) ≤ uPrefix j ∧
                    if hlt : prefixCount j < K then
                      uPrefix j < prefixArrival (prefixCount j + 1) ((splitBlock ω).1)
                    else
                      True := by
              simpa [prefixBase] using hbase
            have hsUpper : s < arrivalTime W (K + 1) ω := (hheadGap_iff (ω := ω)).1 hgap
            have hstrip :
                ∀ j : Fin (m + 1),
                  arrivalTime W (prefixCount j) ω ≤ uPrefix j ∧
                    uPrefix j < arrivalTime W (prefixCount j + 1) ω := by
              intro j
              have hj := hbase' j
              refine ⟨?_, ?_⟩
              · rw [← hprefixArrival_eval (ω := ω) (n := prefixCount j) (hprefixCount_le j)]
                exact hj.1
              · by_cases hlt : prefixCount j < K
                · have hupper :
                      uPrefix j < prefixArrival (prefixCount j + 1) ((splitBlock ω).1) := by
                    simpa [hlt] using hj.2
                  rw [hprefixArrival_eval (ω := ω) (n := prefixCount j + 1)
                    (Nat.succ_le_of_lt hlt)] at hupper
                  exact hupper
                · have hEqK : prefixCount j = K :=
                    (Nat.lt_or_eq_of_le (hprefixCount_le j)).resolve_left hlt
                  have huj : (uPrefix j : ℝ) ≤ s := huPrefix_le_s j
                  simpa [hEqK] using lt_of_le_of_lt huj hsUpper
            have hinc := hstrips.2 hstrip
            funext i
            exact hinc i
        have hfullPathwise :
            ∀ {ω : Ω},
              StrictMono (fun n ↦ arrivalTime W n ω) →
              Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop →
              (ω ∈ fullEvent ↔ splitBlock ω ∈ stripEvent) := by
          intro ω hstrict htend
          have hprefix := hprefixPathwise (ω := ω) hstrict htend
          constructor
          · intro hω
            rcases hω with ⟨hprefixEvent, hsCount, hlastCount⟩
            have hhead : splitBlock ω ∈ headEvent := hprefix.1 hprefixEvent
            have hhead' :
                (splitBlock ω).1 ∈ prefixBase ∧
                  residualGap ((splitBlock ω).1) < (splitBlock ω).2 0 := by
              simpa [headEvent] using hhead
            rcases hhead' with ⟨hbase, _⟩
            have hresidual :
                residualGap ((splitBlock ω).1) = (s : ℝ) - arrivalTime W K ω := by
              simpa [residualGap] using
                congrArg (fun z ↦ (s : ℝ) - z)
                  (hprefixArrival_eval (ω := ω) (n := K) le_rfl)
            have hrelRaw :=
              (renewal_increment_two_time_iff_splitRelativeBlockStrip
                W hstrict htend hst (K := K) (l := l)).2
                ⟨hsCount, by simpa [l] using hlastCount⟩
            rcases hrelRaw with ⟨_, htailRaw⟩
            rcases htailRaw with ⟨hgapRaw, hlowerRaw, hupperRaw⟩
            have hgap :
                residualGap ((splitBlock ω).1) < (splitBlock ω).2 0 := by
              simpa [splitBlock, hresidual] using hgapRaw
            have hlower :
                (∑ i : Fin l, (splitBlock ω).2 i.castSucc) ≤
                  residualGap ((splitBlock ω).1) + ((t - s : NNReal) : ℝ) := by
              simpa [splitBlock, hresidual] using hlowerRaw
            have hupper :
                residualGap ((splitBlock ω).1) + ((t - s : NNReal) : ℝ) <
                  ∑ i : Fin (l + 1), (splitBlock ω).2 i := by
              simpa [splitBlock, hresidual] using hupperRaw
            simpa [stripEvent] using ⟨hbase, hgap, hlower, hupper⟩
          · intro hω
            have hω' :
                (splitBlock ω).1 ∈ prefixBase ∧
                  residualGap ((splitBlock ω).1) < (splitBlock ω).2 0 ∧
                    (∑ i : Fin l, (splitBlock ω).2 i.castSucc) ≤
                      residualGap ((splitBlock ω).1) + ((t - s : NNReal) : ℝ) ∧
                    residualGap ((splitBlock ω).1) + ((t - s : NNReal) : ℝ) <
                      ∑ i : Fin (l + 1), (splitBlock ω).2 i := by
              simpa [stripEvent] using hω
            rcases hω' with ⟨hbase, hgap, hlower, hupper⟩
            have hprefixEvent : ω ∈ prefixEvent := by
              exact hprefix.2 (by simpa [headEvent] using ⟨hbase, hgap⟩)
            have hinc :
                ∀ i : Fin m,
                  renewalCountingProcess W (uPrefix i.succ) ω -
                    renewalCountingProcess W (uPrefix i.castSucc) ω = kPrefix i := by
              intro i
              simpa using congrFun hprefixEvent i
            have hprefixStrips :
                ∀ j : Fin (m + 1),
                  arrivalTime W (prefixCount j) ω ≤ uPrefix j ∧
                    uPrefix j < arrivalTime W (prefixCount j + 1) ω := by
              simpa [prefixCount] using
                (renewalIncrementFinGrid_iff_arrivalStrips
                  W hstrict htend huPrefix0 huPrefix kPrefix).1 hinc
            have hKle : arrivalTime W K ω ≤ s := by
              simpa [uPrefix, s, hprefixCount_last] using (hprefixStrips (Fin.last m)).1
            have hresidual :
                residualGap ((splitBlock ω).1) = (s : ℝ) - arrivalTime W K ω := by
              simpa [residualGap] using
                congrArg (fun z ↦ (s : ℝ) - z)
                  (hprefixArrival_eval (ω := ω) (n := K) le_rfl)
            have hgapRaw : (s : ℝ) - arrivalTime W K ω < W K ω := by
              simpa [splitBlock, hresidual] using hgap
            have hlowerRaw := by
              simpa [splitBlock, hresidual] using hlower
            have hupperRaw := by
              simpa [splitBlock, hresidual] using hupper
            have hcounts :
                renewalCountingProcess W s ω = K ∧
                  renewalCountingProcess W t ω - renewalCountingProcess W s ω = l := by
              simpa [l] using
                (renewal_increment_two_time_iff_splitRelativeBlockStrip
                  W hstrict htend hst (K := K) (l := l)).1
                  ⟨hKle, by simpa using ⟨hgapRaw, hlowerRaw, hupperRaw⟩⟩
            exact ⟨hprefixEvent, hcounts.1, hcounts.2⟩
        have hlowerSet :
            ∀ j : Fin (m + 1),
              MeasurableSet {x : Fin K → ℝ | prefixArrival (prefixCount j) x ≤ uPrefix j} := by
          intro j
          have hpre :
              {x : Fin K → ℝ | prefixArrival (prefixCount j) x ≤ uPrefix j} =
                (fun x : Fin K → ℝ ↦ prefixArrival (prefixCount j) x - uPrefix j) ⁻¹' Set.Iic 0 := by
            ext x
            simp
          rw [hpre]
          exact ((hprefixArrival_meas (prefixCount j)).sub measurable_const) measurableSet_Iic
        have hupperSet :
            ∀ j : Fin (m + 1),
              MeasurableSet
                {x : Fin K → ℝ | uPrefix j < prefixArrival (prefixCount j + 1) x} := by
          intro j
          have hpre :
              {x : Fin K → ℝ | uPrefix j < prefixArrival (prefixCount j + 1) x} =
                (fun x : Fin K → ℝ ↦ prefixArrival (prefixCount j + 1) x - uPrefix j) ⁻¹' Set.Ioi 0 := by
            ext x
            simp [sub_pos]
          rw [hpre]
          exact
            ((hprefixArrival_meas (prefixCount j + 1)).sub measurable_const) measurableSet_Ioi
        have hprefixBase_eq :
            prefixBase =
              ⋂ j : Fin (m + 1),
                ({x : Fin K → ℝ | prefixArrival (prefixCount j) x ≤ uPrefix j} ∩
                  if hlt : prefixCount j < K then
                    {x : Fin K → ℝ | uPrefix j < prefixArrival (prefixCount j + 1) x}
                  else
                    Set.univ) := by
          ext x
          simp [prefixBase]
        have hprefixBase : MeasurableSet prefixBase := by
          rw [hprefixBase_eq]
          refine MeasurableSet.iInter ?_
          intro j
          refine (hlowerSet j).inter ?_
          by_cases hlt : prefixCount j < K
          · simpa [hlt] using hupperSet j
          · simpa [hlt] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Fin K → ℝ)))
        have hresidual_meas : Measurable residualGap := by
          simpa [residualGap] using measurable_const.sub (hprefixArrival_meas K)
        have hresidual_nonneg : ∀ x ∈ prefixBase, 0 ≤ residualGap x := by
          intro x hx
          have hx' :
              ∀ j : Fin (m + 1),
                prefixArrival (prefixCount j) x ≤ uPrefix j ∧
                  if hlt : prefixCount j < K then
                    uPrefix j < prefixArrival (prefixCount j + 1) x
                  else
                    True := by
            simpa [prefixBase] using hx
          have hKle_x : prefixArrival K x ≤ s := by
            simpa [uPrefix, s, hprefixCount_last] using (hx' (Fin.last m)).1
          have hresid : residualGap x = (s : ℝ) - prefixArrival K x := by
            rfl
          rw [hresid]
          linarith
        have hheadEvent : MeasurableSet headEvent := by
          have hprefixMeas :
              MeasurableSet {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) | p.1 ∈ prefixBase} := by
            simpa [Set.preimage] using hprefixBase.preimage measurable_fst
          have hgapMeas :
              MeasurableSet
                {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) | residualGap p.1 < p.2 0} := by
            have hpre :
                {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) | residualGap p.1 < p.2 0} =
                  (fun p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) ↦ p.2 0 - residualGap p.1) ⁻¹' Set.Ioi 0 := by
              ext p
              simp [sub_pos]
            rw [hpre]
            exact
              (((measurable_pi_apply 0).comp measurable_snd).sub
                (hresidual_meas.comp measurable_fst)) measurableSet_Ioi
          have hEq :
              headEvent =
                {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) | p.1 ∈ prefixBase} ∩
                  {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) | residualGap p.1 < p.2 0} := by
            ext p
            simp [headEvent, and_assoc]
          rw [hEq]
          exact hprefixMeas.inter hgapMeas
        have hstripEvent : MeasurableSet stripEvent := by
          have hlower :
              MeasurableSet
                {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
                  (∑ i : Fin l, p.2 i.castSucc) ≤ residualGap p.1 + ((t - s : NNReal) : ℝ)} := by
            have hpre :
                {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
                  (∑ i : Fin l, p.2 i.castSucc) ≤ residualGap p.1 + ((t - s : NNReal) : ℝ)} =
                  (fun p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) ↦
                    (∑ i : Fin l, p.2 i.castSucc) -
                      (residualGap p.1 + ((t - s : NNReal) : ℝ))) ⁻¹' Set.Iic 0 := by
              ext p
              simp
            rw [hpre]
            exact
              (((Finset.measurable_sum Finset.univ fun i _ ↦
                  (measurable_pi_apply i.castSucc).comp measurable_snd).sub
                ((hresidual_meas.comp measurable_fst).add measurable_const)) measurableSet_Iic)
          have hupper :
              MeasurableSet
                {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
                  residualGap p.1 + ((t - s : NNReal) : ℝ) < ∑ i : Fin (l + 1), p.2 i} := by
            have hpre :
                {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
                  residualGap p.1 + ((t - s : NNReal) : ℝ) < ∑ i : Fin (l + 1), p.2 i} =
                  (fun p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) ↦
                    (∑ i : Fin (l + 1), p.2 i) -
                      (residualGap p.1 + ((t - s : NNReal) : ℝ))) ⁻¹' Set.Ioi 0 := by
              ext p
              simp [sub_pos]
            rw [hpre]
            exact
              (((prefixSum_measurable (l + 1)).comp measurable_snd).sub
                ((hresidual_meas.comp measurable_fst).add measurable_const)) measurableSet_Ioi
          have hEq :
              stripEvent =
                (headEvent ∩
                  {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
                    (∑ i : Fin l, p.2 i.castSucc) ≤
                      residualGap p.1 + ((t - s : NNReal) : ℝ)}) ∩
                  {p : (Fin K → ℝ) × (Fin (l + 1) → ℝ) |
                    residualGap p.1 + ((t - s : NNReal) : ℝ) <
                      ∑ i : Fin (l + 1), p.2 i} := by
            ext p
            simp [stripEvent, headEvent, and_assoc]
          rw [hEq]
          exact (hheadEvent.inter hlower).inter hupper
        have hprefixEvent_ae : prefixEvent =ᵐ[μ] splitBlock ⁻¹' headEvent := by
          filter_upwards
            [ae_arrivalTime_strictMono_and_tendsto_of_iid_exponential
              μ α W hW_iid hW0_law hα] with ω hgood
          simpa [Set.mem_preimage] using hprefixPathwise (ω := ω) hgood.1 hgood.2
        have hfullEvent_ae : fullEvent =ᵐ[μ] splitBlock ⁻¹' stripEvent := by
          filter_upwards
            [ae_arrivalTime_strictMono_and_tendsto_of_iid_exponential
              μ α W hW_iid hW0_law hα] with ω hgood
          simpa [Set.mem_preimage] using hfullPathwise (ω := ω) hgood.1 hgood.2
        have hsplitLaw : HasLaw splitBlock ν μ := by
          simpa [splitBlock, ν] using
            prefixBlockPairHasLawOfIidExponential μ α W hW_iid hW0_law hα K l
        have hmap_head : μ (splitBlock ⁻¹' headEvent) = ν headEvent := by
          calc
            μ (splitBlock ⁻¹' headEvent) = Measure.map splitBlock μ headEvent := by
              symm
              exact Measure.map_apply_of_aemeasurable hsplitLaw.aemeasurable hheadEvent
            _ = ν headEvent := by
              rw [hsplitLaw.map_eq]
        have hmap_strip : μ (splitBlock ⁻¹' stripEvent) = ν stripEvent := by
          calc
            μ (splitBlock ⁻¹' stripEvent) = Measure.map splitBlock μ stripEvent := by
              symm
              exact Measure.map_apply_of_aemeasurable hsplitLaw.aemeasurable hstripEvent
            _ = ν stripEvent := by
              rw [hsplitLaw.map_eq]
        have hfactor :
            ν stripEvent = ν headEvent * poissonMeasure (α * (t - s)) ({l} : Set ℕ) := by
          simpa [ν, stripEvent, headEvent] using
            prefixBase_relativeStrip_prodMass_eq_mul_headGap
              (α := α) hα (K := K) (l := l) (d := t - s)
              prefixBase hprefixBase residualGap hresidual_meas hresidual_nonneg
        have hmass :
            μ fullEvent = μ prefixEvent * poissonMeasure (α * (t - s)) ({l} : Set ℕ) := by
          calc
            μ fullEvent = μ (splitBlock ⁻¹' stripEvent) := hfullEvent_ae.measure_eq
            _ = ν stripEvent := hmap_strip
            _ = ν headEvent * poissonMeasure (α * (t - s)) ({l} : Set ℕ) := hfactor
            _ = μ (splitBlock ⁻¹' headEvent) * poissonMeasure (α * (t - s)) ({l} : Set ℕ) := by
                  rw [← hmap_head]
            _ = μ prefixEvent * poissonMeasure (α * (t - s)) ({l} : Set ℕ) := by
                  rw [← hprefixEvent_ae.measure_eq]
        simpa [fullEvent, prefixEvent, l] using hmass
      calc
        μ
            ({ω |
                (fun i : Fin (m + 1) ↦
                  renewalCountingProcess W (u i.succ) ω -
                    renewalCountingProcess W (u i.castSucc) ω) = k})
            =
              μ
                ({ω |
                    (fun i : Fin m ↦
                      renewalCountingProcess W (uPrefix i.succ) ω -
                        renewalCountingProcess W (uPrefix i.castSucc) ω) = kPrefix ∧
                    renewalCountingProcess W t ω - renewalCountingProcess W s ω =
                      k (Fin.last m)}) := by
                rw [hEventSplit]
        _ =
            μ
              ({ω |
                  (fun i : Fin m ↦
                    renewalCountingProcess W (uPrefix i.succ) ω -
                      renewalCountingProcess W (uPrefix i.castSucc) ω) = kPrefix ∧
                  renewalCountingProcess W s ω = K ∧
                    renewalCountingProcess W t ω - renewalCountingProcess W s ω =
                      k (Fin.last m)}) := by
                rw [hEventWithCount]
        _ =
            μ
              ({ω |
                  (fun i : Fin m ↦
                    renewalCountingProcess W (uPrefix i.succ) ω -
                      renewalCountingProcess W (uPrefix i.castSucc) ω) = kPrefix}) *
              poissonMeasure (α * (t - s)) ({k (Fin.last m)} : Set ℕ) := hMassFactor
        _ =
            (Measure.pi
              (fun i : Fin m ↦ poissonMeasure (α * (uPrefix i.succ - uPrefix i.castSucc))))
              ({kPrefix} : Set (Fin m → ℕ)) *
              poissonMeasure (α * (t - s)) ({k (Fin.last m)} : Set ℕ) := by
                rw [hPrefixMass]
        _ =
            (Measure.pi (fun i : Fin (m + 1) ↦ poissonMeasure (α * (u i.succ - u i.castSucc))))
              ({k} : Set (Fin (m + 1) → ℕ)) := by
                rw [hPoissonSplit]

/-- Helper for Theorem 5.36: on a zero-anchored monotone grid, the whole increment vector has the
product Poisson law determined by the grid spacings. -/
private theorem zeroAnchoredRenewalIncrementFinGridHasLawPiPoissonOfIidExponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α)
    {m : ℕ} (u : Fin (m + 1) → NNReal) (hu0 : u 0 = 0) (hu : Monotone u) :
    HasLaw
      (fun ω ↦ fun i : Fin m ↦
        renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω)
      (Measure.pi (fun i : Fin m ↦ poissonMeasure (α * (u i.succ - u i.castSucc)))) μ := by
  let f : Ω → Fin m → ℕ := fun ω i ↦
    renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω
  -- Proof comment: the countable-codomain packaging is already in place, so it remains to supply
  -- null-measurable singleton fibers and the exact singleton masses.
  refine hasLaw_of_countable_preimage_singleton
    (f := f)
    (ν := Measure.pi (fun i : Fin m ↦ poissonMeasure (α * (u i.succ - u i.castSucc)))) ?_ ?_
  · intro k
    simpa [f] using
      renewalIncrementFinGrid_singletonFiber_nullMeasurable_of_iid_exponential
        μ α W hW_iid hW0_law u k
  · intro k
    simpa [f] using
      zeroAnchoredRenewalIncrementFinGrid_singletonMassOfIidExponential
        μ α W hW_iid hW0_law hα u hu0 hu k

/-- Helper for Theorem 5.36: the renewal increment vector over a finite monotone grid has the
product Poisson law with rates given by the grid spacings. -/
theorem renewalIncrementFinGridHasLawPiPoissonOfIidExponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α)
    {m : ℕ} (u : Fin (m + 1) → NNReal) (hu : Monotone u) :
    HasLaw
      (fun ω ↦ fun i : Fin m ↦
        renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω)
      (Measure.pi (fun i : Fin m ↦ poissonMeasure (α * (u i.succ - u i.castSucc)))) μ := by
  -- Route correction: the public theorems below should use the finite-grid definition of
  -- `HasIndepIncrements` directly, so the unresolved work is localized to the zero-anchored
  -- finite-grid law. The augmentation/projection part is handled below.
  let v : Fin (m + 2) → NNReal := Fin.cons 0 u
  have hAugLaw :
      HasLaw
        (fun ω ↦ fun i : Fin (m + 1) ↦
          renewalCountingProcess W (v i.succ) ω - renewalCountingProcess W (v i.castSucc) ω)
        (Measure.pi (fun i : Fin (m + 1) ↦ poissonMeasure (α * (v i.succ - v i.castSucc)))) μ := by
    have hv : Monotone v := by
      refine (Fin.monotone_iff_le_succ (f := v)).2 ?_
      intro i
      cases i using Fin.cases with
      | zero =>
          simp [v]
      | succ j =>
          simpa [v] using hu (Fin.castSucc_le_succ j)
    -- Proof comment: the augmented grid `v = 0 :: u` is zero-anchored, so the packaged
    -- zero-anchored finite-grid law applies directly.
    exact
      zeroAnchoredRenewalIncrementFinGridHasLawPiPoissonOfIidExponential
        μ α W hW_iid hW0_law hα v rfl hv
  let split :
      (Fin (m + 1) → ℕ) ≃ᵐ ℕ × (Fin m → ℕ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℕ) 0
  have hSplitProjLaw :
      HasLaw
        (fun x : Fin (m + 1) → ℕ ↦ split x)
        ((poissonMeasure (α * (v (0 : Fin (m + 1)).succ - v (0 : Fin (m + 1)).castSucc))).prod
          (Measure.pi
            (fun i : Fin m ↦
              poissonMeasure (α * (v ((0 : Fin (m + 1)).succAbove i).succ -
                v ((0 : Fin (m + 1)).succAbove i).castSucc)))))
        (Measure.pi (fun i : Fin (m + 1) ↦ poissonMeasure (α * (v i.succ - v i.castSucc)))) := by
    -- Proof comment: `piFinSuccAbove` separates the first coordinate of the augmented increment
    -- vector from its successor tail.
    exact
      (measurePreserving_piFinSuccAbove
        (α := fun _ : Fin (m + 1) ↦ ℕ)
        (μ := fun i : Fin (m + 1) ↦ poissonMeasure (α * (v i.succ - v i.castSucc)))
        0).hasLaw
  have hTailProjLaw :
      HasLaw
        Prod.snd
        (Measure.pi (fun i : Fin m ↦ poissonMeasure (α * (v i.succ.succ - v i.succ.castSucc))))
        ((poissonMeasure (α * (v (0 : Fin (m + 1)).succ - v (0 : Fin (m + 1)).castSucc))).prod
          (Measure.pi (fun i : Fin m ↦ poissonMeasure (α * (v i.succ.succ - v i.succ.castSucc))))) :=
      by
        refine ⟨measurable_snd.aemeasurable, ?_⟩
        letI :
            IsProbabilityMeasure
              (poissonMeasure (α * (v (0 : Fin (m + 1)).succ - v (0 : Fin (m + 1)).castSucc))) :=
          inferInstance
        -- Proof comment: under a product law, forgetting the first coordinate preserves the tail
        -- product law.
        simpa using
          (Measure.map_snd_prod
            (μ := poissonMeasure (α * (v (0 : Fin (m + 1)).succ - v (0 : Fin (m + 1)).castSucc)))
            (ν := Measure.pi
              (fun i : Fin m ↦ poissonMeasure (α * (v i.succ.succ - v i.succ.castSucc)))))
  have hTailLaw :
      HasLaw
        (fun ω ↦ fun i : Fin m ↦
          renewalCountingProcess W (v i.succ.succ) ω - renewalCountingProcess W (v i.succ.castSucc) ω)
        (Measure.pi (fun i : Fin m ↦ poissonMeasure (α * (v i.succ.succ - v i.succ.castSucc)))) μ :=
    (hTailProjLaw.fun_comp (hSplitProjLaw.fun_comp hAugLaw)).congr <| by
      -- Proof comment: after splitting off coordinate `0`, the second component is literally the
      -- successor tail of the augmented increment vector.
      filter_upwards [] with ω
      funext i
      have htail :=
        congrFun
          (piFinSuccAbove_zero_snd_eq_tail (m := m))
          (fun j : Fin (m + 1) ↦
            renewalCountingProcess W (v j.succ) ω - renewalCountingProcess W (v j.castSucc) ω)
      exact (congrFun htail i).symm
  -- Proof comment: on the augmented grid `v = 0 :: u`, the successor-tail increment vector is
  -- exactly the original increment vector over `u`.
  simpa [v] using hTailLaw

/-- Helper for Theorem 5.36: under the i.i.d. exponential hypotheses, the renewal counting
process has independent increments. -/
theorem renewalCountingProcess_hasIndepIncrements_of_iid_exponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    HasIndepIncrements (renewalCountingProcess W) μ := by
  intro n t ht
  have hGridLaw :
      HasLaw
        (fun ω ↦ fun i : Fin n ↦
          renewalCountingProcess W (t i.succ) ω - renewalCountingProcess W (t i.castSucc) ω)
        (Measure.pi (fun i : Fin n ↦ poissonMeasure (α * (t i.succ - t i.castSucc)))) μ :=
    renewalIncrementFinGridHasLawPiPoissonOfIidExponential μ α W hW_iid hW0_law hα t ht
  have hmeas :
      ∀ i : Fin n,
        AEMeasurable
          (fun ω ↦ renewalCountingProcess W (t i.succ) ω - renewalCountingProcess W (t i.castSucc) ω)
          μ := by
    intro i
    -- Proof comment: each coordinate increment is an evaluation of the finite-grid increment
    -- vector, so its measurability comes from the vector-valued law.
    exact (measurable_pi_apply i).aemeasurable.comp_aemeasurable hGridLaw.aemeasurable
  have hcoordLaw :
      ∀ i : Fin n,
        HasLaw
          (fun ω ↦ renewalCountingProcess W (t i.succ) ω - renewalCountingProcess W (t i.castSucc) ω)
          (poissonMeasure (α * (t i.succ - t i.castSucc))) μ := by
    intro i
    have hevalLaw :
        HasLaw
          (Function.eval i)
          (poissonMeasure (α * (t i.succ - t i.castSucc)))
          (Measure.pi (fun j : Fin n ↦ poissonMeasure (α * (t j.succ - t j.castSucc)))) := by
      exact
        (measurePreserving_eval
          (fun j : Fin n ↦ poissonMeasure (α * (t j.succ - t j.castSucc))) i).hasLaw
    -- Proof comment: evaluate the product-law vector at coordinate `i`.
    simpa [Function.comp] using hevalLaw.fun_comp hGridLaw
  have hcoordMap :
      (fun i : Fin n ↦
        Measure.map
          (fun ω ↦ renewalCountingProcess W (t i.succ) ω - renewalCountingProcess W (t i.castSucc) ω)
          μ) =
        fun i : Fin n ↦ poissonMeasure (α * (t i.succ - t i.castSucc)) := by
    funext i
    exact (hcoordLaw i).map_eq
  letI : IsProbabilityMeasure μ := hGridLaw.isProbabilityMeasure
  -- Proof comment: once the finite-grid increment vector has the product law, independence is
  -- exactly the standard product-measure characterization.
  refine (iIndepFun_iff_map_fun_eq_pi_map hmeas).2 ?_
  simpa [hcoordMap] using hGridLaw.map_eq

/-- Helper for Theorem 5.36: under the i.i.d. exponential hypotheses, each strict increment of the
renewal counting process has the expected Poisson law. -/
theorem renewalIncrement_hasLawPoisson_of_iid_exponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    ∀ ⦃s t : NNReal⦄, s < t →
      HasLaw (fun ω ↦ renewalCountingProcess W t ω - renewalCountingProcess W s ω)
        (poissonMeasure (α * (t - s))) μ := by
  intro s t hst
  let u : Fin 2 → NNReal := Fin.cons s (fun _ ↦ t)
  have hu : Monotone u := by
    refine (Fin.monotone_iff_le_succ (f := u)).2 ?_
    intro i
    fin_cases i
    simpa [u] using (le_of_lt hst)
  have hGridLaw :
      HasLaw
        (fun ω ↦ fun i : Fin 1 ↦
          renewalCountingProcess W (u i.succ) ω - renewalCountingProcess W (u i.castSucc) ω)
        (Measure.pi (fun i : Fin 1 ↦ poissonMeasure (α * (u i.succ - u i.castSucc)))) μ :=
    renewalIncrementFinGridHasLawPiPoissonOfIidExponential μ α W hW_iid hW0_law hα u hu
  have hevalLaw :
      HasLaw
        (Function.eval (0 : Fin 1))
        (poissonMeasure (α * (u (0 : Fin 1).succ - u (0 : Fin 1).castSucc)))
        (Measure.pi
          (fun i : Fin 1 ↦ poissonMeasure (α * (u i.succ - u i.castSucc)))) := by
    exact
      (measurePreserving_eval
        (fun i : Fin 1 ↦ poissonMeasure (α * (u i.succ - u i.castSucc))) (0 : Fin 1)).hasLaw
  have hcoordLaw :
      HasLaw
        (fun ω ↦ renewalCountingProcess W (u (0 : Fin 1).succ) ω -
          renewalCountingProcess W (u (0 : Fin 1).castSucc) ω)
        (poissonMeasure (α * (u (0 : Fin 1).succ - u (0 : Fin 1).castSucc))) μ := by
    -- Proof comment: the unique coordinate of the `Fin 1` increment vector is the desired single
    -- interval increment.
    simpa [Function.comp] using hevalLaw.fun_comp hGridLaw
  simpa [u] using hcoordLaw

-- Proof sketch: `rawRenewalCountingProcess W` is the textbook `sInf` renewal count. The canonical
-- `renewalCountingProcess W` agrees with it on the almost-sure genuine renewal paths singled out
-- by the exponential interarrival hypotheses, and the chapter's `IsPoissonProcess` owner is then
-- applied to that canonical representative. The auxiliary a.e. arrival-time lemmas keep the
-- source-facing assumptions at the i.i.d. exponential layer; independent increments still come
-- from disjoint blocks of the i.i.d. interarrival sequence, the single-coordinate exponential law
-- propagates to every coordinate via `IsIID`, and Theorem 5.35 identifies each increment over
-- `[s,t]` with a Poisson law of parameter `α * (t - s)`.
-- Semantic recall: no direct mathlib renewal-process owner surfaced, so the local
-- `IsPoissonProcess` API is used only for the chapter's canonical representative of the textbook
-- count.
/-- Helper for Theorem 5.36: the chapter's canonical renewal counting representative agrees almost
surely with the raw textbook `sInf` count under the i.i.d. exponential hypotheses. -/
theorem ae_rawRenewalCountingProcess_eq_renewalCountingProcess_of_iid_exponential_interarrivals
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_meas : ∀ n, Measurable (W n))
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    ∀ᵐ ω ∂μ, ∀ t, rawRenewalCountingProcess W t ω = renewalCountingProcess W t ω := by
  let _ := hW_meas
  filter_upwards
    [ae_arrivalTime_strictMono_and_tendsto_of_iid_exponential μ α W hW_iid hW0_law hα]
    with ω hω
  intro t
  have h_first_arrival : 0 < arrivalTime W 1 ω := by
    -- Proof comment: the almost-sure strict-monotonicity event yields the positive first
    -- arrival-time hypothesis needed to select the raw-count branch.
    simpa [arrivalTime_zero] using hω.1 (show 0 < 1 by omega)
  -- Proof comment: on the genuine renewal event, the public representative agrees pointwise with
  -- the textbook `sInf` count.
  exact (renewalCountingProcess_eq_rawRenewalCountingProcess W h_first_arrival hω.2).symm

/-- Auxiliary corollary for Theorem 5.36: the chapter's canonical representative of the textbook
renewal counting family is a Poisson process with intensity `α`. -/
theorem renewalCountingProcess_representative_isPoissonProcess_of_iid_exponential_interarrivals
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_meas : ∀ n, Measurable (W n))
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    IsPoissonProcess α μ (renewalCountingProcess W) := by
  -- Proof comment: once the canonical representative is known to be stochastic, zero-started,
  -- monotone, and to satisfy the two textbook increment axioms, the owner constructor packages it
  -- as a Poisson process.
  refine isPoissonProcess_of_textbook
    (hstochastic := renewalCountingProcess_isStochasticProcess W hW_meas)
    (hzero := renewalCountingProcess_zero_eq W)
    (hmono := renewalCountingProcess_monotone W)
    (hindep :=
      renewalCountingProcess_hasIndepIncrements_of_iid_exponential μ α W hW_iid hW0_law hα)
    (hpoisson :=
      renewalIncrement_hasLawPoisson_of_iid_exponential μ α W hW_iid hW0_law hα)

/-- Theorem 5.36: the textbook renewal counting family attached to an i.i.d. exponential
interarrival sequence is a Poisson process with intensity `α`. -/
theorem renewalCountingProcess_isPoissonProcess_of_iid_exponential_interarrivals
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_meas : ∀ n, Measurable (W n))
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    IsPoissonProcess α μ (renewalCountingProcess W) := by
  -- Proof comment: the previous corollary already proves the theorem for the chapter's canonical
  -- representative of the textbook renewal count.
  exact
    renewalCountingProcess_representative_isPoissonProcess_of_iid_exponential_interarrivals
      μ α W hW_meas hW_iid hW0_law hα

end
