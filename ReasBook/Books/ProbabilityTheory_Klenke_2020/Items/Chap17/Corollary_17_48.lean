/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_47

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/- Layering for Corollary 17.48:
- `expectedFirstReturnTime` and `returnCycleOccupationMeasure` are the primitive source-facing
  data from the preceding items.
- `positiveRecurrentInvariantDistribution` is the source-facing normalized excursion law `π_x`.
- The invariant-distribution conclusion itself should be stated through the owner predicate
  `Kernel.Invariant`. -/

section

variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

/-- Helper for Corollary 17.48: the first return time is at least one, so its expectation is
nonzero. -/
lemma one_le_expectedFirstReturnTime (x : E) :
    (1 : ℝ≥0∞) ≤ expectedFirstReturnTime P X x := by
  -- Proof comment: the first positive entrance time starts at time `1`, so it dominates the
  -- constant function `1` pointwise and therefore also after integration.
  have hpointwise : ∀ ω : Ω, (1 : ℝ≥0∞) ≤ ((τ_[X, x]^1) ω : ℝ≥0∞) := by
    intro ω
    exact_mod_cast
      (show (1 : ℕ∞) ≤ (τ_[X, x]^1) ω by
        simpa [iteratedEntranceTime_one] using
          (le_hittingAfter (u := X) (s := ({x} : Set E)) (n := 1) ω))
  calc
    (1 : ℝ≥0∞) = ∫⁻ _ω, (1 : ℝ≥0∞) ∂(P x : Measure Ω) := by simp
    _ ≤ ∫⁻ ω, ((τ_[X, x]^1) ω : ℝ≥0∞) ∂(P x : Measure Ω) := by
      exact lintegral_mono hpointwise
    _ = expectedFirstReturnTime P X x := by
      simp [expectedFirstReturnTime]

end

section

variable {κ : ℕ → Kernel E E}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization κ P X]

/-- Helper for Corollary 17.48: the positive-time return event
`{ω | (τ_[X, x]^1) ω < ⊤}` is measurable. -/
lemma measurableSet_firstReturnTimeFinite
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization κ P X] (x : E) :
    MeasurableSet {ω | (τ_[X, x]^1) ω < ⊤} := by
  -- Proof comment: finiteness of the first return time means the path hits `x` at some time
  -- `n + 1`, so the event is a countable union of measurable singleton fibers.
  have hEq :
      {ω | (τ_[X, x]^1) ω < ⊤} = ⋃ n : ℕ, X n.succ ⁻¹' ({x} : Set E) := by
    ext ω
    constructor
    · intro hω
      rcases (hittingAfter_singleton_lt_top_iff X x ω).1 (by
        simpa [iteratedEntranceTime_one] using hω) with ⟨n, hn, hnx⟩
      rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨m, rfl⟩
      exact Set.mem_iUnion.2 ⟨m, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hnx⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      exact (hittingAfter_singleton_lt_top_iff X x ω).2
        ⟨n.succ, Nat.succ_pos _, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hn⟩
  rw [hEq]
  refine MeasurableSet.iUnion ?_
  intro n
  exact
    (IsMarkovProcessRealization.measurable_process (κ := κ) (P := P) (X := X) n.succ)
      (measurableSet_singleton x)

/-- Helper for Corollary 17.48: finite expected first return time forces recurrence. -/
lemma positiveRecurrentState_isRecurrentState
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x : E) (hx : IsPositiveRecurrentState P X x) :
    IsRecurrentState P X x := by
  -- Proof comment: if the complement of the finite-return event had positive mass, the first
  -- return time would dominate an `∞`-valued indicator on a positive-measure set, contradicting
  -- finiteness of the expectation.
  let A : Set Ω := {ω | (τ_[X, x]^1) ω < ⊤}
  have hA_meas : MeasurableSet A :=
    measurableSet_firstReturnTimeFinite (κ := κ) (P := P) (X := X) x
  have hAc_zero : (P x : Measure Ω) Aᶜ = 0 := by
    by_contra hAc_zero
    have hindicator_top :
        ∫⁻ ω,
          Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω ∂(P x : Measure Ω) = ∞ := by
      have hmeas :
          AEMeasurable (Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞))) (P x : Measure Ω) :=
        (measurable_const.indicator hA_meas.compl).aemeasurable
      have hset :
          (P x : Measure Ω)
            {ω | Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω = ∞} ≠ 0 := by
        have hEq :
            {ω | Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω = ∞} = Aᶜ := by
          ext ω
          by_cases hω : ω ∈ Aᶜ
          · have hnotA : ω ∉ A := hω
            simp [Set.indicator, hω, hnotA]
          · have hA : ω ∈ A := by simpa using hω
            simp [Set.indicator, hω, hA]
        simpa [hEq] using hAc_zero
      exact lintegral_eq_top_of_measure_eq_top_ne_zero hmeas hset
    have hdom :
        ∫⁻ ω, Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω ∂(P x : Measure Ω) ≤
          expectedFirstReturnTime P X x := by
      rw [expectedFirstReturnTime]
      refine lintegral_mono fun ω ↦ ?_
      by_cases hω : ω ∈ Aᶜ
      · have hτ : (τ_[X, x]^1) ω = ⊤ := by
          simpa [A, Set.mem_setOf_eq, lt_top_iff_ne_top] using hω
        simp [Set.indicator, hω, hτ]
      · simp [Set.indicator, hω]
    have htop : expectedFirstReturnTime P X x = ∞ := by
      simpa [hindicator_top] using hdom
    exact (ne_of_lt hx) htop
  have hA_prob : (P x : Measure Ω) A = 1 := by
    have hA_le : (P x : Measure Ω) A ≤ 1 := by
      have hA_le_univ : (P x : Measure Ω) A ≤ (P x : Measure Ω) Set.univ :=
        measure_mono (show A ⊆ Set.univ by intro ω _; simp)
      simpa using hA_le_univ
    have hA_ge : 1 ≤ (P x : Measure Ω) A := by
      have hunion : A ∪ Aᶜ = Set.univ := by
        ext ω
        simp [A]
      calc
        1 = (P x : Measure Ω) Set.univ := by simp
        _ ≤ (P x : Measure Ω) A + (P x : Measure Ω) Aᶜ := by
              have hUnion_le :
                  (P x : Measure Ω) (A ∪ Aᶜ) ≤ (P x : Measure Ω) A + (P x : Measure Ω) Aᶜ :=
                measure_union_le A Aᶜ
              simpa [hunion] using hUnion_le
        _ = (P x : Measure Ω) A := by rw [hAc_zero, add_zero]
    exact le_antisymm hA_le hA_ge
  have hhit :
      (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = 1 := by
    have hEq : {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = A := by
      ext ω
      simpa [A, iteratedEntranceTime_one] using (hittingAfter_singleton_lt_top_iff X x ω).symm
    rw [hEq]
    exact hA_prob
  -- Proof comment: the recurrent-state predicate is exactly the probability-one version of the
  -- same positive-time return event.
  rw [IsRecurrentState, everHitsProbability_def]
  exact (ENNReal.toReal_eq_one_iff _).2 hhit

/-- Helper for Corollary 17.48: the first return time is at most `n` exactly when `x` is visited
between times `1` and `n`. -/
lemma firstReturnTime_le_iff
    (x : E) (n : ℕ) (ω : Ω) :
    (τ_[X, x]^1) ω ≤ n ↔ ∃ j ∈ Set.Icc 1 n, X j ω = x := by
  -- Proof comment: specialize the bounded-hitting-time characterization of `hittingAfter` to the
  -- singleton set `{x}` and rewrite the membership condition.
  simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using
    (hittingAfter_le_iff (u := X) (s := ({x} : Set E)) (n := 1) (ω := ω) (i := n))

/-- Helper for Corollary 17.48: the event `{ω | (τ_[X, x]^1) ω ≤ n}` is measurable. -/
lemma measurableSet_firstReturnTimeLe
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization κ P X] (x : E) (n : ℕ) :
    MeasurableSet {ω | (τ_[X, x]^1) ω ≤ n} := by
  -- Proof comment: rewrite the bounded return-time event as a finite union of singleton fibers
  -- of the coordinates `X j`.
  have hEq :
      {ω | (τ_[X, x]^1) ω ≤ n} =
        ⋃ j ∈ ((Finset.Icc 1 n : Finset ℕ) : Set ℕ), X j ⁻¹' ({x} : Set E) := by
    ext ω
    simp [firstReturnTime_le_iff, Finset.mem_Icc]
  rw [hEq]
  refine MeasurableSet.biUnion (Set.to_countable _) ?_
  intro j hj
  exact
    (IsMarkovProcessRealization.measurable_process (κ := κ) (P := P) (X := X) j)
      (MeasurableSet.singleton x)

/-- Helper for Corollary 17.48: the counting measure of the initial segment below `t : ℕ∞`
recovers `t` itself. -/
lemma count_lt_enat_eq (t : ℕ∞) :
    Measure.count {n : ℕ | (n : ℕ∞) < t} = t := by
  -- Proof comment: split into the infinite case and the finite case identified by `ENat.toNat`.
  by_cases ht : t = ⊤
  · subst ht
    simpa using
      (Measure.count_univ : Measure.count (Set.univ : Set ℕ) = ENat.card ℕ)
  · have hEq :
        {n : ℕ | (n : ℕ∞) < t} = (Finset.range (ENat.toNat t) : Set ℕ) := by
          have hco : (ENat.toNat t : ℕ∞) = t := (ENat.coe_toNat_eq_self).2 ht
          ext n
          rw [← hco]
          simp [Finset.mem_range]
    rw [hEq, Measure.count_apply_finset' (by simpa using (Finset.range (ENat.toNat t)).measurableSet)]
    have hco : (ENat.toNat t : ℕ∞) = t := (ENat.coe_toNat_eq_self).2 ht
    rw [Finset.card_range]
    exact congrArg (fun s : ℕ∞ ↦ (s : ℝ≥0∞)) hco

/-- Helper for Corollary 17.48: the pointwise tail-indicator series is the counting measure of the
tail set `{n | n < τ_x^1(ω)}`. -/
lemma tsum_tailIndicators_eq_countTailMass
    (x : E) (ω : Ω) :
    (∑' n : ℕ,
      Set.indicator {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'} (fun _ ↦ (1 : ℝ≥0∞)) ω) =
      Measure.count {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: rewrite the sum over `ℕ` as the sum over the subtype of admissible indices.
  rw [Measure.count_apply MeasurableSet.of_discrete]
  calc
    ∑' n : ℕ,
        Set.indicator {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'} (fun _ ↦ (1 : ℝ≥0∞)) ω
      = ∑' _ : {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω}, (1 : ℝ≥0∞) := by
          simpa [Set.indicator_apply] using
            (tsum_subtype {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω}
              (fun _ : ℕ ↦ (1 : ℝ≥0∞))).symm
    _ = ENat.card {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          simpa using
            (ENNReal.tsum_one :
              ∑' _ : {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω}, (1 : ℝ≥0∞) =
                ENat.card {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω})
    _ = ({n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω}).encard := by
          rw [ENat.card_coe_set_eq]

/-- Helper for Corollary 17.48: the first return time equals the tail-indicator series of the
events `{ω | n < τ_[X, x]^1 ω}`. -/
lemma firstReturnTime_eq_tsum_tailIndicators
    (x : E) (ω : Ω) :
    ((τ_[X, x]^1) ω : ℝ≥0∞) =
      ∑' n : ℕ,
        Set.indicator {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'} (fun _ ↦ (1 : ℝ≥0∞)) ω := by
  -- Proof comment: rewrite the series as a counting measure of the tail set and identify it with
  -- the `ℕ∞`-valued first return time.
  calc
    ((τ_[X, x]^1) ω : ℝ≥0∞)
      = Measure.count {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          symm
          exact count_lt_enat_eq ((τ_[X, x]^1) ω)
    _ = ∑' n : ℕ,
          Set.indicator
            {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'} (fun _ ↦ (1 : ℝ≥0∞)) ω := by
          symm
          exact tsum_tailIndicators_eq_countTailMass (X := X) x ω

/-- Helper for Corollary 17.48: the tail event `{ω | n < τ_x^1(ω)}` is measurable. -/
lemma measurableSet_firstReturnTimeTail
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization κ P X] (x : E) (n : ℕ) :
    MeasurableSet {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: the strict tail is the complement of the measurable bounded-horizon event.
  have hEq :
      {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} = {ω | (τ_[X, x]^1) ω ≤ n}ᶜ := by
    ext ω
    simp
  rw [hEq]
  exact (measurableSet_firstReturnTimeLe (κ := κ) (P := P) (X := X) x n).compl

/-- Helper for Corollary 17.48: `𝔼_x[τ_x^1]` is the tail-probability series of the first return
time. -/
lemma expectedFirstReturnTime_eq_tsum_tailProbabilities
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x : E) :
    expectedFirstReturnTime P X x =
      ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: rewrite the integrand pointwise as the tail-indicator series, commute the
  -- countable sum through the integral, and evaluate each indicator integral as a tail
  -- probability.
  rw [expectedFirstReturnTime]
  calc
    ∫⁻ ω, ((τ_[X, x]^1) ω : ℝ≥0∞) ∂(P x : Measure Ω)
      = ∫⁻ ω,
          ∑' n : ℕ,
            Set.indicator {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'} (fun _ ↦ (1 : ℝ≥0∞)) ω
          ∂(P x : Measure Ω) := by
            refine lintegral_congr_ae ?_
            filter_upwards [] with ω
            rw [firstReturnTime_eq_tsum_tailIndicators (X := X) x ω]
    _ = ∑' n : ℕ,
          ∫⁻ ω,
            Set.indicator {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'} (fun _ ↦ (1 : ℝ≥0∞)) ω
          ∂(P x : Measure Ω) := by
            have hIndicator_meas :
                ∀ n : ℕ,
                  AEMeasurable
                    (fun ω ↦
                      Set.indicator
                        {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'}
                        (fun _ ↦ (1 : ℝ≥0∞)) ω)
                    (P x : Measure Ω) := by
              intro n
              have hmeas :
                  Measurable
                    (Set.indicator
                      {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'}
                      (fun _ ↦ (1 : ℝ≥0∞))) :=
                measurable_const.indicator
                  (measurableSet_firstReturnTimeTail (κ := κ) (P := P) (X := X) x n)
              exact hmeas.aemeasurable
            rw [lintegral_tsum hIndicator_meas]
    _ = ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          refine tsum_congr fun n ↦ ?_
          simpa using
            (lintegral_indicator_one (μ := (P x : Measure Ω))
              (s := {ω | (n : ℕ∞) < (τ_[X, x]^1) ω})
              (measurableSet_firstReturnTimeTail (κ := κ) (P := P) (X := X) x n))

-- Source alignment: the normalization and state-slice summations below use countable singleton
-- decompositions over `E`; in particular, the `∑' y : E, ...` slice recombination and the
-- corresponding `lintegral_tsum` step stay in the same countable-state regime as Theorem 17.47.
variable [Countable E]

/-- Helper for Corollary 17.48: at a fixed time `n`, summing the state-slice probabilities over
all states recovers the tail probability `ℙ_x[n < τ_x^1]`. -/
lemma tsum_stateSliceProbabilities_eq_tailProbability
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] [Countable E]
    (x : E) (n : ℕ) :
    ∑' y : E, (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} =
      (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  classical
  -- Route correction: keep the slice recombination inside the `[Countable E]` regime, where the
  -- state sum can be commuted with the integral and collapsed pointwise by `tsum_eq_single`.
  let A : Set Ω := {ω | (n : ℕ∞) < (τ_[X, x]^1) ω}
  have hA_meas : MeasurableSet A :=
    measurableSet_firstReturnTimeTail (κ := κ) (P := P) (X := X) x n
  have hSlice_meas : ∀ y : E, MeasurableSet {ω | X n ω = y ∧ ω ∈ A} := by
    intro y
    have hState :
        MeasurableSet (X n ⁻¹' ({y} : Set E)) :=
      (IsMarkovProcessRealization.measurable_process (κ := κ) (P := P) (X := X) n)
        (MeasurableSet.singleton y)
    have hEq :
        {ω | X n ω = y ∧ ω ∈ A} = (X n ⁻¹' ({y} : Set E)) ∩ A := by
      ext ω
      simp [A]
    rw [hEq]
    exact hState.inter hA_meas
  -- Proof comment: rewrite each slice probability as an indicator integral, commute the countable
  -- state sum with the integral, and collapse the pointwise sum to the unique state `X n ω`.
  calc
    ∑' y : E, (P x : Measure Ω) {ω | X n ω = y ∧ ω ∈ A}
      = ∑' y : E,
          ∫⁻ ω, Set.indicator {ω | X n ω = y ∧ ω ∈ A} (fun _ ↦ (1 : ℝ≥0∞)) ω
            ∂(P x : Measure Ω) := by
            refine tsum_congr fun y ↦ ?_
            symm
            exact
              lintegral_indicator_one (μ := (P x : Measure Ω))
                (s := {ω | X n ω = y ∧ ω ∈ A}) (hSlice_meas y)
    _ = ∫⁻ ω,
          ∑' y : E, Set.indicator {ω | X n ω = y ∧ ω ∈ A} (fun _ ↦ (1 : ℝ≥0∞)) ω
            ∂(P x : Measure Ω) := by
            symm
            rw [lintegral_tsum fun y ↦
              (measurable_const.indicator (hSlice_meas y)).aemeasurable]
    _ = ∫⁻ ω, Set.indicator A (fun _ ↦ (1 : ℝ≥0∞)) ω ∂(P x : Measure Ω) := by
          refine lintegral_congr_ae ?_
          filter_upwards [] with ω
          by_cases hω : ω ∈ A
          · have hω' : (n : ℕ∞) < (τ_[X, x]^1) ω := by
                simpa [A] using hω
            have hsum :
                (∑' y : E, if X n ω = y then (1 : ℝ≥0∞) else 0) = 1 := by
              rw [tsum_eq_single (b := X n ω)]
              · simp
              · intro z hz
                simp [eq_comm, hz]
            simpa [A, Set.indicator, hω, hω'] using hsum
          · have hnot : ¬ (n : ℕ∞) < (τ_[X, x]^1) ω := by
                simpa [A] using hω
            simp [A, Set.indicator, hω, hnot]
    _ = (P x : Measure Ω) A := by
          simpa using
            (lintegral_indicator_one (μ := (P x : Measure Ω)) (s := A) hA_meas)
    _ = (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          rfl

/-- Helper for Corollary 17.48: the total excursion occupation mass agrees with the tail
probability series of `τ_[X, x]^1`. -/
lemma tsum_returnCycleOccupationMass_eq_tsum_tailProbabilities
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] [Countable E]
    (x : E) :
    ∑' y : E, returnCycleOccupationMass P X x y =
      ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: rewrite the outer state sum as a count integral, commute it past the time
  -- series, and collapse each fixed-time slice with the previous helper.
  calc
    ∑' y : E, returnCycleOccupationMass P X x y
      = ∫⁻ y, returnCycleOccupationMass P X x y ∂Measure.count := by
          rw [lintegral_count]
    _ = ∫⁻ y, ∑' n : ℕ,
          (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}
          ∂Measure.count := by
          rfl
    _ = ∑' n : ℕ,
          ∫⁻ y, (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}
          ∂Measure.count := by
          rw [lintegral_tsum fun n ↦
            (Measurable.of_discrete :
              Measurable fun y : E ↦
                (P x : Measure Ω)
                  {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}).aemeasurable]
    _ = ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          refine tsum_congr fun n ↦ ?_
          rw [lintegral_count]
          exact tsum_stateSliceProbabilities_eq_tailProbability
            (P := P) (X := X) (κ := κ) x n

/-- Helper for Corollary 17.48: the return-cycle occupation measure has total mass
`𝔼_x[τ_x^1]`. -/
lemma returnCycleOccupationMeasure_univ_eq_expectedFirstReturnTime
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] [Countable E]
    (x : E) :
    (μ[P, X] x) Set.univ = expectedFirstReturnTime P X x := by
  -- Proof comment: evaluate `withDensity` on `Set.univ`, rewrite the count integral as a series,
  -- and identify that series with the first-return tail expansion.
  calc
    (μ[P, X] x) Set.univ
      = ∫⁻ y, returnCycleOccupationMass P X x y ∂Measure.count := by
          rw [returnCycleOccupationMeasure, withDensity_apply _ MeasurableSet.univ,
            Measure.restrict_univ]
    _ = ∑' y : E, returnCycleOccupationMass P X x y := by
          rw [lintegral_count]
    _ = ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          rw [tsum_returnCycleOccupationMass_eq_tsum_tailProbabilities
            (P := P) (X := X) (κ := κ) x]
    _ = expectedFirstReturnTime P X x := by
          symm
          exact expectedFirstReturnTime_eq_tsum_tailProbabilities
            (P := P) (X := X) (κ := κ) x

-- Proof sketch: identify the total mass of `returnCycleOccupationMeasure P X x` with the
-- expected first return time `𝔼_x[τ_x^1]`; positive recurrence makes this mass finite, and
-- scaling by its inverse normalizes the total mass to `1`.
/-- The excursion occupation measure `μ_x` divided by `𝔼_x[τ_x^1]` is a probability measure
for a positive recurrent state `x`. -/
theorem isProbabilityMeasure_smul_returnCycleOccupationMeasure
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] [Countable E]
    (x : E) (hx : IsPositiveRecurrentState P X x) :
    IsProbabilityMeasure
      ((expectedFirstReturnTime P X x)⁻¹ • (μ[P, X] x)) := by
  have hmass :
      (μ[P, X] x) Set.univ = expectedFirstReturnTime P X x :=
    returnCycleOccupationMeasure_univ_eq_expectedFirstReturnTime
      (P := P) (X := X) (κ := κ) x
  have hmass_ne_zero : (μ[P, X] x) Set.univ ≠ 0 := by
    have hpos :
        0 < expectedFirstReturnTime P X x := by
      exact lt_of_lt_of_le zero_lt_one
        (one_le_expectedFirstReturnTime (P := P) (X := X) x)
    rw [hmass]
    exact ne_of_gt hpos
  -- Proof comment: the total mass is finite and nonzero, so scaling by its inverse makes the
  -- total mass exactly `1`.
  refine isProbabilityMeasure_iff.2 ?_
  rw [Measure.smul_apply, hmass]
  exact ENNReal.inv_mul_cancel (by simpa [hmass] using hmass_ne_zero) (ne_of_lt hx)

/-- The distribution `π_x := μ_x / 𝔼_x[τ_x^1]` obtained by normalizing the return-cycle
occupation measure of the state `x`. -/
def positiveRecurrentInvariantDistribution
    (x : E) (hx : IsPositiveRecurrentState P X x) : ProbabilityMeasure E :=
  ⟨(expectedFirstReturnTime P X x)⁻¹ • (μ[P, X] x),
    isProbabilityMeasure_smul_returnCycleOccupationMeasure
      (κ := κ) (P := P) (X := X) x hx⟩

omit [DiscreteMeasurableSpace E] [Countable E] in
/-- Helper for Corollary 17.48: scaling preserves kernel invariance of a measure. -/
lemma kernelInvariant_smul {μ : Measure E} {a : ℝ≥0∞}
    (hμ : Kernel.Invariant (κ 1) μ) :
    Kernel.Invariant (κ 1) (a • μ) := by
  -- Proof comment: `Measure.bind` is linear in the measure argument, so the invariance equation
  -- scales on both sides.
  rw [Kernel.Invariant] at hμ ⊢
  calc
    (a • μ).bind (κ 1) = a • (μ.bind (κ 1)) := Measure.bind_smul a μ (κ 1)
    _ = a • μ := by rw [hμ]

-- Proof sketch: if the chain is positive recurrent, then every state `x` is positive recurrent.
-- Apply the state-level normalization to `x`, use Theorem 17.47 for the underlying excursion
-- measure `(μ[P, X] x)`, and preserve invariance under scaling by `(𝔼_x[τ_x^1])⁻¹`.
/-- Corollary 17.48: on a countable discrete state space, if the chain `X` is positive
recurrent, then for any state `x`, the normalized excursion law
`π_x := μ_x / 𝔼_x[τ_x^1]` is an invariant distribution for the one-step kernel `κ 1`. -/
theorem positiveRecurrentInvariantDistribution_isInvariantDistribution
    (hX : IsPositiveRecurrentMarkovChain P X) (x : E) :
    Kernel.Invariant (κ 1) (positiveRecurrentInvariantDistribution (κ := κ) x (hX x)) := by
  -- Route correction: use Theorem 17.47 for the owner excursion measure first, then transport
  -- that invariance through the normalization scalar.
  have hx : IsPositiveRecurrentState P X x := hX x
  have hrec : IsRecurrentState P X x :=
    positiveRecurrentState_isRecurrentState (P := P) (X := X) (κ := κ) x hx
  have hraw : Kernel.Invariant (κ 1) ((μ[P, X] x) : Measure E) :=
    recurrentState_returnCycleOccupationMeasure_comp_eq
      (κ := κ) (P := P) (X := X) hrec
  have hscaled :
      Kernel.Invariant (κ 1)
        ((expectedFirstReturnTime P X x)⁻¹ • (μ[P, X] x)) :=
    kernelInvariant_smul
      (κ := κ) (a := (expectedFirstReturnTime P X x)⁻¹) hraw
  simpa [positiveRecurrentInvariantDistribution] using hscaled

end

end ProbabilityTheory
