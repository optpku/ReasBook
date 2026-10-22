/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Theorem_20_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

local instance : MeasurableSpace (Stream' ℝ) :=
  inferInstanceAs (MeasurableSpace (ℕ → ℝ))

/-- Helper for Theorem 20.21: the one-sided shift on `Stream' ℝ` is measurable coordinatewise. -/
lemma measurableTailReal : Measurable (Stream'.tail : Stream' ℝ → Stream' ℝ) := by
  -- Proof comment: each output coordinate `i` is the input coordinate `i + 1`.
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i + 1)

/-- Helper for Theorem 20.21: the partial sums
`ω ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω` are measurable. -/
lemma measurablePartialSumEvalZero (n : ℕ) :
    Measurable (fun ω : ℕ → ℝ ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω) := by
  -- Proof comment: reuse the chapter owner for measurable Birkhoff sums on the path-space shift.
  simpa using
    measurable_birkhoffSum (τ := Stream'.tail) (g := Function.eval 0)
      measurableTailReal (measurable_pi_apply 0) n

/-- Helper for Theorem 20.21: the event that the partial sums tend to `+∞` is measurable and
invariant under the one-sided shift. -/
lemma isInvariantPartialSumAtTopEvent :
    is_invariant_event Stream'.tail {ω : ℕ → ℝ |
      Tendsto (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω) atTop atTop} := by
  change
    MeasurableSet {ω : ℕ → ℝ |
        Tendsto (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω) atTop atTop} ∧
      Stream'.tail ⁻¹' {ω : ℕ → ℝ |
          Tendsto (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω) atTop atTop} =
        {ω : ℕ → ℝ |
          Tendsto (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω) atTop atTop}
  refine ⟨measurableSet_tendsto atTop measurablePartialSumEvalZero, ?_⟩
  ext ω
  constructor
  · intro hω
    have hshiftEq :
        (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) (n + 1) ω) =
          fun n ↦ ω 0 + birkhoffSum Stream'.tail (Function.eval 0) n (Stream'.tail ω) := by
      funext n
      rw [birkhoffSum_succ']
    have htranslated :
        Tendsto
          (fun n ↦ ω 0 + birkhoffSum Stream'.tail (Function.eval 0) n (Stream'.tail ω))
          atTop atTop := by
      simpa using tendsto_atTop_add_const_left atTop (ω 0) hω
    rw [← hshiftEq] at htranslated
    exact (tendsto_add_atTop_iff_nat 1).1 htranslated
  · intro hω
    have hshiftEq :
        (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) (n + 1) ω) =
          fun n ↦ ω 0 + birkhoffSum Stream'.tail (Function.eval 0) n (Stream'.tail ω) := by
      funext n
      rw [birkhoffSum_succ']
    have hshift :
        Tendsto (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) (n + 1) ω) atTop atTop := by
      exact (tendsto_add_atTop_iff_nat 1).2 hω
    rw [hshiftEq] at hshift
    have htranslated := tendsto_atTop_add_const_left atTop (-ω 0) hshift
    simpa [add_assoc] using htranslated

/-- Helper for Theorem 20.21: a strictly positive limit of the Birkhoff averages forces the
corresponding partial sums to tend to `+∞`. -/
lemma positiveAverageEventually_forces_partialSumAtTop {ω : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hω :
      Tendsto
        (fun n ↦ birkhoffAverage ℝ Stream'.tail (Function.eval 0) n ω)
        atTop
        (𝓝 c)) :
    Tendsto
      (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
      atTop atTop := by
  have hc_half : 0 < c / 2 := by linarith
  have hω_shift :
      Tendsto
        (fun n ↦ birkhoffAverage ℝ Stream'.tail (Function.eval 0) (n + 1) ω)
        atTop
        (𝓝 c) :=
    (tendsto_add_atTop_iff_nat 1).2 hω
  have hEventually :
      ∀ᶠ n in atTop,
        c / 2 ≤ birkhoffAverage ℝ Stream'.tail (Function.eval 0) (n + 1) ω := by
    have hnhds : Set.Ici (c / 2) ∈ 𝓝 c := Ici_mem_nhds <| by linarith
    exact hω_shift hnhds
  have hLower :
      (fun n ↦ (((n + 1 : ℕ) : ℝ) * (c / 2))) ≤ᶠ[atTop]
        (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) (n + 1) ω) := by
    filter_upwards [hEventually] with n hn
    have hn0 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    calc
      (((n + 1 : ℕ) : ℝ) * (c / 2)) ≤
          ((n + 1 : ℕ) : ℝ) * birkhoffAverage ℝ Stream'.tail (Function.eval 0) (n + 1) ω := by
            gcongr
      _ = birkhoffSum Stream'.tail (Function.eval 0) (n + 1) ω := by
        rw [birkhoffAverage, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  have hLinear :
      Tendsto (fun n ↦ (((n + 1 : ℕ) : ℝ) * (c / 2))) atTop atTop := by
    exact ((tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop).atTop_mul_const hc_half
  have hShift :
      Tendsto
        (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) (n + 1) ω)
        atTop atTop :=
    tendsto_atTop_mono' atTop hLower hLinear
  exact (tendsto_add_atTop_iff_nat 1).1 hShift

/-- Helper for Theorem 20.21: the `k`-th barrier event asks every positive-time partial sum to
stay above `(1 : ℝ) / (k + 1)`. -/
def partialSumBarrierEvent (k : ℕ) : Set (ℕ → ℝ) :=
  {ω | ∀ n : ℕ, (1 : ℝ) / (k + 1) < birkhoffSum Stream'.tail (Function.eval 0) (n + 1) ω}

/-- Helper for Theorem 20.21: the barrier event is measurable because it is a countable
intersection of measurable strict half-spaces for the positive-time partial sums. -/
lemma measurableSet_partialSumBarrierEvent (k : ℕ) :
    MeasurableSet (partialSumBarrierEvent k) := by
  -- Proof comment: rewrite the barrier condition as one inequality for each positive time and
  -- intersect those measurable slices.
  suffices
      MeasurableSet
        (⋂ n : ℕ,
          {ω : ℕ → ℝ | (1 : ℝ) / (k + 1) <
            birkhoffSum Stream'.tail (Function.eval 0) (n + 1) ω}) by
    simpa [partialSumBarrierEvent, Set.setOf_forall]
  refine MeasurableSet.iInter fun n : ℕ ↦ ?_
  exact measurableSet_lt measurable_const (measurablePartialSumEvalZero (n + 1))

/-- Helper for Theorem 20.21: the barrier-event definition matches the source-style formulation
`∀ m ≥ 1, ε < S_m`. -/
lemma mem_partialSumBarrierEvent_iff {k : ℕ} {ω : ℕ → ℝ} :
    ω ∈ partialSumBarrierEvent k ↔
      ∀ m ≥ 1, (1 : ℝ) / (k + 1) < birkhoffSum Stream'.tail (Function.eval 0) m ω := by
  constructor
  · intro h m hm
    rcases Nat.exists_eq_add_of_le hm with ⟨n, rfl⟩
    simpa [Nat.add_assoc, Nat.add_comm] using h n
  · intro h n
    simpa using h (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Helper for Theorem 20.21: shifting by `j` subtracts the initial `j`-term partial sum from the
later orbit partial sums. -/
lemma partialSum_iterate_tail_eq_sub (j m : ℕ) (ω : ℕ → ℝ) :
    birkhoffSum Stream'.tail (Function.eval 0) m (Stream'.tail^[j] ω) =
      birkhoffSum Stream'.tail (Function.eval 0) (j + m) ω -
        birkhoffSum Stream'.tail (Function.eval 0) j ω := by
  -- Proof comment: split the long Birkhoff sum at time `j` and then move the initial block to the
  -- other side of the equality.
  have hsplit :
      birkhoffSum Stream'.tail (Function.eval 0) (j + m) ω =
        birkhoffSum Stream'.tail (Function.eval 0) j ω +
          birkhoffSum Stream'.tail (Function.eval 0) m (Stream'.tail^[j] ω) :=
    birkhoffSum_add Stream'.tail (Function.eval 0) j m ω
  have hsub :=
    congrArg
      (fun t : ℝ ↦ t - birkhoffSum Stream'.tail (Function.eval 0) j ω)
      hsplit
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub.symm

/-- Helper for Theorem 20.21: the barrier-event indicator is integrable on the probability path
space. -/
lemma integrable_partialSumBarrierIndicator
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (k : ℕ) :
    Integrable ((partialSumBarrierEvent k).indicator (fun _ : ℕ → ℝ ↦ (1 : ℝ))) P := by
  -- Proof comment: on a probability space the indicator is bounded by the integrable constant `1`.
  exact (integrable_const (1 : ℝ)).indicator (measurableSet_partialSumBarrierEvent k)

/-- Helper for Theorem 20.21: the barrier-visit times before `n` are the indices `i < n` whose
shifted path lies in the `k`-th barrier event. -/
noncomputable def partialSumBarrierVisitTimes (k n : ℕ) (ω : ℕ → ℝ) : Finset ℕ :=
  @Finset.filter ℕ (fun i => Stream'.tail^[i] ω ∈ partialSumBarrierEvent k)
    (Classical.decPred _) (Finset.range n)

/-- Helper for Theorem 20.21: among the first `N + 1` partial sums, there is a last index where
the prefix minimum is attained. -/
lemma existsLastPrefixMinimum (S : ℕ → ℝ) (N : ℕ) :
    ∃ j ≤ N, (∀ i ≤ N, S j ≤ S i) ∧ ∀ ⦃i : ℕ⦄, j < i → i ≤ N → S j < S i := by
  classical
  -- Route correction: choose the maximal index among all minimizers of the finite prefix so the
  -- required strict inequality at later prefix indices is built into the witness.
  let p : ℕ → Prop := fun j ↦ ∀ i ∈ Finset.range (N + 1), S j ≤ S i
  letI : DecidablePred p := Classical.decPred p
  let minimizers : Finset ℕ :=
    (Finset.range (N + 1)).filter p
  have hminimizers_ne : minimizers.Nonempty := by
    obtain ⟨j, hj_mem, hj_min⟩ :=
      Finset.exists_min_image (Finset.range (N + 1)) S ⟨0, by simp⟩
    refine ⟨j, ?_⟩
    refine Finset.mem_filter.mpr ⟨hj_mem, ?_⟩
    intro i hi
    exact hj_min i hi
  let j : ℕ := minimizers.max' hminimizers_ne
  have hj_mem : j ∈ minimizers := Finset.max'_mem minimizers hminimizers_ne
  have hj_prop : ∀ i ∈ Finset.range (N + 1), S j ≤ S i := (Finset.mem_filter.mp hj_mem).2
  have hjN : j ≤ N := by
    exact Nat.lt_succ_iff.mp (by simpa [minimizers, p] using (Finset.mem_filter.mp hj_mem).1)
  refine ⟨j, hjN, ?_⟩
  constructor
  · intro i hiN
    exact hj_prop i (by simpa using Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hiN))
  · intro i hji hiN
    have hle : S j ≤ S i := by
      exact hj_prop i (by simpa using Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hiN))
    by_cases hEq : S j = S i
    · have hi_prefix : i ∈ Finset.range (N + 1) := by
        simpa using Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hiN)
      have hi_mem : i ∈ minimizers := by
        refine Finset.mem_filter.mpr ⟨hi_prefix, ?_⟩
        intro m hm
        calc
          S i = S j := hEq.symm
          _ ≤ S m := hj_prop m hm
      have hi_le_j : i ≤ j := Finset.le_max' minimizers i hi_mem
      exact (not_le_of_gt hji hi_le_j).elim
    · exact lt_of_le_of_ne hle hEq

/-- Helper for Theorem 20.21: the last prefix minimum and an eventually positive tail produce a
rational barrier event after the corresponding shift. -/
lemma lastPrefixMinimumHasBarrierIndex {ω : ℕ → ℝ} {N j : ℕ}
    (_hjN : j ≤ N)
    (hmin :
      ∀ i ≤ N,
        birkhoffSum Stream'.tail (Function.eval 0) j ω ≤
          birkhoffSum Stream'.tail (Function.eval 0) i ω)
    (hstrict :
      ∀ ⦃i : ℕ⦄,
        j < i → i ≤ N →
          birkhoffSum Stream'.tail (Function.eval 0) j ω <
            birkhoffSum Stream'.tail (Function.eval 0) i ω)
    (hTail :
      ∀ n ≥ N,
        1 ≤ birkhoffSum Stream'.tail (Function.eval 0) n ω) :
    ∃ k : ℕ, Stream'.tail^[j] ω ∈ partialSumBarrierEvent k := by
  let S : ℕ → ℝ := fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω
  have hS0 : S 0 = 0 := by
    simp [S, birkhoffSum]
  have hSj_nonpos : S j ≤ 0 := by
    have hj0 : S j ≤ S 0 := hmin 0 (Nat.zero_le N)
    simpa [hS0] using hj0
  by_cases hExists : ∃ i : ℕ, j < i ∧ i ≤ N
  · classical
    -- Route correction: isolate the finite positive gaps above the last minimum and choose the
    -- barrier from their minimum before rewriting shifted partial sums.
    obtain ⟨i₀, hj_i₀, hi₀N⟩ := hExists
    let active : Finset ℕ := Finset.Icc (j + 1) N
    have hactive_ne : active.Nonempty := by
      refine ⟨i₀, ?_⟩
      simp [active, Nat.succ_le_of_lt hj_i₀, hi₀N]
    obtain ⟨iMin, hiMin_mem, hiMin_min⟩ :=
      Finset.exists_min_image active (fun i ↦ S i - S j) hactive_ne
    have hiMin_gt : j < iMin := by
      exact lt_of_lt_of_le (Nat.lt_succ_self j) (Finset.mem_Icc.mp hiMin_mem).1
    have hiMinN : iMin ≤ N := (Finset.mem_Icc.mp hiMin_mem).2
    have hgap_pos : 0 < S iMin - S j := by
      have hstrict_pos : S j < S iMin := hstrict hiMin_gt hiMinN
      linarith
    let δ : ℝ := min 1 (S iMin - S j)
    have hδpos : 0 < δ := by
      dsimp [δ]
      positivity
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδpos
    refine ⟨k, (mem_partialSumBarrierEvent_iff).2 ?_⟩
    intro m hm
    have hm_pos : 0 < m := Nat.succ_le_iff.mp hm
    have hshift :
        birkhoffSum Stream'.tail (Function.eval 0) m (Stream'.tail^[j] ω) =
          S (j + m) - S j := by
      simpa [S] using partialSum_iterate_tail_eq_sub j m ω
    by_cases hmN : j + m ≤ N
    · -- Proof comment: inside the finite prefix, the chosen gap minimum controls all shifted sums.
      have hjm_mem : j + m ∈ active := by
        simp [active, hmN, Nat.succ_le_iff.mpr hm_pos]
      have hgap_lower : S iMin - S j ≤ S (j + m) - S j := hiMin_min (j + m) hjm_mem
      have hδ_le_gap : δ ≤ S (j + m) - S j := by
        exact le_trans (min_le_right 1 (S iMin - S j)) hgap_lower
      rw [hshift]
      exact lt_of_lt_of_le hk hδ_le_gap
    · -- Proof comment: once the time lies past `N`, eventual positivity and `S j ≤ 0` give a
      -- uniform lower bound by `1`.
      have htail : 1 ≤ S (j + m) := hTail (j + m) (le_of_not_ge hmN)
      have hgap_one : 1 ≤ S (j + m) - S j := by
        linarith
      have hδ_le_one : δ ≤ 1 := min_le_left 1 (S iMin - S j)
      rw [hshift]
      exact lt_of_lt_of_le hk (le_trans hδ_le_one hgap_one)
  · -- Proof comment: if there is no later prefix index, then `j = N`, so every positive-time
    -- shifted sum is already in the eventual tail and stays above the fixed barrier `1/2`.
    refine ⟨1, (mem_partialSumBarrierEvent_iff).2 ?_⟩
    intro m hm
    have hm_pos : 0 < m := Nat.succ_le_iff.mp hm
    have hm_tail : ¬ j + m ≤ N := by
      intro hmN
      exact hExists ⟨j + m, by omega, hmN⟩
    have hshift :
        birkhoffSum Stream'.tail (Function.eval 0) m (Stream'.tail^[j] ω) =
          S (j + m) - S j := by
      simpa [S] using partialSum_iterate_tail_eq_sub j m ω
    have htail : 1 ≤ S (j + m) := hTail (j + m) (le_of_not_ge hm_tail)
    have hgap_one : 1 ≤ S (j + m) - S j := by
      linarith
    rw [hshift]
    have hhalf : (1 : ℝ) / ((1 : ℕ) + 1) < 1 := by
      norm_num
    exact lt_of_lt_of_le hhalf hgap_one

/-- Helper for Theorem 20.21: along a path whose partial sums tend to `+∞`, some shift of the
path enters a rational barrier event. -/
lemma existsShiftPositiveBarrierOfPartialSumAtTop {ω : ℕ → ℝ}
    (hω :
      Tendsto
        (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
        atTop atTop) :
    ∃ j k : ℕ, Stream'.tail^[j] ω ∈ partialSumBarrierEvent k := by
  let S : ℕ → ℝ := fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω
  have hEventually : ∀ᶠ n in atTop, 1 ≤ S n := by
    simpa [S] using (tendsto_atTop.1 hω) (1 : ℝ)
  rcases Filter.mem_atTop_sets.mp hEventually with ⟨N, hN⟩
  obtain ⟨j, hjN, hmin, hstrict⟩ := existsLastPrefixMinimum S N
  have hTail : ∀ n ≥ N, 1 ≤ S n := by
    intro n hn
    exact hN n hn
  rcases lastPrefixMinimumHasBarrierIndex (ω := ω) hjN
      (by simpa [S] using hmin)
      (by simpa [S] using hstrict)
      (by simpa [S] using hTail) with ⟨k, hk⟩
  exact ⟨j, k, hk⟩

/-- Helper for Theorem 20.21: almost-sure divergence of the partial sums yields a barrier event of
strictly positive probability. -/
lemma exists_posMeasure_positiveBarrierEvent
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (hP : Ergodic Stream'.tail P)
    (hAe :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
          atTop atTop) :
    ∃ k : ℕ, 0 < P (partialSumBarrierEvent k) := by
  let A : Set (ℕ → ℝ) := {ω |
    Tendsto
      (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
      atTop atTop}
  let E : ℕ × ℕ → Set (ℕ → ℝ) := fun p ↦ (Stream'.tail^[p.1]) ⁻¹' partialSumBarrierEvent p.2
  have hcover : A ⊆ ⋃ p : ℕ × ℕ, E p := by
    intro ω hω
    rcases existsShiftPositiveBarrierOfPartialSumAtTop hω with ⟨j, k, hjk⟩
    refine Set.mem_iUnion.mpr ⟨(j, k), ?_⟩
    simpa [E]
  have hAae : A =ᵐ[P] Set.univ := by
    simpa [A] using hAe
  have hAone : P A = 1 := by
    simpa using measure_congr hAae
  have hUnionPos : 0 < P (⋃ p : ℕ × ℕ, E p) := by
    calc
      0 < P A := by simp [hAone]
      _ ≤ P (⋃ p : ℕ × ℕ, E p) := measure_mono hcover
  obtain ⟨p, hp⟩ :
      ∃ p : ℕ × ℕ, 0 < P (E p) :=
    MeasureTheory.exists_measure_pos_of_not_measure_iUnion_null (ne_of_gt hUnionPos)
  refine ⟨p.2, ?_⟩
  have hpreimage :
      P (E p) = P (partialSumBarrierEvent p.2) := by
    simpa [E] using
      (hP.toMeasurePreserving.iterate p.1).measure_preimage
        (measurableSet_partialSumBarrierEvent p.2).nullMeasurableSet
  rwa [hpreimage] at hp

/-- Helper for Theorem 20.21: the Birkhoff sum of the barrier indicator counts barrier visits. -/
lemma birkhoffSum_partialSumBarrierIndicator_eq_card (k n : ℕ) (ω : ℕ → ℝ) :
    birkhoffSum Stream'.tail ((partialSumBarrierEvent k).indicator (fun _ : ℕ → ℝ ↦ (1 : ℝ))) n ω =
      (partialSumBarrierVisitTimes k n ω).card := by
  classical
  -- Proof comment: unfold the Birkhoff sum into a finite `0`/`1` sum and identify it with the
  -- filtered range cardinality of barrier-visit times.
  rw [birkhoffSum]
  simp only [Set.indicator_apply]
  rw [Finset.sum_boole]
  rfl

/-- Helper for Theorem 20.21: every barrier visit contributes one more uniform barrier increment
to every later partial sum. -/
lemma partialSumLowerBoundOfPositiveBarrierVisits {ω : ℕ → ℝ} {L : ℝ} {k n : ℕ}
    (hL :
      ∀ m : ℕ,
        L ≤ birkhoffSum Stream'.tail (Function.eval 0) m ω) :
    L + (1 : ℝ) / (k + 1) * (partialSumBarrierVisitTimes k n ω).card ≤
      birkhoffSum Stream'.tail (Function.eval 0) n ω := by
  classical
  let ε : ℝ := (1 : ℝ) / (k + 1)
  let S : ℕ → ℝ := fun m ↦ birkhoffSum Stream'.tail (Function.eval 0) m ω
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  -- Route correction: recurse on the maximal barrier visit before `n`, so the counting step is
  -- a single card decomposition plus one barrier increment.
  induction n using Nat.strong_induction_on with
  | h n ih =>
  by_cases hVisits : (partialSumBarrierVisitTimes k n ω).Nonempty
  · let visits : Finset ℕ := partialSumBarrierVisitTimes k n ω
    let i : ℕ := visits.max' hVisits
    have hi_mem : i ∈ visits := Finset.max'_mem visits hVisits
    have hi_props : i < n ∧ Stream'.tail^[i] ω ∈ partialSumBarrierEvent k := by
      simpa [visits, partialSumBarrierVisitTimes] using hi_mem
    have hi_lt_n : i < n := hi_props.1
    have hi_barrier : Stream'.tail^[i] ω ∈ partialSumBarrierEvent k := hi_props.2
    have hprev_eq : partialSumBarrierVisitTimes k i ω = visits.erase i := by
      ext j
      constructor
      · intro hj
        have hj_props : j < i ∧ Stream'.tail^[j] ω ∈ partialSumBarrierEvent k := by
          simpa [partialSumBarrierVisitTimes] using hj
        have hj_lt_n : j < n := lt_trans hj_props.1 hi_lt_n
        have hj_ne : j ≠ i := Nat.ne_of_lt hj_props.1
        simp [visits, partialSumBarrierVisitTimes, hj_lt_n, hj_props.2, hj_ne]
      · intro hj
        rcases Finset.mem_erase.mp hj with ⟨hj_ne, hj_mem_visits⟩
        have hj_props : j < n ∧ Stream'.tail^[j] ω ∈ partialSumBarrierEvent k := by
          simpa [visits, partialSumBarrierVisitTimes] using hj_mem_visits
        have hj_le_i : j ≤ i := Finset.le_max' visits j hj_mem_visits
        have hj_lt_i : j < i := lt_of_le_of_ne hj_le_i hj_ne
        simp [partialSumBarrierVisitTimes, hj_lt_i, hj_props.2]
    have hcard_nat :
        (partialSumBarrierVisitTimes k n ω).card =
          (partialSumBarrierVisitTimes k i ω).card + 1 := by
      calc
        visits.card = (visits.erase i).card + 1 := (Finset.card_erase_add_one hi_mem).symm
        _ = (partialSumBarrierVisitTimes k i ω).card + 1 := by rw [← hprev_eq]
    have hcard_real :
        ((partialSumBarrierVisitTimes k n ω).card : ℝ) =
          ((partialSumBarrierVisitTimes k i ω).card : ℝ) + 1 := by
      rw [hcard_nat, Nat.cast_add, Nat.cast_one]
    have hih :
        L + ε * (partialSumBarrierVisitTimes k i ω).card ≤ S i := by
      simpa [S, ε] using ih i hi_lt_n
    have hi_barrier' := (mem_partialSumBarrierEvent_iff).1 hi_barrier
    have hni : 1 ≤ n - i := by
      omega
    have hgap_shift :
        ε <
          birkhoffSum Stream'.tail (Function.eval 0) (n - i) (Stream'.tail^[i] ω) := by
      simpa [ε] using hi_barrier' (n - i) hni
    have hshift :
        birkhoffSum Stream'.tail (Function.eval 0) (n - i) (Stream'.tail^[i] ω) =
          S n - S i := by
      simpa [S, Nat.add_sub_of_le hi_lt_n.le] using partialSum_iterate_tail_eq_sub i (n - i) ω
    have hgap : ε < S n - S i := by
      rw [← hshift]
      exact hgap_shift
    rw [hcard_real]
    have hstep :
        L + ε * (((partialSumBarrierVisitTimes k i ω).card : ℝ) + 1) < S n := by
      calc
        L + ε * (((partialSumBarrierVisitTimes k i ω).card : ℝ) + 1)
            = (L + ε * (partialSumBarrierVisitTimes k i ω).card) + ε := by ring
        _ ≤ S i + ε := by gcongr
        _ < S n := by linarith
    exact le_of_lt hstep
  · have hEmpty : partialSumBarrierVisitTimes k n ω = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hVisits
    -- Proof comment: if there is no barrier visit before `n`, the estimate reduces to the global
    -- lower bound `L ≤ S n`.
    rw [hEmpty, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero]
    simpa [S] using hL n

/-- Helper for Theorem 20.21: dividing the visit-count inequality by `n + 1` turns it into a
comparison between the barrier-indicator average and the original partial-sum average. -/
lemma scaledBarrierVisitAverage_le_partialSumAverage {ω : ℕ → ℝ} {L : ℝ} {k n : ℕ}
    (hL :
      ∀ m : ℕ,
        L ≤ birkhoffSum Stream'.tail (Function.eval 0) m ω) :
    (((n + 1 : ℕ) : ℝ)⁻¹ * L) +
        (1 : ℝ) / (k + 1) *
          birkhoffAverage ℝ Stream'.tail
            ((partialSumBarrierEvent k).indicator (fun _ : ℕ → ℝ ↦ (1 : ℝ))) (n + 1) ω ≤
      birkhoffAverage ℝ Stream'.tail (Function.eval 0) (n + 1) ω := by
  let m : ℕ := n + 1
  let ε : ℝ := (1 : ℝ) / (k + 1)
  have hm0 : ((m : ℕ) : ℝ) ≠ 0 := by
    dsimp [m]
    positivity
  have hscaled :
      (m : ℝ)⁻¹ *
          (L + ε * (partialSumBarrierVisitTimes k m ω).card) ≤
        (m : ℝ)⁻¹ * birkhoffSum Stream'.tail (Function.eval 0) m ω := by
    have hcount :=
      partialSumLowerBoundOfPositiveBarrierVisits
        (ω := ω) (L := L) (k := k) (n := m) hL
    exact mul_le_mul_of_nonneg_left hcount (by positivity)
  -- Proof comment: rewrite both sides into `birkhoffAverage` normal form only once.
  have hleft :
      (m : ℝ)⁻¹ * (L + ε * (partialSumBarrierVisitTimes k m ω).card) =
        ((m : ℝ)⁻¹ * L) +
          ε *
            birkhoffAverage ℝ Stream'.tail
              ((partialSumBarrierEvent k).indicator (fun _ : ℕ → ℝ ↦ (1 : ℝ))) m ω := by
    rw [birkhoffAverage, smul_eq_mul, birkhoffSum_partialSumBarrierIndicator_eq_card]
    ring
  have hright :
      (m : ℝ)⁻¹ * birkhoffSum Stream'.tail (Function.eval 0) m ω =
        birkhoffAverage ℝ Stream'.tail (Function.eval 0) m ω := by
    rw [birkhoffAverage, smul_eq_mul]
  rw [hleft, hright] at hscaled
  simpa [m, ε] using hscaled

/-- Helper for Theorem 20.21: almost-sure divergence of the partial sums forces a strictly positive
expectation of the first-coordinate observable. -/
lemma expectation_pos_of_partialSumAtTop_ae
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (hP : Ergodic Stream'.tail P)
    (h_int : Integrable (Function.eval 0) P)
    (hAe :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
          atTop atTop) :
    0 < P[Function.eval 0] := by
  obtain ⟨k, hkPos⟩ := exists_posMeasure_positiveBarrierEvent P hP hAe
  let ε : ℝ := (1 : ℝ) / (k + 1)
  let g : (ℕ → ℝ) → ℝ := (partialSumBarrierEvent k).indicator (fun _ : ℕ → ℝ ↦ (1 : ℝ))
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hg_int : Integrable g P := by
    simpa [g] using integrable_partialSumBarrierIndicator P k
  have hAverageEval :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n ↦ birkhoffAverage ℝ Stream'.tail (Function.eval 0) n ω)
          atTop
          (𝓝 (P[Function.eval 0])) :=
    birkhoffAverage_tendsto_ae_expectation_of_ergodic
      (P := P) (τ := Stream'.tail) (f := Function.eval 0) hP h_int
  have hAverageBarrier :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n ↦ birkhoffAverage ℝ Stream'.tail g n ω)
          atTop
          (𝓝 (P[g])) :=
    birkhoffAverage_tendsto_ae_expectation_of_ergodic
      (P := P) (τ := Stream'.tail) (f := g) hP hg_int
  have hgExpectation : P[g] = P.real (partialSumBarrierEvent k) := by
    -- Proof comment: the expectation of the barrier indicator is the real-valued probability of
    -- the barrier event.
    simpa [g] using
      (integral_indicator_one (μ := P) (s := partialSumBarrierEvent k)
        (measurableSet_partialSumBarrierEvent k))
  have hgPos : 0 < P[g] := by
    rw [hgExpectation]
    exact ENNReal.toReal_pos (ne_of_gt hkPos) (measure_ne_top P _)
  have hLowerAe : ∀ᵐ ω ∂P, ε * P[g] ≤ P[Function.eval 0] := by
    filter_upwards [hAe, hAverageEval, hAverageBarrier] with ω hDiv hEval hBarrier
    let S : ℕ → ℝ := fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω
    have hEventuallyNonneg : ∀ᶠ n in atTop, 0 ≤ S n := by
      simpa [S] using (tendsto_atTop.1 hDiv) (0 : ℝ)
    rcases Filter.mem_atTop_sets.mp hEventuallyNonneg with ⟨N, hN⟩
    obtain ⟨j, hjmem, hjmin⟩ := Finset.exists_min_image (Finset.range (N + 1)) S
      ⟨0, by simp⟩
    have hLower :
        ∀ m : ℕ, S j ≤ S m := by
      intro m
      by_cases hm : m ≤ N
      · exact hjmin m <| by simp [hm]
      · have hj0 : S j ≤ S 0 := hjmin 0 <| by simp
        have hmNonneg : 0 ≤ S m := hN m (Nat.le_of_lt (Nat.lt_of_not_ge hm))
        have hjNonpos : S j ≤ 0 := by simpa [S] using hj0
        linarith
    have hBarrierShift :
        Tendsto
          (fun n ↦ birkhoffAverage ℝ Stream'.tail g (n + 1) ω)
          atTop
          (𝓝 (P[g])) :=
      (tendsto_add_atTop_iff_nat 1).2 hBarrier
    have hDecay :
        Tendsto
          (fun n ↦ (((n + 1 : ℕ) : ℝ)⁻¹ * S j))
          atTop
          (𝓝 (0 : ℝ)) := by
      have hInv :
          Tendsto
            (fun n ↦ (((n + 1 : ℕ) : ℝ)⁻¹))
            atTop
            (𝓝 (0 : ℝ)) := by
        exact (((tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop)).inv_tendsto_atTop
      simpa using hInv.mul tendsto_const_nhds
    have hScaledBarrier :
        Tendsto
          (fun n ↦ ε * birkhoffAverage ℝ Stream'.tail g (n + 1) ω)
          atTop
          (𝓝 (ε * P[g])) := by
      simpa [ε] using tendsto_const_nhds.mul hBarrierShift
    have hEvalShift :
        Tendsto
          (fun n ↦ birkhoffAverage ℝ Stream'.tail (Function.eval 0) (n + 1) ω)
          atTop
          (𝓝 (P[Function.eval 0])) :=
      (tendsto_add_atTop_iff_nat 1).2 hEval
    have hLeft :
        Tendsto
          (fun n ↦ (((n + 1 : ℕ) : ℝ)⁻¹ * S j) +
            ε * birkhoffAverage ℝ Stream'.tail g (n + 1) ω)
          atTop
          (𝓝 (ε * P[g])) := by
      simpa using hDecay.add hScaledBarrier
    -- Proof comment: compare the two convergent shifted averages through the pointwise lower bound
    -- supplied by the barrier-visit estimate.
    exact le_of_tendsto_of_tendsto' hLeft hEvalShift fun n ↦
      scaledBarrierVisitAverage_le_partialSumAverage
        (ω := ω) (L := S j) (k := k) (n := n) (by simpa [S] using hLower)
  have hBound : ε * P[g] ≤ P[Function.eval 0] := by
    by_contra hlt
    have hFalse : ∀ᵐ ω ∂P, False := hLowerAe.mono fun _ hω => hlt hω
    have hUnivZero : P Set.univ = 0 := by
      simp [ae_iff] at hFalse
    have hUnivOne : P Set.univ = 1 := by
      simp
    rw [hUnivZero] at hUnivOne
    norm_num at hUnivOne
  have hPos : 0 < ε * P[g] := by
    nlinarith
  exact lt_of_lt_of_le hPos hBound

-- Proof sketch: apply the canonical ergodic-theory owners on path space. The relevant partial
-- sums are the Birkhoff sums of the first-coordinate observable `ω ↦ ω 0` along the one-sided
-- shift `Stream'.tail`, and the normalized partial sums are the corresponding Birkhoff averages.
-- The divergence event is shift-invariant, so ergodicity upgrades positive probability to almost
-- sure occurrence. The linear-drift clause is the almost-sure convergence of the Birkhoff
-- averages to the expectation of the first coordinate.
/-- Theorem 20.21: for an integrable ergodic process on the path space `ℕ → ℝ`, the following are
equivalent: the Birkhoff sums of the first coordinate along the one-sided shift tend to `+∞`
almost surely; the same event has positive probability; and the corresponding Birkhoff averages
converge almost surely to the positive expectation of the first coordinate. -/
theorem ergodic_process_partial_sum_tendsto_atTop_tfae
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (hP : Ergodic Stream'.tail P)
    (h_int : Integrable (Function.eval 0) P) :
    List.TFAE
      [ ∀ᵐ ω ∂P,
          Tendsto
            (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
            atTop atTop
      , 0 < P {ω |
          Tendsto
            (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
            atTop atTop}
      , 0 < P[Function.eval 0] ∧
          ∀ᵐ ω ∂P,
            Tendsto
              (fun n ↦ birkhoffAverage ℝ Stream'.tail (Function.eval 0) n ω)
              atTop
              (𝓝 (P[Function.eval 0]))
      ] := by
  let A : Set (ℕ → ℝ) := {ω |
    Tendsto
      (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
      atTop atTop}
  have hAinv : is_invariant_event Stream'.tail A := by
    -- Package the divergence event once so the zero-one step can use it directly.
    simpa [A] using isInvariantPartialSumAtTopEvent
  have hAmeas : MeasurableSet A := hAinv.1
  have hAverageAe :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n ↦ birkhoffAverage ℝ Stream'.tail (Function.eval 0) n ω)
          atTop
          (𝓝 (P[Function.eval 0])) :=
    birkhoffAverage_tendsto_ae_expectation_of_ergodic
      (P := P) (τ := Stream'.tail) (f := Function.eval 0) hP h_int
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hAe
      -- Almost-sure occurrence upgrades the event measure to `1`, hence to positivity.
      have hAuniv : A =ᵐ[P] Set.univ := by
        simpa [A] using hAe
      have hPA : P A = 1 := by
        simpa using measure_congr hAuniv
      simp [A, hPA]
    · intro hPApos
      -- Ergodicity turns positive measure of the invariant event into almost-sure occurrence.
      rcases hP.toPreErgodic.ae_empty_or_univ hAmeas hAinv.2 with hAempty | hAuniv
      · have hPA0 : P A = 0 := by
          simpa using measure_congr hAempty
        exfalso
        simp [A, hPA0] at hPApos
      · simpa [A] using hAuniv
  tfae_have 3 → 1 := by
    rintro ⟨hExpectationPos, hAverage⟩
    -- A positive almost-sure average limit yields linear growth of the partial sums pathwise.
    filter_upwards [hAverage] with ω hω
    exact positiveAverageEventually_forces_partialSumAtTop hExpectationPos hω
  tfae_have 1 → 3 := by
    intro hAe
    -- The average limit comes from the earlier ergodic theorem; only strict positivity remains.
    refine ⟨expectation_pos_of_partialSumAtTop_ae P hP h_int hAe, hAverageAe⟩
  tfae_finish
