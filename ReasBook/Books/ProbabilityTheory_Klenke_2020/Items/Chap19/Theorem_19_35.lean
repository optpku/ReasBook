/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Example_20_26
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Remark_20_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Remark_20_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Theorem_20_14
import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/- Layering for Theorem 19.35:
- `source-facing`: a sampled one-dimensional environment `W : Ω → RandomEnvironment`, the site
  law of the logarithmic Solomon ratios `log ρ_x`, and the quenched almost-sure drift/oscillation
  conclusions for the walk in the realized environment `W ω`.
- `core/canonical`: for each fixed environment sample `ω`, the Chapter 19 owner
  `W ω .IsElliptic` together with `IsMarkovProcessRealization
    (fun n ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix (W ω)) ^ n)`.
- `bridge/view`: the almost-sure Solomon series regimes `R⁻[W ω]`, `R⁺[W ω]` from
  `Theorem_19_33`, obtained from the sign of `∫ log ρ₀`. -/

/-- The logarithmic local Solomon ratio `log ρ_x` of the sampled environment `W ω`. This is the
real-valued source quantity that appears in Solomon's criterion. -/
def randomEnvironmentLogRatio (W : Ω → RandomEnvironment) (x : ℤ) : Ω → ℝ :=
  fun ω ↦
    Real.log
      (((((1 : ℝ≥0) - ((W ω).rightJumpProb x)) / ((W ω).rightJumpProb x) : ℝ≥0) : ℝ))

scoped[ProbabilityTheory] notation "logρ[" W "](" x ")" => randomEnvironmentLogRatio W x

/-- A Solomon environment law is a random nearest-neighbor environment on `ℤ` whose log-ratio
field is i.i.d. and whose sampled environments are almost surely elliptic. This is the
source-facing environment-law owner for Theorem 19.35; the walk itself remains organized by the
canonical fixed-environment owner from Definition 19.34. -/
class IsSolomonEnvironmentLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → RandomEnvironment) : Prop where
  ae_elliptic : ∀ᵐ ω ∂μ, (W ω).IsElliptic
  logRatio_iid : IsIID (fun x ↦ logρ[W](x)) μ

namespace IsSolomonEnvironmentLaw

variable {W : Ω → RandomEnvironment}

/-- In a Solomon environment law, the sampled environment is elliptic almost surely. -/
theorem ae_elliptic_at (hW : IsSolomonEnvironmentLaw μ W) (x : ℤ) :
    ∀ᵐ ω ∂μ, 0 < (W ω).rightJumpProb x ∧ (W ω).rightJumpProb x < 1 :=
  hW.ae_elliptic.mono fun _ hω ↦ hω.pos_lt_one x

/-- In a Solomon environment law, all sitewise log-ratios have the same distribution. -/
theorem identDistrib_logRatio (hW : IsSolomonEnvironmentLaw μ W) (x y : ℤ) :
    IdentDistrib (logρ[W](x)) (logρ[W](y)) μ μ :=
  hW.logRatio_iid.identDistrib x y

end IsSolomonEnvironmentLaw

/-- Helper for Theorem 19.35: identify the path-space measurable structure on `Stream' ℝ` with
the product measurable structure on `ℕ → ℝ`. -/
local instance : MeasurableSpace (Stream' ℝ) :=
  inferInstanceAs (MeasurableSpace (ℕ → ℝ))

/-- Helper for Theorem 19.35: the one-sided shift on `Stream' ℝ` is measurable coordinatewise. -/
private lemma measurableTailReal : Measurable (Stream'.tail : Stream' ℝ → Stream' ℝ) := by
  -- Proof comment: each output coordinate `i` is the input coordinate `i + 1`.
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i + 1)

/-- Helper for Theorem 19.35: the one-sided path-space partial sums
`ω ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω` are measurable. -/
private lemma measurablePartialSumEvalZero (n : ℕ) :
    Measurable (fun ω : ℕ → ℝ ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω) := by
  -- Proof comment: reuse the Chapter 20 owner for measurable Birkhoff sums on the shift path
  -- space.
  simpa using
    measurable_birkhoffSum (τ := Stream'.tail) (X₀ := Function.eval 0)
      measurableTailReal (measurable_pi_apply 0) n

/-- Helper for Theorem 19.35: the `k`-th barrier event asks every positive-time path-space partial
sum to stay above `(1 : ℝ) / (k + 1)`. -/
private def partialSumBarrierEvent (k : ℕ) : Set (ℕ → ℝ) :=
  {ω | ∀ n : ℕ, (1 : ℝ) / (k + 1) < birkhoffSum Stream'.tail (Function.eval 0) (n + 1) ω}

/-- Helper for Theorem 19.35: the barrier event is measurable because it is a countable
intersection of measurable strict half-spaces for the positive-time partial sums. -/
private lemma measurableSet_partialSumBarrierEvent (k : ℕ) :
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

/-- Helper for Theorem 19.35: the barrier-event definition matches the source-style formulation
`∀ m ≥ 1, ε < S_m`. -/
private lemma mem_partialSumBarrierEvent_iff {k : ℕ} {ω : ℕ → ℝ} :
    ω ∈ partialSumBarrierEvent k ↔
      ∀ m ≥ 1, (1 : ℝ) / (k + 1) < birkhoffSum Stream'.tail (Function.eval 0) m ω := by
  constructor
  · intro h m hm
    rcases Nat.exists_eq_add_of_le hm with ⟨n, rfl⟩
    simpa [Nat.add_assoc, Nat.add_comm] using h n
  · intro h n
    simpa using h (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Helper for Theorem 19.35: shifting by `j` subtracts the initial `j`-term partial sum from the
later path-space partial sums. -/
private lemma partialSum_iterate_tail_eq_sub (j m : ℕ) (ω : ℕ → ℝ) :
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

/-- Helper for Theorem 19.35: the barrier-event indicator is integrable on any probability path
space. -/
private lemma integrable_partialSumBarrierIndicator
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (k : ℕ) :
    Integrable ((partialSumBarrierEvent k).indicator (fun _ : ℕ → ℝ ↦ (1 : ℝ))) P := by
  -- Proof comment: on a probability space the indicator is bounded by the integrable constant
  -- `1`.
  exact (integrable_const (1 : ℝ)).indicator (measurableSet_partialSumBarrierEvent k)

/-- Helper for Theorem 19.35: among the first `N + 1` partial sums, there is a last index where
the prefix minimum is attained. -/
private lemma existsLastPrefixMinimum (S : ℕ → ℝ) (N : ℕ) :
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

/-- Helper for Theorem 19.35: the last prefix minimum and an eventually positive tail produce a
rational barrier event after the corresponding shift. -/
private lemma lastPrefixMinimumHasBarrierIndex {ω : ℕ → ℝ} {N j : ℕ}
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

/-- Helper for Theorem 19.35: along a path whose partial sums tend to `+∞`, some shift of the
path enters a rational barrier event. -/
private lemma existsShiftPositiveBarrierOfPartialSumAtTop {ω : ℕ → ℝ}
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

/-- Helper for Theorem 19.35: almost-sure divergence of the path-space partial sums yields a
barrier event of strictly positive probability. -/
private lemma exists_posMeasure_positiveBarrierEvent
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

/-- Helper for Theorem 19.35: the barrier visits before time `n` are the indices `i < n` whose
shifted path lies in the `k`-th barrier event. -/
private noncomputable def partialSumBarrierVisitTimes (k n : ℕ) (ω : ℕ → ℝ) : Finset ℕ :=
  @Finset.filter ℕ (fun i => Stream'.tail^[i] ω ∈ partialSumBarrierEvent k)
    (Classical.decPred _) (Finset.range n)

/-- Helper for Theorem 19.35: the Birkhoff sum of the barrier indicator counts barrier visits. -/
private lemma birkhoffSum_partialSumBarrierIndicator_eq_card (k n : ℕ) (ω : ℕ → ℝ) :
    birkhoffSum Stream'.tail ((partialSumBarrierEvent k).indicator (fun _ : ℕ → ℝ ↦ (1 : ℝ))) n ω =
      (partialSumBarrierVisitTimes k n ω).card := by
  classical
  -- Proof comment: unfold the Birkhoff sum into a finite `0`/`1` sum and identify it with the
  -- filtered range cardinality of barrier-visit times.
  rw [birkhoffSum]
  simp only [Set.indicator_apply]
  rw [Finset.sum_boole]
  rfl

/-- Helper for Theorem 19.35: every barrier visit contributes one more uniform barrier increment
to every later partial sum. -/
private lemma partialSumLowerBoundOfPositiveBarrierVisits {ω : ℕ → ℝ} {L : ℝ} {k n : ℕ}
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
        -- Proof comment: if there is no barrier visit before `n`, the estimate reduces to the
        -- global lower bound `L ≤ S n`.
        rw [hEmpty, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero]
        simpa [S] using hL n

/-- Helper for Theorem 19.35: dividing the visit-count inequality by `n + 1` turns it into a
comparison between the barrier-indicator average and the original partial-sum average. -/
private lemma scaledBarrierVisitAverage_le_partialSumAverage {ω : ℕ → ℝ} {L : ℝ} {k n : ℕ}
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

/-- Helper for Theorem 19.35: almost-sure divergence of the path-space partial sums forces a
strictly positive expectation of the first-coordinate observable. -/
private lemma expectation_pos_of_partialSumAtTop_ae
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
    have hFalse : ∀ᵐ ω ∂P, False := hLowerAe.mono fun _ hω ↦ hlt hω
    have hUnivZero : P Set.univ = 0 := by
      simp [ae_iff] at hFalse
    have hUnivOne : P Set.univ = 1 := by
      simp
    rw [hUnivZero] at hUnivOne
    norm_num at hUnivOne
  have hPos : 0 < ε * P[g] := by
    nlinarith
  exact lt_of_lt_of_le hPos hBound

section SeriesBridge

variable {W : Ω → RandomEnvironment}

/-- Helper for Theorem 19.35: in an elliptic sampled environment, each local Solomon ratio is the
`ENNReal.ofReal` image of the exponential of the corresponding logarithmic ratio. -/
private lemma randomEnvironmentRatio_eq_ofReal_exp_logRatio
    (W : Ω → RandomEnvironment) (ω : Ω) (hω : (W ω).IsElliptic) (x : ℤ) :
    ρ[W ω](x) = ENNReal.ofReal (Real.exp (logρ[W](x) ω)) := by
  have hp_pos : 0 < ((W ω).rightJumpProb x : ℝ) := by
    exact_mod_cast hω.pos x
  have hp_nonneg : 0 ≤ ((W ω).rightJumpProb x : ℝ) := le_of_lt hp_pos
  have hnum :
      ((1 : ℝ≥0∞) - (W ω).rightJumpProb x) =
        ENNReal.ofReal (1 - ((W ω).rightJumpProb x : ℝ)) := by
    have hnum' :
        ENNReal.ofReal (1 - ((W ω).rightJumpProb x : ℝ)) =
          ((1 : ℝ≥0∞) - (W ω).rightJumpProb x) := by
      rw [ENNReal.ofReal_sub (1 : ℝ) hp_nonneg, ENNReal.ofReal_one]
      simp
    exact hnum'.symm
  have hratio_pos :
      0 <
        (((((1 : ℝ≥0) - (W ω).rightJumpProb x) /
          (W ω).rightJumpProb x : ℝ≥0) : ℝ)) := by
    exact_mod_cast div_pos (tsub_pos_iff_lt.2 (hω.lt_one x)) (hω.pos x)
  have hreal_ratio :
      (1 - ((W ω).rightJumpProb x : ℝ)) / ((W ω).rightJumpProb x : ℝ) =
        (((((1 : ℝ≥0) - (W ω).rightJumpProb x) /
          (W ω).rightJumpProb x : ℝ≥0) : ℝ)) := by
    simp [NNReal.coe_div, NNReal.coe_sub, le_of_lt (hω.lt_one x)]
  -- Proof comment: unfold both sides to the same positive real ratio and finish with `exp_log`.
  calc
    ρ[W ω](x)
        = ENNReal.ofReal (1 - ((W ω).rightJumpProb x : ℝ)) /
            ENNReal.ofReal ((W ω).rightJumpProb x : ℝ) := by
              rw [randomEnvironmentRatio, hnum]
              simp
    _ = ENNReal.ofReal ((1 - ((W ω).rightJumpProb x : ℝ)) / ((W ω).rightJumpProb x : ℝ)) := by
          rw [ENNReal.ofReal_div_of_pos hp_pos]
    _ = ENNReal.ofReal
          (((((1 : ℝ≥0) - (W ω).rightJumpProb x) /
            (W ω).rightJumpProb x : ℝ≥0) : ℝ)) := by
          rw [hreal_ratio]
    _ = ENNReal.ofReal
          (Real.exp
            (Real.log
              (((((1 : ℝ≥0) - (W ω).rightJumpProb x) /
                (W ω).rightJumpProb x : ℝ≥0) : ℝ)))) := by
            rw [Real.exp_log hratio_pos]
    _ = ENNReal.ofReal (Real.exp (logρ[W](x) ω)) := by
          simp [randomEnvironmentLogRatio]

/-- Helper for Theorem 19.35: the reciprocal Solomon ratio on the reflected left ray is the
`ENNReal.ofReal` image of the exponential of the negated logarithmic ratio. -/
private lemma randomEnvironmentInvRatio_eq_ofReal_exp_negLogRatio
    (W : Ω → RandomEnvironment) (ω : Ω) (hω : (W ω).IsElliptic) (x : ℤ) :
    (ρ[W ω](x))⁻¹ = ENNReal.ofReal (Real.exp (-logρ[W](x) ω)) := by
  -- Proof comment: invert the exponential ratio normal form termwise and rewrite `exp (-a)`.
  calc
    (ρ[W ω](x))⁻¹
        = (ENNReal.ofReal (Real.exp (logρ[W](x) ω)))⁻¹ := by
            rw [randomEnvironmentRatio_eq_ofReal_exp_logRatio (W := W) ω hω x]
    _ = ENNReal.ofReal ((Real.exp (logρ[W](x) ω))⁻¹) := by
          rw [ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]
    _ = ENNReal.ofReal (Real.exp (-logρ[W](x) ω)) := by
          congr 1
          rw [(Real.exp_neg _).symm]

/-- Helper for Theorem 19.35: the `n`-th right Solomon product is the exponential of the right
log-ratio prefix sum. -/
private lemma randomEnvironmentRightSeriesTerm_eq_ofReal_exp_logPrefixSum
    (W : Ω → RandomEnvironment) (ω : Ω) (hω : (W ω).IsElliptic) (n : ℕ) :
    randomEnvironmentRightSeriesTerm (W ω) n =
      ENNReal.ofReal
        (Real.exp (Finset.sum (Finset.range (n + 1)) fun i : ℕ ↦ logρ[W](i) ω)) := by
  induction n with
  | zero =>
      -- Proof comment: the zeroth rightward product is exactly the first local ratio.
      simpa [randomEnvironmentRightSeriesTerm] using
        randomEnvironmentRatio_eq_ofReal_exp_logRatio (W := W) ω hω (0 : ℤ)
  | succ n ih =>
      have hsum :
          Finset.sum (Finset.range (n + 2)) (fun i : ℕ ↦ logρ[W](i) ω) =
            Finset.sum (Finset.range (n + 1)) (fun i : ℕ ↦ logρ[W](i) ω) +
              logρ[W](n + 1) ω := by
        simpa using (Finset.sum_range_succ (fun i : ℕ ↦ logρ[W](i) ω) (n + 1))
      have hexp :
          Real.exp (Finset.sum (Finset.range (n + 1)) (fun i : ℕ ↦ logρ[W](i) ω)) *
              Real.exp (logρ[W](n + 1) ω) =
            Real.exp (Finset.sum (Finset.range (n + 2)) (fun i : ℕ ↦ logρ[W](i) ω)) := by
        rw [← Real.exp_add]
        congr 1
        exact hsum.symm
      -- Proof comment: peel off the newest ratio factor and merge it into the exponential prefix.
      rw [randomEnvironmentRightSeriesTerm_succ, ih,
        randomEnvironmentRatio_eq_ofReal_exp_logRatio (W := W) ω hω (n + 1),
        ← ENNReal.ofReal_mul (by positivity), hexp]

/-- Helper for Theorem 19.35: the `n`-th left Solomon product is the exponential of the reflected
negative-ray log-ratio prefix sum. -/
private lemma randomEnvironmentLeftSeriesTerm_eq_ofReal_exp_reflectedNegLogPrefixSum
    (W : Ω → RandomEnvironment) (ω : Ω) (hω : (W ω).IsElliptic) (n : ℕ) :
    randomEnvironmentLeftSeriesTerm (W ω) n =
      ENNReal.ofReal
        (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ -logρ[W](-((i : ℤ) + 1)) ω)) := by
  induction n with
  | zero =>
      -- Proof comment: the empty leftward product is `1`, matching the empty exponential prefix.
      simp [randomEnvironmentLeftSeriesTerm]
  | succ n ih =>
      have hsum :
          Finset.sum (Finset.range (n + 1)) (fun i : ℕ ↦ -logρ[W](-((i : ℤ) + 1)) ω) =
            Finset.sum (Finset.range n) (fun i : ℕ ↦ -logρ[W](-((i : ℤ) + 1)) ω) +
              -logρ[W](-((n : ℤ) + 1)) ω := by
        simpa using
          (Finset.sum_range_succ (fun i : ℕ ↦ -logρ[W](-((i : ℤ) + 1)) ω) n)
      have hexp :
          Real.exp (Finset.sum (Finset.range n) (fun i : ℕ ↦ -logρ[W](-((i : ℤ) + 1)) ω)) *
              Real.exp (-logρ[W](-((n : ℤ) + 1)) ω) =
            Real.exp
              (Finset.sum (Finset.range (n + 1)) (fun i : ℕ ↦ -logρ[W](-((i : ℤ) + 1)) ω)) := by
        rw [← Real.exp_add]
        congr 1
        exact hsum.symm
      -- Proof comment: unfold one more reflected left factor and absorb it into the exponential
      -- normal form.
      rw [randomEnvironmentLeftSeriesTerm_succ, ih,
        randomEnvironmentInvRatio_eq_ofReal_exp_negLogRatio
          (W := W) ω hω (-((n : ℤ) + 1)),
        ← ENNReal.ofReal_mul (by positivity), hexp]

/-- Helper for Theorem 19.35: reindexing the `ℤ`-indexed log-ratio field to the reflected
negative ray and then negating each coordinate preserves the i.i.d. structure. -/
private lemma negReflectedLeftLogRatio_isIID
    (hW : IsSolomonEnvironmentLaw μ W) :
    IsIID (fun n : ℕ ↦ fun ω ↦ -logρ[W](-((n : ℤ) + 1)) ω) μ := by
  have hreflected :
      IsIID (fun n : ℕ ↦ fun ω ↦ logρ[W](-((n : ℤ) + 1)) ω) μ := by
    refine ⟨?_, ?_⟩
    · -- Proof comment: the reflected embedding `n ↦ -((n : ℤ) + 1)` is injective, so the
      -- reindexed field keeps independence.
      simpa using
        hW.logRatio_iid.iIndepFun.precomp
          (g := fun n : ℕ ↦ -((n : ℤ) + 1))
          (by
            intro a b h
            have h' : (a : ℤ) + 1 = (b : ℤ) + 1 := by
              simpa using congrArg Neg.neg h
            omega)
    · -- Proof comment: identical distribution is inherited from the ambient Solomon field after
      -- the same reflected reindexing on both coordinates.
      intro i j
      simpa using hW.identDistrib_logRatio (-((i : ℤ) + 1)) (-((j : ℤ) + 1))
  refine ⟨?_, ?_⟩
  · -- Proof comment: independence is stable under the same measurable negation on every
    -- reflected coordinate.
    simpa using
      hreflected.iIndepFun.comp (fun _ ↦ fun x : ℝ ↦ -x) (fun _ ↦ measurable_neg)
  · -- Proof comment: identical distribution is likewise preserved by coordinatewise negation.
    intro i j
    simpa using (hreflected.identDistrib i j).comp measurable_neg

/-- Helper for Theorem 19.35: identical distribution transports integrability from `logρ[W](0)`
to every sitewise log-ratio. -/
private lemma integrable_randomEnvironmentLogRatio
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ) (x : ℤ) :
    Integrable (logρ[W](x)) μ := by
  -- Proof comment: all sitewise log-ratios have the same law, so integrability of one coordinate
  -- propagates to every other coordinate.
  simpa using (hW.identDistrib_logRatio x 0).symm.integrable_snd hlog

/-- Helper for Theorem 19.35: the reflected negative-ray negated log-ratio field is integrable at
every coordinate once `logρ[W](0)` is integrable. -/
private lemma integrable_negReflectedLeftLogRatio
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ) (n : ℕ) :
    Integrable (fun ω ↦ -logρ[W](-((n : ℤ) + 1)) ω) μ := by
  -- Proof comment: first transport integrability to the reflected coordinate, then negate.
  exact (integrable_randomEnvironmentLogRatio (W := W) hW hlog (-((n : ℤ) + 1))).neg

/-- Helper for Theorem 19.35: restricting the `ℤ`-indexed log-ratio field to the nonnegative ray
preserves the i.i.d. structure. -/
private lemma rightLogRatio_isIID
    (hW : IsSolomonEnvironmentLaw μ W) :
    IsIID (fun n : ℕ ↦ fun ω ↦ logρ[W](n) ω) μ := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: restricting the `ℤ`-indexed field to the nonnegative ray preserves
    -- independence because `ℕ ↪ ℤ` is injective.
    simpa using
      hW.logRatio_iid.iIndepFun.precomp
        (g := fun n : ℕ ↦ (n : ℤ))
        (by
          intro a b h
          exact Int.ofNat.inj h)
  · -- Proof comment: the common law is inherited from the ambient Solomon field.
    intro i j
    simpa using hW.identDistrib_logRatio (i : ℤ) (j : ℤ)

/-- Helper for Theorem 19.35: shifting the nonnegative ray by one site preserves the i.i.d.
structure of the sampled Solomon log-ratio field. -/
private lemma shiftedRightLogRatio_isIID
    (hW : IsSolomonEnvironmentLaw μ W) :
    IsIID (fun n : ℕ ↦ fun ω ↦ logρ[W](n + 1) ω) μ := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: the successor embedding of `ℕ` into `ℤ` is injective, so independence is
    -- inherited from the ambient Solomon field.
    simpa using
      hW.logRatio_iid.iIndepFun.precomp
        (g := fun n : ℕ ↦ ((n + 1 : ℕ) : ℤ))
        (by
          intro a b h
          exact Nat.succ.inj (Int.ofNat.inj h))
  · -- Proof comment: identical distribution is unchanged after shifting both coordinates by one.
    intro i j
    simpa using hW.identDistrib_logRatio ((i + 1 : ℕ) : ℤ) ((j + 1 : ℕ) : ℤ)

/-- Helper for Theorem 19.35: the shifted right-ray log-ratio field has the same mean as the
origin field. -/
private lemma integral_shiftedRightLogRatio_eq_mean
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ) :
    ∫ ω, logρ[W](1) ω ∂μ = ∫ ω, logρ[W](0) ω ∂μ := by
  -- Proof comment: identical distribution transports the origin integral to the shifted ray.
  simpa using (hW.identDistrib_logRatio 1 0).integral_eq

/-- Helper for Theorem 19.35: a negative mean and the strong law force the partial sums of an
i.i.d. real field eventually below half the mean slope. -/
private lemma ae_eventually_prefixSum_le_halfMean_mul_of_mean_neg
    {Y : ℕ → Ω → ℝ}
    (hint : Integrable (Y 0) μ)
    (hY_iid : IsIID Y μ)
    (hmean : ∫ ω, Y 0 ω ∂μ < 0) :
    ∀ᵐ ω ∂μ,
      Filter.Eventually
        (fun n : ℕ ↦
          Finset.sum (Finset.range n) (fun i : ℕ ↦ Y i ω) ≤
            ((∫ ω, Y 0 ω ∂μ) / 2) * (n : ℝ)) atTop := by
  have hindep : Pairwise fun i j ↦ Y i ⟂ᵢ[μ] Y j := by
    intro i j hij
    exact hY_iid.iIndepFun.indepFun hij
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i ↦ hY_iid.identDistrib i 0
  have hslln := ProbabilityTheory.strong_law_ae_real Y hint hindep hident
  have hhalf : (∫ ω, Y 0 ω ∂μ) < (∫ ω, Y 0 ω ∂μ) / 2 := by
    linarith
  filter_upwards [hslln] with ω hω
  have hlt :
      ∀ᶠ n in atTop,
        (Finset.sum (Finset.range n) (fun i : ℕ ↦ Y i ω)) / (n : ℝ) <
          (∫ ω, Y 0 ω ∂μ) / 2 := by
    simpa using hω.eventually (Iio_mem_nhds hhalf)
  have hpos : Filter.Eventually (fun n : ℕ ↦ 0 < (n : ℝ)) atTop := by
    refine Filter.eventually_atTop.mpr ?_
    refine ⟨1, fun n hn ↦ ?_⟩
    positivity
  -- Proof comment: once the empirical averages stay below `mean / 2`, multiply by the positive
  -- denominator `n`.
  filter_upwards [hlt, hpos] with n hn hn_pos
  exact le_of_lt ((div_lt_iff₀ hn_pos).mp hn)

/-- Helper for Theorem 19.35: a positive mean and the strong law force the partial sums of an
i.i.d. real field eventually above half the mean slope. -/
private lemma ae_eventually_halfMean_mul_le_prefixSum_of_mean_pos
    {Y : ℕ → Ω → ℝ}
    (hint : Integrable (Y 0) μ)
    (hY_iid : IsIID Y μ)
    (hmean : 0 < ∫ ω, Y 0 ω ∂μ) :
    ∀ᵐ ω ∂μ,
      Filter.Eventually
        (fun n : ℕ ↦
          ((∫ ω, Y 0 ω ∂μ) / 2) * (n : ℝ) ≤
            Finset.sum (Finset.range n) (fun i : ℕ ↦ Y i ω)) atTop := by
  have hindep : Pairwise fun i j ↦ Y i ⟂ᵢ[μ] Y j := by
    intro i j hij
    exact hY_iid.iIndepFun.indepFun hij
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i ↦ hY_iid.identDistrib i 0
  have hslln := ProbabilityTheory.strong_law_ae_real Y hint hindep hident
  have hhalf : (∫ ω, Y 0 ω ∂μ) / 2 < (∫ ω, Y 0 ω ∂μ) := by
    linarith
  filter_upwards [hslln] with ω hω
  have hlt :
      ∀ᶠ n in atTop,
        (∫ ω, Y 0 ω ∂μ) / 2 <
          (Finset.sum (Finset.range n) (fun i : ℕ ↦ Y i ω)) / (n : ℝ) := by
    simpa using hω.eventually (Ioi_mem_nhds hhalf)
  have hpos : Filter.Eventually (fun n : ℕ ↦ 0 < (n : ℝ)) atTop := by
    refine Filter.eventually_atTop.mpr ?_
    refine ⟨1, fun n hn ↦ ?_⟩
    positivity
  -- Proof comment: multiply the eventual lower bound on the averages by the positive
  -- denominator `n`.
  filter_upwards [hlt, hpos] with n hn hn_pos
  exact le_of_lt ((lt_div_iff₀ hn_pos).mp hn)

/-- Helper for Theorem 19.35: the reflected negative-ray field has mean equal to the negated
common mean of the original Solomon log-ratio field. -/
private lemma integral_negReflectedLeftLogRatio_eq_neg_mean
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (n : ℕ) :
    ∫ ω, -logρ[W](-((n : ℤ) + 1)) ω ∂μ = - ∫ ω, logρ[W](0) ω ∂μ := by
  have hEq :
      ∫ ω, logρ[W](-((n : ℤ) + 1)) ω ∂μ = ∫ ω, logρ[W](0) ω ∂μ := by
    rw [(hW.identDistrib_logRatio (-((n : ℤ) + 1)) 0).integral_eq]
  -- Proof comment: move the reflected coordinate back to the origin and then pull out negation.
  simpa [integral_neg] using congrArg Neg.neg hEq

/-- Helper for Theorem 19.35: an eventual strictly negative linear upper bound on the exponent
forces the corresponding exponential ENNReal series to be finite. -/
private lemma expSeries_lt_top_of_eventually_linearUpperBound
    {S : ℕ → ℝ} {a : ℝ} (ha : a < 0)
    (hS : Filter.Eventually (fun n : ℕ ↦ S n ≤ a * n) atTop) :
    (∑' n, ENNReal.ofReal (Real.exp (S n))) < ∞ := by
  let r : ℝ := Real.exp a
  have hr_nonneg : 0 ≤ r := by
    -- Proof comment: the geometric comparison ratio is an exponential.
    dsimp [r]
    positivity
  have hr_lt_one : r < 1 := by
    -- Proof comment: a negative exponent yields a geometric ratio strictly below `1`.
    dsimp [r]
    exact Real.exp_lt_one_iff.mpr ha
  rcases Filter.eventually_atTop.mp hS with ⟨N, hN⟩
  have hgeom : Summable (fun n : ℕ ↦ r ^ n) := by
    -- Proof comment: once `r ∈ [0, 1)`, the real geometric series is summable.
    simpa [r] using summable_geometric_of_lt_one hr_nonneg hr_lt_one
  have htail :
      Summable (fun k : ℕ ↦ Real.exp (S (k + N))) := by
    have hgeomTail : Summable (fun k : ℕ ↦ r ^ (k + N)) := by
      exact (_root_.summable_nat_add_iff (f := fun n : ℕ ↦ r ^ n) N).2 hgeom
    -- Proof comment: every tail term is bounded by the same-index geometric term.
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) ?_ hgeomTail
    intro k
    have hbound : S (k + N) ≤ a * (k + N : ℕ) := hN (k + N) (Nat.le_add_left N k)
    calc
      Real.exp (S (k + N)) ≤ Real.exp (a * (k + N : ℕ)) := by
        exact Real.exp_le_exp.mpr hbound
      _ = r ^ (k + N) := by
        rw [show a * (k + N : ℕ) = ((k + N : ℕ) : ℝ) * a by ring]
        dsimp [r]
        rw [Real.exp_nat_mul]
  have hsummable : Summable (fun n : ℕ ↦ Real.exp (S n)) := by
    -- Proof comment: summability of one tail is equivalent to summability of the full sequence.
    exact (_root_.summable_nat_add_iff (f := fun n : ℕ ↦ Real.exp (S n)) N).mp htail
  -- Proof comment: a nonnegative summable real series maps to a finite ENNReal series under
  -- `ENNReal.ofReal`.
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hsummable]
  exact ENNReal.ofReal_lt_top

/-- Helper for Theorem 19.35: if the exponent is nonnegative infinitely often, then the
corresponding exponential ENNReal series diverges to `∞`. -/
private lemma expSeries_eq_top_of_frequently_nonnegative
    {S : ℕ → ℝ} (hS : Filter.Frequently (fun n : ℕ ↦ 0 ≤ S n) atTop) :
    (∑' n, ENNReal.ofReal (Real.exp (S n))) = ∞ := by
  let term : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (Real.exp (S n))
  by_contra hfinite
  have htend : Tendsto term atTop (nhds 0) := by
    -- Proof comment: a finite ENNReal sum forces the summands to tend to `0`.
    exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top (by simpa [term] using hfinite)
  have hhalf_pos : 0 < ENNReal.ofReal (1 / 2 : ℝ) := by
    -- Proof comment: `1 / 2` is a strictly positive contradiction threshold.
    refine ENNReal.ofReal_pos.2 ?_
    norm_num
  have hsmall : ∀ᶠ n in atTop, term n ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    -- Proof comment: eventual smallness follows from convergence of the summands to `0`.
    rcases (ENNReal.tendsto_atTop_zero.mp htend) (ENNReal.ofReal (1 / 2 : ℝ)) hhalf_pos with
      ⟨N, hN⟩
    exact Filter.eventually_atTop.mpr ⟨N, hN⟩
  have hhalf_lt_one : ENNReal.ofReal (1 / 2 : ℝ) < ENNReal.ofReal (1 : ℝ) := by
    -- Proof comment: the frequent lower bound `≥ 1` sits strictly above the eventual threshold.
    norm_num
  have hlarge : Filter.Frequently (fun n : ℕ ↦ ENNReal.ofReal (1 / 2 : ℝ) < term n) atTop := by
    -- Proof comment: every nonnegative exponent contributes at least `exp 0 = 1`.
    refine hS.mono ?_
    intro n hn
    have hone_le : (1 : ℝ) ≤ Real.exp (S n) := by
      simpa using (Real.exp_le_exp.mpr hn : Real.exp 0 ≤ Real.exp (S n))
    have hone_term : ENNReal.ofReal (1 : ℝ) ≤ term n := by
      exact ENNReal.ofReal_le_ofReal hone_le
    exact lt_of_lt_of_le hhalf_lt_one hone_term
  have hnot_large : ¬ Filter.Frequently (fun n : ℕ ↦ ENNReal.ofReal (1 / 2 : ℝ) < term n) atTop := by
    -- Proof comment: eventual upper bounds rule out frequent visits above the same threshold.
    rw [Filter.not_frequently]
    exact hsmall.mono fun n hn ↦ not_lt.mpr hn
  exact hnot_large hlarge

/-- Helper for Theorem 19.35: if a real sequence does not tend to `-∞`, then its exponential
series cannot have finite ENNReal sum. -/
private lemma expSeries_eq_top_of_not_tendsto_atBot
    {S : ℕ → ℝ} (hS : ¬ Tendsto S atTop atBot) :
    (∑' n, ENNReal.ofReal (Real.exp (S n))) = ∞ := by
  let term : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (Real.exp (S n))
  rw [tendsto_atTop_atBot] at hS
  push_neg at hS
  rcases hS with ⟨b, hb⟩
  have hlarge : Filter.Frequently (fun n : ℕ ↦ ENNReal.ofReal (Real.exp b) ≤ term n) atTop := by
    -- Proof comment: failing to converge to `-∞` leaves one exponential lower bound visited
    -- infinitely often.
    rw [Filter.frequently_atTop]
    intro N
    rcases hb N with ⟨n, hnN, hbn⟩
    refine ⟨n, hnN, ?_⟩
    exact ENNReal.ofReal_le_ofReal (le_of_lt (Real.exp_lt_exp.mpr hbn))
  by_contra hfinite
  have hfiniteSet :
      {n : ℕ | ENNReal.ofReal (Real.exp b) ≤ term n}.Finite := by
    refine ENNReal.finite_const_le_of_tsum_ne_top ?_ ?_
    · simpa [term] using hfinite
    · exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hnot_large : ¬ Filter.Frequently (fun n : ℕ ↦ ENNReal.ofReal (Real.exp b) ≤ term n) atTop := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact hfiniteSet.not_infinite
  exact hnot_large hlarge

/-- Helper for Theorem 19.35: along the one-sided shift, the Birkhoff sum of the first
coordinate is exactly the usual `Finset.range` prefix sum of the path. -/
private lemma birkhoffSumEvalZero_eq_rangeSum
    (z : ℕ → ℝ) (n : ℕ) :
    birkhoffSum Stream'.tail (Function.eval 0) n z =
      Finset.sum (Finset.range n) fun i : ℕ ↦ z i := by
  induction n generalizing z with
  | zero =>
      -- Proof comment: both the Birkhoff sum and the ordinary prefix sum are empty at time `0`.
      simp [birkhoffSum]
  | succ n ih =>
      -- Proof comment: peel off the head term and identify the tail contribution recursively.
      rw [birkhoffSum_succ', ih]
      simp [Stream'.tail, Stream'.get, Finset.sum_range_succ', add_comm]

/-- Helper for Theorem 19.35: the path law of an i.i.d. real field is the infinite product of
its one-coordinate marginal. -/
private lemma iidRealPathMeasure_eq_infinitePi
    {Y : ℕ → Ω → ℝ} (hY_iid : IsIID Y μ) :
    Measure.map (fun ω n ↦ Y n ω) μ =
      Measure.infinitePi (fun _ : ℕ ↦ Measure.map (Y 0) μ) := by
  have hY_aemeas : ∀ n : ℕ, AEMeasurable (Y n) μ := fun n ↦
    (hY_iid.identDistrib n 0).aemeasurable_fst
  -- Proof comment: compare the joint law with the product of the coordinate marginals and then
  -- collapse every marginal to the origin law.
  calc
    Measure.map (fun ω n ↦ Y n ω) μ
        = Measure.infinitePi (fun n : ℕ ↦ Measure.map (Y n) μ) := by
            exact (iIndepFun_iff_map_fun_eq_infinitePi_map₀' hY_aemeas).1 hY_iid.iIndepFun
    _ = Measure.infinitePi (fun _ : ℕ ↦ Measure.map (Y 0) μ) := by
          congr 1
          funext n
          exact (hY_iid.identDistrib n 0).map_eq

/-- Helper for Theorem 19.35: negating every coordinate of an i.i.d. real field preserves the
i.i.d. structure. -/
private lemma isIID_neg {Y : ℕ → Ω → ℝ} (hY_iid : IsIID Y μ) :
    IsIID (fun n ↦ fun ω ↦ -Y n ω) μ := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: independence is stable under the same measurable postcomposition on every
    -- coordinate.
    simpa using
      hY_iid.iIndepFun.comp (fun _ ↦ fun x : ℝ ↦ -x) (fun _ ↦ measurable_neg)
  · -- Proof comment: identical distribution is likewise stable under coordinatewise negation.
    intro i j
    simpa using (hY_iid.identDistrib i j).comp measurable_neg

/-- Helper for Theorem 19.35: the canonical path law of an i.i.d. real field is ergodic for the
one-sided shift. -/
private lemma iidRealPathMeasureErgodic
    {Y : ℕ → Ω → ℝ} (hY_iid : IsIID Y μ) :
    Ergodic Stream'.tail (Measure.map (fun ω n ↦ Y n ω) μ) := by
  let ν : Measure ℝ := Measure.map (Y 0) μ
  have hY0_aemeas : AEMeasurable (Y 0) μ := (hY_iid.identDistrib 0 0).aemeasurable_fst
  letI : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    dsimp [ν]
    rw [Measure.map_apply_of_aemeasurable hY0_aemeas MeasurableSet.univ, Set.preimage_univ]
    simp
  let P : Measure (Stream' ℝ) := Measure.infinitePi (fun _ : ℕ ↦ ν)
  letI : IsProbabilityMeasure P := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ ↦ ν))
    infer_instance
  have hmixing :
      MeasurePreserving Stream'.tail
          P
          P ∧
        IsStronglyMixing Stream'.tail P := by
    -- Proof comment: the one-sided Bernoulli shift is strongly mixing for every product law.
    simpa [ν] using
      (iid_oneSided_product_shift_is_mixing (E := ℝ) ν)
  rcases hmixing with ⟨hpres, hstrong⟩
  have hergodic :
      Ergodic Stream'.tail P :=
    ergodic_of_isStronglyMixing (P := P) hpres hstrong
  -- Proof comment: identify the i.i.d. path law with its Bernoulli product law and transport the
  -- ergodicity statement across that equality.
  have hpath : Measure.map (fun ω n ↦ Y n ω) μ = P := by
    simpa [P, ν] using iidRealPathMeasure_eq_infinitePi (μ := μ) (Y := Y) hY_iid
  exact hpath ▸ hergodic

/-- Helper for Theorem 19.35: a zero-mean i.i.d. real field has prefix sums that almost surely do
not tend to `-∞`. This is the Chapter 20 bridge used in Solomon's recurrent case. -/
private lemma ae_not_tendsto_atBot_prefixSum_of_mean_zero
    {Y : ℕ → Ω → ℝ}
    (hint : Integrable (Y 0) μ)
    (hY_iid : IsIID Y μ)
    (hmean : ∫ ω, Y 0 ω ∂μ = 0) :
    ∀ᵐ ω ∂μ,
      ¬ Tendsto
        (fun n ↦ Finset.sum (Finset.range n) (fun i : ℕ ↦ Y i ω))
        atTop atBot := by
  let Z : ℕ → Ω → ℝ := fun n ω ↦ -Y n ω
  let pathZ : Ω → ℕ → ℝ := fun ω n ↦ Z n ω
  let P : Measure (ℕ → ℝ) := Measure.map pathZ μ
  have hpathZ_aemeas : AEMeasurable pathZ μ := by
    -- Proof comment: each coordinate is a.e. measurable, so the path map is a.e. measurable in
    -- the product sigma-algebra.
    refine aemeasurable_pi_lambda _ fun n ↦ ?_
    exact ((isIID_neg (μ := μ) hY_iid).identDistrib n 0).aemeasurable_fst
  letI : IsProbabilityMeasure P := by
    refine ⟨?_⟩
    dsimp [P]
    rw [Measure.map_apply_of_aemeasurable hpathZ_aemeas MeasurableSet.univ, Set.preimage_univ]
    simp
  let B : Set (ℕ → ℝ) := {z |
    Tendsto (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n z) atTop atTop}
  have hZ_iid : IsIID Z μ := isIID_neg (μ := μ) hY_iid
  have hP_ergodic : Ergodic Stream'.tail P := by
    -- Proof comment: Chapter 20 supplies ergodicity of the i.i.d. path law under the shift.
    simpa [P, pathZ, Z] using iidRealPathMeasureErgodic (μ := μ) (Y := Z) hZ_iid
  have hP_int : Integrable (Function.eval 0) P := by
    -- Proof comment: the first coordinate under the path law is exactly the negated origin
    -- variable.
    rw [show P = Measure.map pathZ μ by rfl]
    refine
      (integrable_map_measure
        (μ := μ) (f := pathZ) (g := Function.eval 0)
        (measurable_pi_apply 0).aestronglyMeasurable hpathZ_aemeas).2 ?_
    change Integrable (fun ω ↦ -Y 0 ω) μ
    simpa using hint.neg
  have hP_meanZero : P[Function.eval 0] = 0 := by
    -- Proof comment: transport the zero mean of `Y 0` through the negated path map.
    change ∫ z, Function.eval 0 z ∂P = 0
    rw [show P = Measure.map pathZ μ by rfl,
      integral_map hpathZ_aemeas (measurable_pi_apply 0).aestronglyMeasurable]
    simpa [pathZ, Z, integral_neg, hmean]
  have hB_meas : MeasurableSet B := by
    -- Proof comment: the Chapter 20 Birkhoff event is measurable.
    exact measurableSet_tendsto atTop measurablePartialSumEvalZero
  have hB_zero : P B = 0 := by
    by_contra hB_ne_zero
    have hB_pos : 0 < P B := bot_lt_iff_ne_bot.mpr hB_ne_zero
    have hB_ae :
        ∀ᵐ z ∂P,
          Tendsto (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n z) atTop atTop :=
      (orbit_partial_sum_tendsto_atTop_ae_iff_measure_pos_of_ergodic
        P hP_ergodic (measurable_pi_apply 0)).2 hB_pos
    have hExpPos :
        0 < P[Function.eval 0] :=
      expectation_pos_of_partialSumAtTop_ae P hP_ergodic hP_int hB_ae
    have : 0 < (0 : ℝ) := by
      simpa [hP_meanZero] using hExpPos
    exact lt_irrefl 0 this
  have hpre_ae : pathZ ⁻¹' Bᶜ ∈ ae μ := by
    -- Proof comment: pull the almost-sure exclusion of the bad path event back to the original
    -- probability space.
    have hB_ae_notMem : Bᶜ ∈ ae P := by
      simpa [mem_ae_iff] using hB_zero
    exact (mem_ae_map_iff hpathZ_aemeas hB_meas.compl).mp hB_ae_notMem
  filter_upwards [hpre_ae] with ω hω
  intro hbad
  -- Proof comment: if the prefix sums tended to `-∞`, then the negated path would land in the
  -- forbidden shift-ergodic event.
  have hpathBad : pathZ ω ∈ B := by
    have hneg :
        Tendsto
          (fun n : ℕ ↦ -(Finset.sum (Finset.range n) (fun i : ℕ ↦ Y i ω)))
          atTop atTop :=
      tendsto_neg_atTop_iff.2 hbad
    simpa [B, pathZ, Z, birkhoffSumEvalZero_eq_rangeSum, Finset.sum_neg_distrib] using hneg
  have hnotBad : pathZ ω ∉ B := by
    simpa [Set.preimage, Set.mem_compl_iff] using hω
  exact hnotBad hpathBad

/-- Helper for Theorem 19.35: the right Solomon product splits into the zeroth ratio factor times
the exponential of the shifted right-ray log-ratio prefix sum. -/
private lemma randomEnvironmentRightSeriesTerm_eq_ratioZero_mul_ofReal_exp_shiftedLogPrefixSum
    (W : Ω → RandomEnvironment) (ω : Ω) (hω : (W ω).IsElliptic) (n : ℕ) :
    randomEnvironmentRightSeriesTerm (W ω) n =
      ENNReal.ofReal (Real.exp (logρ[W](0) ω)) *
        ENNReal.ofReal
          (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ logρ[W](i + 1) ω)) := by
  have hsum :
      Finset.sum (Finset.range (n + 1)) (fun i : ℕ ↦ logρ[W](i) ω) =
        logρ[W](0) ω +
          Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ[W](i + 1) ω) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_range_succ' (fun i : ℕ ↦ logρ[W](i) ω) n)
  -- Proof comment: split off the zeroth right-ray ratio and rewrite the remaining factors as the
  -- shifted prefix sum used by the generic IID lemmas.
  calc
    randomEnvironmentRightSeriesTerm (W ω) n
        = ENNReal.ofReal
            (Real.exp (Finset.sum (Finset.range (n + 1)) (fun i : ℕ ↦ logρ[W](i) ω))) := by
              simpa using
                randomEnvironmentRightSeriesTerm_eq_ofReal_exp_logPrefixSum
                  (W := W) ω hω n
    _ = ENNReal.ofReal
          (Real.exp
            (logρ[W](0) ω +
              Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ[W](i + 1) ω))) := by
            rw [hsum]
    _ = ENNReal.ofReal
          (Real.exp (logρ[W](0) ω) *
            Real.exp (Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ[W](i + 1) ω))) := by
            rw [Real.exp_add]
    _ = ENNReal.ofReal (Real.exp (logρ[W](0) ω)) *
          ENNReal.ofReal
            (Real.exp (Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ[W](i + 1) ω))) := by
            rw [ENNReal.ofReal_mul (by positivity)]

/-- Helper for Theorem 19.35: the right Solomon series is the boundary ratio factor times the
shifted-right exponential series. -/
private lemma randomEnvironmentRightSeries_eq_ratioZero_mul_tsum_shiftedExpLogPrefixSum
    (W : Ω → RandomEnvironment) (ω : Ω) (hω : (W ω).IsElliptic) :
    R⁺[W ω] =
      ENNReal.ofReal (Real.exp (logρ[W](0) ω)) *
        ∑' n : ℕ,
          ENNReal.ofReal
            (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ logρ[W](i + 1) ω)) := by
  have hterms :
      (fun n : ℕ ↦ randomEnvironmentRightSeriesTerm (W ω) n) =
        fun n : ℕ ↦
          ENNReal.ofReal (Real.exp (logρ[W](0) ω)) *
            ENNReal.ofReal
              (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ logρ[W](i + 1) ω)) := by
    -- Proof comment: rewrite each rightward product term into the packaged shifted-prefix form.
    funext n
    simpa using
      randomEnvironmentRightSeriesTerm_eq_ratioZero_mul_ofReal_exp_shiftedLogPrefixSum
        (W := W) ω hω n
  -- Proof comment: package the pointwise normal form once so later theorems can rewrite by a
  -- single series-level bridge.
  rw [randomEnvironmentRightSeries_def, hterms, ENNReal.tsum_mul_left]

/-- Helper for Theorem 19.35: the left Solomon series is exactly the reflected-left exponential
series. -/
private lemma randomEnvironmentLeftSeries_eq_tsum_reflectedNegExpLogPrefixSum
    (W : Ω → RandomEnvironment) (ω : Ω) (hω : (W ω).IsElliptic) :
    R⁻[W ω] =
      ∑' n : ℕ,
        ENNReal.ofReal
          (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ -logρ[W](-((i : ℤ) + 1)) ω)) := by
  have hterms :
      (fun n : ℕ ↦ randomEnvironmentLeftSeriesTerm (W ω) n) =
        fun n : ℕ ↦
          ENNReal.ofReal
            (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ -logρ[W](-((i : ℤ) + 1)) ω)) := by
    -- Proof comment: rewrite each reflected leftward product term into its exponential prefix
    -- normal form.
    funext n
    simpa using
      randomEnvironmentLeftSeriesTerm_eq_ofReal_exp_reflectedNegLogPrefixSum
        (W := W) ω hω n
  -- Proof comment: after the termwise rewrite, the left series is already in the desired normal
  -- form with no extra boundary factor.
  rw [randomEnvironmentLeftSeries_def, hterms]

/-- Helper for Theorem 19.35: the shifted-right logarithmic prefix sum used in the right Solomon
series normal form. -/
private def shiftedRightLogRatioField
    (W : Ω → RandomEnvironment) : ℕ → Ω → ℝ :=
  fun n ω ↦ logρ[W](n + 1) ω

/-- Helper for Theorem 19.35: the reflected-left negated logarithmic field used in the left
Solomon series normal form. -/
private def reflectedNegLeftLogRatioField
    (W : Ω → RandomEnvironment) : ℕ → Ω → ℝ :=
  fun n ω ↦ -logρ[W](-((n : ℤ) + 1)) ω

/-- Helper for Theorem 19.35: the shifted-right field inherits integrability at the base
coordinate from the origin Solomon log-ratio. -/
private lemma integrable_shiftedRightLogRatioField
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ) :
    Integrable (shiftedRightLogRatioField W 0) μ := by
  -- Proof comment: the alias is just the site `1` log-ratio field.
  simpa [shiftedRightLogRatioField] using
    (integrable_randomEnvironmentLogRatio (W := W) hW hlog 1)

/-- Helper for Theorem 19.35: the shifted-right field keeps the i.i.d. structure of the Solomon
log-ratio field. -/
private lemma shiftedRightLogRatioField_isIID
    (hW : IsSolomonEnvironmentLaw μ W) :
    IsIID (shiftedRightLogRatioField W) μ := by
  -- Proof comment: this is only a thin alias over the already proved shifted-right IID family.
  simpa [shiftedRightLogRatioField] using shiftedRightLogRatio_isIID (W := W) hW

/-- Helper for Theorem 19.35: the mean of the shifted-right alias at coordinate `0` is the origin
mean. -/
private lemma integral_shiftedRightLogRatioField_zero_eq_mean
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ) :
    ∫ ω, shiftedRightLogRatioField W 0 ω ∂μ = ∫ ω, logρ[W](0) ω ∂μ := by
  -- Proof comment: unfolding the alias reduces this to the already packaged shifted-mean lemma.
  simpa [shiftedRightLogRatioField] using integral_shiftedRightLogRatio_eq_mean hW hlog

/-- Helper for Theorem 19.35: the reflected-left field alias keeps the i.i.d. structure of the
reflected negated Solomon log-ratio field. -/
private lemma reflectedNegLeftLogRatioField_isIID
    (hW : IsSolomonEnvironmentLaw μ W) :
    IsIID (reflectedNegLeftLogRatioField W) μ := by
  -- Proof comment: rewrite the alias to the exact reflected coordinate family already proved i.i.d.
  change IsIID (fun n : ℕ ↦ fun ω ↦ -logρ[W](-((n : ℤ) + 1)) ω) μ
  exact negReflectedLeftLogRatio_isIID (W := W) hW

/-- Helper for Theorem 19.35: the reflected-left field alias is integrable at the base
coordinate. -/
private lemma integrable_reflectedNegLeftLogRatioField
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ) :
    Integrable (reflectedNegLeftLogRatioField W 0) μ := by
  -- Proof comment: the base reflected alias is exactly the previously packaged reflected
  -- coordinate `n = 0`.
  change Integrable (fun ω ↦ -logρ[W](-((0 : ℤ) + 1)) ω) μ
  exact integrable_negReflectedLeftLogRatio (W := W) hW hlog 0

/-- Helper for Theorem 19.35: the shifted-right logarithmic prefix sum used in the right Solomon
series normal form. -/
private def shiftedRightLogPrefixSum
    (W : Ω → RandomEnvironment) (ω : Ω) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) (fun i : ℕ ↦ shiftedRightLogRatioField W i ω)

/-- Helper for Theorem 19.35: the reflected-left negated logarithmic prefix sum used in the left
Solomon series normal form. -/
private def reflectedNegLeftLogPrefixSum
    (W : Ω → RandomEnvironment) (ω : Ω) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) (fun i : ℕ ↦ reflectedNegLeftLogRatioField W i ω)

/-- Helper for Theorem 19.35: the shifted-right alias is definitionally the raw `Finset.range`
prefix sum used by the generic SLLN bridge. -/
private lemma shiftedRightLogPrefixSum_apply
    (W : Ω → RandomEnvironment) (ω : Ω) (n : ℕ) :
    shiftedRightLogPrefixSum W ω n =
      Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ[W](i + 1) ω) := by
  -- Proof comment: this exposes the alias in the exact normal form expected by the generic
  -- prefix-sum lemmas.
  simp [shiftedRightLogPrefixSum, shiftedRightLogRatioField]

/-- Helper for Theorem 19.35: the reflected-left alias is definitionally the raw `Finset.range`
prefix sum used by the generic SLLN bridge. -/
private lemma reflectedNegLeftLogPrefixSum_apply
    (W : Ω → RandomEnvironment) (ω : Ω) (n : ℕ) :
    reflectedNegLeftLogPrefixSum W ω n =
      Finset.sum (Finset.range n) (fun i : ℕ ↦ -logρ[W](-((i : ℤ) + 1)) ω) := by
  -- Proof comment: this keeps the reflected alias in the same spelling world as the reusable
  -- Chapter 20 prefix-sum API.
  simp [reflectedNegLeftLogPrefixSum, reflectedNegLeftLogRatioField]

/-- Helper for Theorem 19.35: the right Solomon series bridge rewritten in the shifted-right alias
spelling. -/
private lemma randomEnvironmentRightSeries_eq_ratioZero_mul_tsum_shiftedRightLogPrefixSum
    (W : Ω → RandomEnvironment) (ω : Ω) (hω : (W ω).IsElliptic) :
    R⁺[W ω] =
      ENNReal.ofReal (Real.exp (logρ[W](0) ω)) *
        ∑' n : ℕ, ENNReal.ofReal (Real.exp (shiftedRightLogPrefixSum W ω n)) := by
  -- Proof comment: rewrite the existing raw series bridge once into the local alias spelling.
  simpa only [shiftedRightLogPrefixSum_apply] using
    randomEnvironmentRightSeries_eq_ratioZero_mul_tsum_shiftedExpLogPrefixSum
      (W := W) ω hω

/-- Helper for Theorem 19.35: the left Solomon series bridge rewritten in the reflected-left alias
spelling. -/
private lemma randomEnvironmentLeftSeries_eq_tsum_reflectedNegLeftLogPrefixSum
    (W : Ω → RandomEnvironment) (ω : Ω) (hω : (W ω).IsElliptic) :
    R⁻[W ω] =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (reflectedNegLeftLogPrefixSum W ω n)) := by
  -- Proof comment: keep the left-series normalization in the alias spelling used by the final
  -- Solomon regime theorems.
  simpa only [reflectedNegLeftLogPrefixSum_apply] using
    randomEnvironmentLeftSeries_eq_tsum_reflectedNegExpLogPrefixSum
      (W := W) ω hω

/-- Helper for Theorem 19.35: a negative origin mean forces the shifted-right prefix sums below
half the mean slope eventually almost surely. -/
private lemma ae_eventually_shiftedRightLogPrefix_le_halfMean_mul_of_mean_neg
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, logρ[W](0) ω ∂μ < 0) :
    ∀ᵐ ω ∂μ,
      Filter.Eventually
        (fun n : ℕ ↦
          shiftedRightLogPrefixSum W ω n ≤
            ((∫ ω, logρ[W](0) ω ∂μ) / 2) * (n : ℝ)) atTop := by
  -- Route correction: rewrite through the alias `_apply` lemma instead of unfolding the alias
  -- under `Filter.Eventually`.
  have hshiftMean : ∫ ω, logρ[W](1) ω ∂μ < 0 := by
    rw [integral_shiftedRightLogRatio_eq_mean hW hlog]
    exact hmean
  have hraw :=
    ae_eventually_prefixSum_le_halfMean_mul_of_mean_neg
      (μ := μ)
      (Y := shiftedRightLogRatioField W)
      (integrable_shiftedRightLogRatioField hW hlog)
      (shiftedRightLogRatioField_isIID hW)
      hshiftMean
  have hraw' :
      ∀ᵐ ω ∂μ,
        Filter.Eventually
          (fun n : ℕ ↦
            shiftedRightLogPrefixSum W ω n ≤
              ((∫ ω, logρ[W](1) ω ∂μ) / 2) * (n : ℝ)) atTop := by
    -- Proof comment: first rewrite only the field alias and the prefix-sum alias.
    simpa only [shiftedRightLogPrefixSum_apply, shiftedRightLogRatioField] using hraw
  have hcoeff :
      ∫ ω, logρ[W](1) ω ∂μ = ∫ ω, logρ[W](0) ω ∂μ :=
    integral_shiftedRightLogRatio_eq_mean hW hlog
  -- Proof comment: the shifted alias is exactly the raw prefix sum seen by the generic strong law.
  simpa only [hcoeff] using hraw'

/-- Helper for Theorem 19.35: a positive shifted-right mean forces the shifted-right prefix sums
above half the mean slope eventually almost surely. -/
private lemma ae_eventually_shiftedRightHalfMean_mul_le_logPrefix_of_mean_pos
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : 0 < ∫ ω, logρ[W](1) ω ∂μ) :
    ∀ᵐ ω ∂μ,
      Filter.Eventually
        (fun n : ℕ ↦
          ((∫ ω, logρ[W](1) ω ∂μ) / 2) * (n : ℝ) ≤
            shiftedRightLogPrefixSum W ω n) atTop := by
  -- Route correction: prove the shifted-right wrapper by a direct `simpa` from the generic
  -- positive-slope SLLN lemma.
  have hraw :=
    ae_eventually_halfMean_mul_le_prefixSum_of_mean_pos
      (μ := μ)
      (Y := shiftedRightLogRatioField W)
      (integrable_shiftedRightLogRatioField hW hlog)
      (shiftedRightLogRatioField_isIID hW)
      hmean
  -- Proof comment: the alias matches the generic prefix-sum spelling exactly after one rewrite.
  simpa only [shiftedRightLogPrefixSum_apply, shiftedRightLogRatioField] using hraw

/-- Helper for Theorem 19.35: the zero-mean shifted-right prefix sums do not tend to `-∞`
almost surely. -/
private lemma ae_not_tendsto_atBot_shiftedRightLogPrefix_of_mean_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, logρ[W](1) ω ∂μ = 0) :
    ∀ᵐ ω ∂μ,
      ¬ Tendsto
        (fun n : ℕ ↦ shiftedRightLogPrefixSum W ω n)
        atTop atBot := by
  -- Route correction: use the Chapter 20 non-`atBot` bridge on the raw prefix sums and rewrite
  -- once through the alias API.
  have hraw :=
    ae_not_tendsto_atBot_prefixSum_of_mean_zero
      (μ := μ)
      (Y := shiftedRightLogRatioField W)
      (integrable_shiftedRightLogRatioField hW hlog)
      (shiftedRightLogRatioField_isIID hW)
      hmean
  -- Proof comment: the alias is definitionally the same prefix-sum process.
  simpa only [shiftedRightLogPrefixSum_apply, shiftedRightLogRatioField] using hraw

/-- Helper for Theorem 19.35: a positive reflected-left mean forces the reflected-left prefix
sums above half the mean slope eventually almost surely. -/
private lemma ae_eventually_reflectedNegLeftHalfMean_mul_le_prefix_of_mean_pos
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : 0 < ∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ) :
    ∀ᵐ ω ∂μ,
      Filter.Eventually
        (fun n : ℕ ↦
          ((∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ) / 2) * (n : ℝ) ≤
            reflectedNegLeftLogPrefixSum W ω n) atTop := by
  -- Route correction: use the reflected IID family directly and expose the alias only at the end.
  have hraw :=
    ae_eventually_halfMean_mul_le_prefixSum_of_mean_pos
      (μ := μ)
      (Y := reflectedNegLeftLogRatioField W)
      (integrable_reflectedNegLeftLogRatioField hW hlog)
      (reflectedNegLeftLogRatioField_isIID hW)
      hmean
  -- Proof comment: the reflected alias is just the raw reflected prefix sum used by the generic
  -- strong law.
  simpa only [reflectedNegLeftLogPrefixSum_apply] using hraw

/-- Helper for Theorem 19.35: a negative reflected-left mean forces the reflected-left prefix
sums below half the mean slope eventually almost surely. -/
private lemma ae_eventually_reflectedNegLeftLogPrefix_le_halfMean_mul_of_mean_neg
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ < 0) :
    ∀ᵐ ω ∂μ,
      Filter.Eventually
        (fun n : ℕ ↦
          reflectedNegLeftLogPrefixSum W ω n ≤
            ((∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ) / 2) * (n : ℝ)) atTop := by
  -- Route correction: rewrite through the reflected alias bridge instead of unfolding under
  -- `Eventually`.
  have hraw :=
    ae_eventually_prefixSum_le_halfMean_mul_of_mean_neg
      (μ := μ)
      (Y := reflectedNegLeftLogRatioField W)
      (integrable_reflectedNegLeftLogRatioField hW hlog)
      (reflectedNegLeftLogRatioField_isIID hW)
      hmean
  -- Proof comment: after the alias rewrite, the result is exactly the generic reflected prefix
  -- statement.
  simpa only [reflectedNegLeftLogPrefixSum_apply] using hraw

/-- Helper for Theorem 19.35: the zero-mean reflected-left prefix sums do not tend to `-∞`
almost surely. -/
private lemma ae_not_tendsto_atBot_reflectedNegLeftPrefix_of_mean_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ = 0) :
    ∀ᵐ ω ∂μ,
      ¬ Tendsto
        (fun n : ℕ ↦ reflectedNegLeftLogPrefixSum W ω n)
        atTop atBot := by
  -- Route correction: use the zero-mean prefix-sum bridge once in the raw reflected spelling and
  -- then return to the alias API.
  have hraw :=
    ae_not_tendsto_atBot_prefixSum_of_mean_zero
      (μ := μ)
      (Y := reflectedNegLeftLogRatioField W)
      (integrable_reflectedNegLeftLogRatioField hW hlog)
      (reflectedNegLeftLogRatioField_isIID hW)
      hmean
  -- Proof comment: the alias and the raw reflected prefix process are identical termwise.
  simpa only [reflectedNegLeftLogPrefixSum_apply] using hraw

-- Proof sketch: apply the strong law of large numbers to the i.i.d. field `x ↦ logρ[W](x)` from
-- `IsSolomonEnvironmentLaw`; negative mean implies exponentially decaying rightward products and
-- divergent reciprocal leftward products, so Solomon's series satisfy `R_w^- = ∞` and
-- `R_w^+ < ∞` almost surely.
/-- Theorem 19.35: if the common law of `log ρ₀` has negative mean, then almost every sampled
environment lies in the Solomon regime `R_w^- = ∞`, `R_w^+ < ∞` used in Theorem 19.33. -/
theorem ae_leftSeries_eq_top_and_rightSeries_lt_top_of_integral_logRatio_lt_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, logρ[W](0) ω ∂μ < 0) :
    ∀ᵐ ω ∂μ,
      R⁻[W ω] = ∞ ∧ R⁺[W ω] < ∞ := by
  have hrightPrefix :=
    ae_eventually_shiftedRightLogPrefix_le_halfMean_mul_of_mean_neg hW hlog hmean
  have hreflectedMean :
      0 < ∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ := by
    have hEq :
        ∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ =
          -∫ ω, logρ[W](0) ω ∂μ := by
      simpa using integral_negReflectedLeftLogRatio_eq_neg_mean hW hlog 0
    rw [hEq]
    linarith
  have hleftPrefix :=
    ae_eventually_reflectedNegLeftHalfMean_mul_le_prefix_of_mean_pos hW hlog hreflectedMean
  have hrightCoeff : (∫ ω, logρ[W](0) ω ∂μ) / 2 < 0 := by
    linarith
  have hreflectedCoeffNonneg :
      0 ≤ (∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ) / 2 := by
    exact le_of_lt (half_pos hreflectedMean)
  filter_upwards [hW.ae_elliptic, hrightPrefix, hleftPrefix] with ω hω hright hleft
  constructor
  · have hleftEventuallyNonneg :
        Filter.Eventually (fun n : ℕ ↦ 0 ≤ reflectedNegLeftLogPrefixSum W ω n) atTop := by
      filter_upwards [hleft] with n hn
      have hbase : 0 ≤ ((∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ) / 2) * (n : ℝ) :=
        mul_nonneg hreflectedCoeffNonneg (show 0 ≤ (n : ℝ) by positivity)
      exact le_trans hbase hn
    have hseries :
        (∑' n : ℕ, ENNReal.ofReal (Real.exp (reflectedNegLeftLogPrefixSum W ω n))) = ∞ :=
      expSeries_eq_top_of_frequently_nonnegative hleftEventuallyNonneg.frequently
    -- Proof comment: once the reflected exponent is eventually nonnegative, the left Solomon
    -- series diverges after the alias-level series rewrite.
    rw [randomEnvironmentLeftSeries_eq_tsum_reflectedNegLeftLogPrefixSum (W := W) ω hω, hseries]
  · have hseries :
        (∑' n : ℕ, ENNReal.ofReal (Real.exp (shiftedRightLogPrefixSum W ω n))) < ∞ :=
      expSeries_lt_top_of_eventually_linearUpperBound hrightCoeff hright
    -- Proof comment: the negative slope gives a finite exponential tail, and the extra boundary
    -- factor is a finite ENNReal constant.
    rw [randomEnvironmentRightSeries_eq_ratioZero_mul_tsum_shiftedRightLogPrefixSum
      (W := W) ω hω]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hseries

-- Proof sketch: the same strong-law argument, now with positive mean, makes the rightward
-- products grow and the leftward reciprocal products decay, yielding `R_w^- < ∞` and
-- `R_w^+ = ∞` almost surely.
/-- If the common law of `log ρ₀` has positive mean, then almost every sampled environment lies in
the Solomon regime `R_w^- < ∞`, `R_w^+ = ∞` used in Theorem 19.33. -/
theorem ae_leftSeries_lt_top_and_rightSeries_eq_top_of_integral_logRatio_gt_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : 0 < ∫ ω, logρ[W](0) ω ∂μ) :
    ∀ᵐ ω ∂μ,
      R⁻[W ω] < ∞ ∧ R⁺[W ω] = ∞ := by
  have hshiftMean :
      0 < ∫ ω, logρ[W](1) ω ∂μ := by
    rw [integral_shiftedRightLogRatio_eq_mean hW hlog]
    exact hmean
  have hrightPrefix :=
    ae_eventually_shiftedRightHalfMean_mul_le_logPrefix_of_mean_pos hW hlog hshiftMean
  have hreflectedMean :
      ∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ < 0 := by
    have hEq :
        ∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ =
          -∫ ω, logρ[W](0) ω ∂μ := by
      simpa using integral_negReflectedLeftLogRatio_eq_neg_mean hW hlog 0
    rw [hEq]
    linarith
  have hleftPrefix :=
    ae_eventually_reflectedNegLeftLogPrefix_le_halfMean_mul_of_mean_neg hW hlog hreflectedMean
  have hreflectedCoeff : (∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ) / 2 < 0 := by
    have htwo : (0 : ℝ) < 2 := by norm_num
    exact (div_neg_iff).2 <| Or.inr ⟨hreflectedMean, htwo⟩
  have hshiftCoeffNonneg : 0 ≤ (∫ ω, logρ[W](1) ω ∂μ) / 2 := by
    exact le_of_lt (half_pos hshiftMean)
  filter_upwards [hW.ae_elliptic, hleftPrefix, hrightPrefix] with ω hω hleft hright
  constructor
  · have hseries :
        (∑' n : ℕ, ENNReal.ofReal (Real.exp (reflectedNegLeftLogPrefixSum W ω n))) < ∞ :=
      expSeries_lt_top_of_eventually_linearUpperBound hreflectedCoeff hleft
    -- Proof comment: the reflected negative slope makes the left Solomon series summable after
    -- the alias-level normalization.
    rw [randomEnvironmentLeftSeries_eq_tsum_reflectedNegLeftLogPrefixSum (W := W) ω hω]
    exact hseries
  · have hrightEventuallyNonneg :
        Filter.Eventually (fun n : ℕ ↦ 0 ≤ shiftedRightLogPrefixSum W ω n) atTop := by
      filter_upwards [hright] with n hn
      have hbase : 0 ≤ ((∫ ω, logρ[W](1) ω ∂μ) / 2) * (n : ℝ) :=
        mul_nonneg hshiftCoeffNonneg (show 0 ≤ (n : ℝ) by positivity)
      exact le_trans hbase hn
    have hseries :
        (∑' n : ℕ, ENNReal.ofReal (Real.exp (shiftedRightLogPrefixSum W ω n))) = ∞ :=
      expSeries_eq_top_of_frequently_nonnegative hrightEventuallyNonneg.frequently
    have hconst_ne_zero : ENNReal.ofReal (Real.exp (logρ[W](0) ω)) ≠ 0 := by
      simpa only [Ne, ENNReal.ofReal_eq_zero, not_le] using
        (Real.exp_pos (logρ[W](0) ω))
    -- Proof comment: the right series differs from the alias exponential series only by a
    -- strictly positive boundary factor.
    rw [randomEnvironmentRightSeries_eq_ratioZero_mul_tsum_shiftedRightLogPrefixSum
      (W := W) ω hω, hseries]
    simp [hconst_ne_zero]

-- Proof sketch: zero mean forces the partial sums of `log ρ_x` to oscillate on both sides
-- infinitely often, so neither Solomon series converges.
/-- If the common law of `log ρ₀` has mean `0`, then almost every sampled environment lies in the
recurrent Solomon regime `R_w^- = ∞`, `R_w^+ = ∞` used in Theorem 19.33. -/
theorem ae_leftSeries_eq_top_and_rightSeries_eq_top_of_integral_logRatio_eq_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, logρ[W](0) ω ∂μ = 0) :
    ∀ᵐ ω ∂μ,
      R⁻[W ω] = ∞ ∧ R⁺[W ω] = ∞ := by
  have hshiftMean :
      ∫ ω, logρ[W](1) ω ∂μ = 0 := by
    rw [integral_shiftedRightLogRatio_eq_mean hW hlog]
    exact hmean
  have hrightPrefix :=
    ae_not_tendsto_atBot_shiftedRightLogPrefix_of_mean_zero hW hlog hshiftMean
  have hreflectedMean :
      ∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ = 0 := by
    have hEq :
        ∫ ω, -logρ[W](-((0 : ℤ) + 1)) ω ∂μ =
          -∫ ω, logρ[W](0) ω ∂μ := by
      simpa using integral_negReflectedLeftLogRatio_eq_neg_mean hW hlog 0
    rw [hEq]
    simpa using congrArg Neg.neg hmean
  have hleftPrefix :=
    ae_not_tendsto_atBot_reflectedNegLeftPrefix_of_mean_zero hW hlog hreflectedMean
  filter_upwards [hW.ae_elliptic, hleftPrefix, hrightPrefix] with ω hω hleft hright
  constructor
  · have hseries :
        (∑' n : ℕ, ENNReal.ofReal (Real.exp (reflectedNegLeftLogPrefixSum W ω n))) = ∞ :=
      expSeries_eq_top_of_not_tendsto_atBot hleft
    -- Proof comment: the left alias exponential series diverges because its exponent does not
    -- drift to `-∞`.
    rw [randomEnvironmentLeftSeries_eq_tsum_reflectedNegLeftLogPrefixSum (W := W) ω hω, hseries]
  · have hseries :
        (∑' n : ℕ, ENNReal.ofReal (Real.exp (shiftedRightLogPrefixSum W ω n))) = ∞ :=
      expSeries_eq_top_of_not_tendsto_atBot hright
    have hconst_ne_zero : ENNReal.ofReal (Real.exp (logρ[W](0) ω)) ≠ 0 := by
      simpa only [Ne, ENNReal.ofReal_eq_zero, not_le] using
        (Real.exp_pos (logρ[W](0) ω))
    -- Proof comment: the right Solomon series is the same divergent alias series up to a
    -- positive boundary factor.
    rw [randomEnvironmentRightSeries_eq_ratioZero_mul_tsum_shiftedRightLogPrefixSum
      (W := W) ω hω, hseries]
    simp [hconst_ne_zero]

end SeriesBridge

section Quenched

variable {Ξ : Type v} [MeasurableSpace Ξ]
variable {W : Ω → RandomEnvironment}
variable {P : Ω → ℤ → ProbabilityMeasure Ξ} {X : Ω → ℕ → Ξ → ℤ}

-- Proof sketch: combine the almost-sure series regime from
-- `ae_leftSeries_eq_top_and_rightSeries_lt_top_of_integral_logRatio_lt_zero` with Theorem 19.33
-- for each fixed environment sample `ω`; since `R_w^- = ∞`, the positive-direction Solomon ratio
-- is `1`, so the quenched probability of `X_n → +∞` equals `1`.
/-- Part (1) of Theorem 19.35: if `E[log ρ₀] < 0` and `E[|log ρ₀|] < ∞`, then for almost every
environment sample `ω`, every realization of the random walk in the fixed environment `W ω`
tends to `+∞` with quenched probability `1`. -/
theorem ae_quenched_prob_tendsToPosInfinity_of_integral_logRatio_lt_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, logρ[W](0) ω ∂μ < 0)
    (hreal :
      ∀ ω,
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix (W ω)) ^ n)
          (P ω) (X ω)) :
    ∀ᵐ ω ∂μ,
      (P ω 0 : Measure Ξ) {ξ | Tendsto (fun n ↦ X ω n ξ) atTop atTop} = 1 := by
  -- Proof comment: first place almost every sampled environment in the Solomon regime
  -- `R_w^- = ∞`, `R_w^+ < ∞`.
  have hseries :
      ∀ᵐ ω ∂μ,
        R⁻[W ω] = ∞ ∧ R⁺[W ω] < ∞ :=
    ae_leftSeries_eq_top_and_rightSeries_lt_top_of_integral_logRatio_lt_zero hW hlog hmean
  -- Proof comment: on each such sample, apply Theorem 19.33 and collapse Solomon's directional
  -- ratio with `R_w^- = ∞`.
  filter_upwards [hseries, hW.ae_elliptic] with ω hseries hω
  rcases hseries with ⟨hleft, hright⟩
  letI := hreal ω
  have hprob :
      (P ω 0 : Measure Ξ) {ξ | Tendsto (fun n ↦ X ω n ξ) atTop atTop} =
        solomonDirectionalSeriesRatio R⁻[W ω] R⁺[W ω] :=
    randomEnvironmentWalk_prob_tendsToPosInfinity
      (W := W ω) (P := P ω) (X := X ω) hω (Or.inr hright)
  have hratio : solomonDirectionalSeriesRatio R⁻[W ω] R⁺[W ω] = 1 := by
    simpa [hleft] using
      (solomonDirectionalSeriesRatio_eq_one
        (toward := R⁻[W ω]) (away := R⁺[W ω]) hleft)
  calc
    (P ω 0 : Measure Ξ) {ξ | Tendsto (fun n ↦ X ω n ξ) atTop atTop}
        = solomonDirectionalSeriesRatio R⁻[W ω] R⁺[W ω] := hprob
    _ = 1 := hratio

-- Proof sketch: use the almost-sure series regime from
-- `ae_leftSeries_lt_top_and_rightSeries_eq_top_of_integral_logRatio_gt_zero` and apply Theorem
-- 19.33 pointwise in the sampled environment `W ω`; the negative-direction ratio is then `1`.
/-- Part (2) of Theorem 19.35: if `E[log ρ₀] > 0` and `E[|log ρ₀|] < ∞`, then for almost every
environment sample `ω`, every realization of the random walk in the fixed environment `W ω`
tends to `-∞` with quenched probability `1`. -/
theorem ae_quenched_prob_tendsToNegInfinity_of_integral_logRatio_gt_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : 0 < ∫ ω, logρ[W](0) ω ∂μ)
    (hreal :
      ∀ ω,
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix (W ω)) ^ n)
          (P ω) (X ω)) :
    ∀ᵐ ω ∂μ,
      (P ω 0 : Measure Ξ) {ξ | Tendsto (fun n ↦ X ω n ξ) atTop atBot} = 1 := by
  -- Proof comment: first put almost every sampled environment into the Solomon regime
  -- `R_w^- < ∞`, `R_w^+ = ∞`.
  have hseries :
      ∀ᵐ ω ∂μ,
        R⁻[W ω] < ∞ ∧ R⁺[W ω] = ∞ :=
    ae_leftSeries_lt_top_and_rightSeries_eq_top_of_integral_logRatio_gt_zero hW hlog hmean
  -- Proof comment: then apply the negative-direction formula from Theorem 19.33 and simplify the
  -- Solomon ratio with `R_w^+ = ∞`.
  filter_upwards [hseries, hW.ae_elliptic] with ω hseries hω
  rcases hseries with ⟨hleft, hright⟩
  letI := hreal ω
  have hprob :
      (P ω 0 : Measure Ξ) {ξ | Tendsto (fun n ↦ X ω n ξ) atTop atBot} =
        solomonDirectionalSeriesRatio R⁺[W ω] R⁻[W ω] :=
    randomEnvironmentWalk_prob_tendsToNegInfinity
      (W := W ω) (P := P ω) (X := X ω) hω (Or.inl hleft)
  have hratio : solomonDirectionalSeriesRatio R⁺[W ω] R⁻[W ω] = 1 := by
    simpa [hright] using
      (solomonDirectionalSeriesRatio_eq_one
        (toward := R⁺[W ω]) (away := R⁻[W ω]) hright)
  calc
    (P ω 0 : Measure Ξ) {ξ | Tendsto (fun n ↦ X ω n ξ) atTop atBot}
        = solomonDirectionalSeriesRatio R⁺[W ω] R⁻[W ω] := hprob
    _ = 1 := hratio

-- Proof sketch: combine the recurrent series regime from
-- `ae_leftSeries_eq_top_and_rightSeries_eq_top_of_integral_logRatio_eq_zero` with Theorem 19.33
-- pointwise in `W ω`.
/-- Part (3) of Theorem 19.35: if `E[log ρ₀] = 0` and `E[|log ρ₀|] < ∞`, then for almost every
environment sample `ω`, every realization of the random walk in the fixed environment `W ω`
satisfies `liminf Xₙ = -∞` almost surely under the quenched law. -/
theorem ae_quenched_liminf_eq_bot_of_integral_logRatio_eq_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, logρ[W](0) ω ∂μ = 0)
    (hreal :
      ∀ ω,
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix (W ω)) ^ n)
          (P ω) (X ω)) :
    ∀ᵐ ω ∂μ,
      ∀ᵐ ξ ∂(P ω 0 : Measure Ξ),
        liminf (fun n ↦ (((X ω n ξ : ℤ) : ℝ) : EReal)) atTop = ⊥ := by
  -- Proof comment: the zero-mean bridge theorem puts almost every sample into the recurrent
  -- Solomon regime `R_w^- = R_w^+ = ∞`.
  have hseries :
      ∀ᵐ ω ∂μ,
        R⁻[W ω] = ∞ ∧ R⁺[W ω] = ∞ :=
    ae_leftSeries_eq_top_and_rightSeries_eq_top_of_integral_logRatio_eq_zero hW hlog hmean
  -- Proof comment: Theorem 19.33 then gives the quenched `liminf` statement pointwise in each
  -- sampled environment.
  filter_upwards [hseries, hW.ae_elliptic] with ω hseries hω
  rcases hseries with ⟨hleft, hright⟩
  letI := hreal ω
  simpa using
    (randomEnvironmentWalk_ae_hasLiminfEqNegInfinity
      (W := W ω) (P := P ω) (X := X ω) hω hleft hright)

-- Proof sketch: the same recurrent regime from
-- `ae_leftSeries_eq_top_and_rightSeries_eq_top_of_integral_logRatio_eq_zero`, together with the
-- second oscillation conclusion in Theorem 19.33, gives `limsup Xₙ = +∞` quenched almost surely.
/-- Part (4) of Theorem 19.35: if `E[log ρ₀] = 0` and `E[|log ρ₀|] < ∞`, then for almost every
environment sample `ω`, every realization of the random walk in the fixed environment `W ω`
satisfies `limsup Xₙ = +∞` almost surely under the quenched law. -/
theorem ae_quenched_limsup_eq_top_of_integral_logRatio_eq_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, logρ[W](0) ω ∂μ = 0)
    (hreal :
      ∀ ω,
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix (W ω)) ^ n)
          (P ω) (X ω)) :
    ∀ᵐ ω ∂μ,
      ∀ᵐ ξ ∂(P ω 0 : Measure Ξ),
        limsup (fun n ↦ (((X ω n ξ : ℤ) : ℝ) : EReal)) atTop = ⊤ := by
  -- Proof comment: reuse the recurrent Solomon regime from the zero-mean bridge theorem.
  have hseries :
      ∀ᵐ ω ∂μ,
        R⁻[W ω] = ∞ ∧ R⁺[W ω] = ∞ :=
    ae_leftSeries_eq_top_and_rightSeries_eq_top_of_integral_logRatio_eq_zero hW hlog hmean
  -- Proof comment: the second recurrent conclusion in Theorem 19.33 is the desired quenched
  -- `limsup` statement.
  filter_upwards [hseries, hW.ae_elliptic] with ω hseries hω
  rcases hseries with ⟨hleft, hright⟩
  letI := hreal ω
  simpa using
    (randomEnvironmentWalk_ae_hasLimsupEqPosInfinity
      (W := W ω) (P := P ω) (X := X ω) hω hleft hright)

end Quenched

end ProbabilityTheory
