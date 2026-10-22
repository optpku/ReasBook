/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_43
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_4_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_37

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/-- A probability measure on a countable discrete state space must charge some singleton
positively. -/
private lemma exists_singletonMass_pos [Countable E] (μ : ProbabilityMeasure E) :
    ∃ x : E, 0 < (μ : Measure E) ({x} : Set E) := by
  -- Proof comment: if every singleton had zero mass, the countable singleton decomposition of
  -- `Set.univ` would force the total mass of the probability measure to be `0`.
  by_contra hmass
  have hzero : ∀ x : E, (μ : Measure E) ({x} : Set E) = 0 := by
    intro x
    by_contra hx
    exact hmass ⟨x, bot_lt_iff_ne_bot.mpr hx⟩
  have huniv_zero : (μ : Measure E) Set.univ = 0 := by
    calc
      (μ : Measure E) Set.univ = ∑' x : E, (μ : Measure E) ({x} : Set E) := by
        symm
        simpa using
          (μ : Measure E).tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
      _ = 0 := by
        rw [ENNReal.tsum_eq_zero]
        exact hzero
  have hone : (1 : ℝ≥0∞) = 0 := by
    simp at huniv_zero
  exact one_ne_zero hone

section

variable {κ : ℕ → Kernel E E}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization κ P X]

/-- The positive-time first-return event `{ω | (τ_[X, x]^1) ω < ⊤}` is measurable. -/
private lemma measurableSet_firstReturnTimeFinite
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization κ P X] (x : E) :
    MeasurableSet {ω | (τ_[X, x]^1) ω < ⊤} := by
  -- Proof comment: finiteness of the first return time means the path hits `x` at some time
  -- `n + 1`, so this event is a countable union of measurable singleton fibers.
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
  have hReal : IsMarkovProcessRealization κ P X := inferInstance
  exact
    (hReal.measurable_process n.succ) (measurableSet_singleton x)

/-- Finite expected first return time implies recurrence. -/
private lemma recurrent_of_positiveRecurrentState
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization κ P X] (x : E) (hx : IsPositiveRecurrentState P X x) :
    IsRecurrentState P X x := by
  -- Proof comment: if the complement of the finite-return event had positive mass, the first
  -- return time would integrate to `∞`, contradicting positive recurrence.
  let A : Set Ω := {ω | (τ_[X, x]^1) ω < ⊤}
  have hFirstReturnFinite :
      ∀ y : E, MeasurableSet {ω | (τ_[X, y]^1) ω < ⊤} :=
    fun y ↦ @measurableSet_firstReturnTimeFinite E _ _ Ω _ κ P X inferInstance y
  have hA_meas : MeasurableSet A := by
    simpa [A] using hFirstReturnFinite x
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
          have hτne : ¬ (τ_[X, x]^1) ω ≠ ⊤ := by
            simpa [A, Set.mem_setOf_eq, lt_top_iff_ne_top] using hω
          exact not_not.mp hτne
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
      have hUnion_le :
          (P x : Measure Ω) (A ∪ Aᶜ) ≤ (P x : Measure Ω) A + (P x : Measure Ω) Aᶜ :=
        measure_union_le A Aᶜ
      calc
        1 = (P x : Measure Ω) Set.univ := by simp
        _ ≤ (P x : Measure Ω) A + (P x : Measure Ω) Aᶜ := by
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
  rw [IsRecurrentState, everHitsProbability_def]
  exact (ENNReal.toReal_eq_one_iff _).2 hhit

end

section

variable (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/-- Irreducibility transports positive invariant singleton mass to any target state. -/
private lemma singletonMass_pos_of_mem_invariantDistribution
    [Countable E]
    {μ : ProbabilityMeasure E} {x y : E}
    (hμ : μ ∈ invariantDistributions (discreteMatrixKernel p))
    (hymass : 0 < (μ : Measure E) ({y} : Set E))
    (hyx : 0 < (F[P, X]) y x) :
    0 < (μ : Measure E) ({x} : Set E) := by
  -- Proof comment: positive communication from `y` to `x` yields a positive-time step mass, and
  -- invariance then pushes the positive singleton mass from `y` forward to `x`.
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
    inferInstance
  have hμinv :
      Kernel.Invariant ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) (μ : Measure E) := by
    simpa using (mem_invariantDistributions_iff (discreteMatrixKernel p) μ).1 hμ
  have hstep : ∃ n : ℕ, 0 < n ∧ 0 < ((discreteMatrixKernel p ^ n) y ({x} : Set E)) :=
    existsPosStepMass_of_everHitsProbability_pos hyx
  exact singletonMass_pos_of_invariant_of_posStepMass
    hReal.semigroup hμinv hymass hstep

/-- Positive singleton mass under an invariant distribution yields a recurrent state. -/
private lemma recurrentState_of_mem_invariantDistribution_singleton_pos
    [Countable E]
    {μ : ProbabilityMeasure E} {x : E}
    (hμ : μ ∈ invariantDistributions (discreteMatrixKernel p))
    (hxmass : 0 < (μ : Measure E) ({x} : Set E)) :
    IsRecurrentState P X x := by
  -- Proof comment: convert set membership to kernel invariance, upgrade the positive singleton
  -- mass to positive recurrence using Exercise 17.4.1, then drop to recurrence.
  have hμinv :
      Kernel.Invariant ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) (μ : Measure E) := by
    simpa using (mem_invariantDistributions_iff (discreteMatrixKernel p) μ).1 hμ
  have hxPositive : IsPositiveRecurrentState P X x :=
    isPositiveRecurrentState_of_invariantDistribution_singleton_pos hμinv hxmass
  exact
    @recurrent_of_positiveRecurrentState E _ _ Ω _
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X inferInstance x hxPositive

/-- Every invariant distribution on a countable discrete state space charges some recurrent
state. -/
private lemma existsRecurrentState_of_mem_invariantDistribution [Countable E]
    {μ : ProbabilityMeasure E}
    (hμ : μ ∈ invariantDistributions (discreteMatrixKernel p)) :
    ∃ x : E, IsRecurrentState P X x := by
  -- Proof comment: a countable probability measure has a positive singleton, and the previous
  -- bridge turns that invariant singleton mass into recurrence of the same state.
  obtain ⟨x, hxmass⟩ := exists_singletonMass_pos μ
  exact ⟨x, recurrentState_of_mem_invariantDistribution_singleton_pos p P X hμ hxmass⟩

end

-- Source alignment: the local `source/` directory is unavailable in this workspace, but the
-- runner metadata includes both the extracted theorem text
-- "If any point is transient, then an invariant distribution does not exist." and the source
-- proof sketch. That proof uses the global-transience conclusion `G(x, y) < ∞` for all states,
-- which in the local Chapter 17 API is supplied by Theorem 17.37 from irreducibility together
-- with one transient state. Accordingly, the existential irreducible statement is the labeled
-- source-facing theorem here, while the all-states-transient version remains only as a helper.
-- Semantic recall: `lean_leansearch` surfaced only generic kernel irreducibility owners, with no
-- canonical mathlib theorem for this Chapter 17 transient/invariant-distribution contradiction.
-- Proof sketch: any invariant distribution on the countable state space charges some singleton
-- positively, hence by Exercise 17.4.1 charges a recurrent state. This contradicts the global
-- transient-state hypothesis.
omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- Helper for Theorem 17.46: a recurrent state cannot be transient. -/
private lemma recurrentState_not_transient
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    {x : E} (hx : IsRecurrentState P X x) :
    ¬ IsTransientState P X x := by
  -- Proof comment: recurrence identifies the self-hit probability with `1`, while transience
  -- requires that same probability to be strictly smaller than `1`.
  rw [IsTransientState, hx]
  simp

/-- Helper for Theorem 17.46: under global transience, no invariant distribution can exist. -/
private lemma not_mem_invariantDistribution_of_all_states_transient
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [Countable E]
    {μ : ProbabilityMeasure E}
    (htransient : ∀ x : E, IsTransientState P X x) :
    μ ∉ invariantDistributions (discreteMatrixKernel p) := by
  intro hμ
  -- Proof comment: invariant distributions produce a recurrent state via the singleton-mass
  -- bridge above, contradicting the assumed transient classification of every state.
  rcases existsRecurrentState_of_mem_invariantDistribution (p := p) (P := P) (X := X) hμ with
    ⟨x, hxrec⟩
  exact recurrentState_not_transient hxrec (htransient x)

/-- Helper theorem: on a countable discrete state space, if every state is transient, then the
invariant-distribution set of `discreteMatrixKernel p` is empty. -/
theorem not_exists_invariantDistribution_of_all_states_transient
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [Countable E]
    (htransient : ∀ x : E, IsTransientState P X x) :
    invariantDistributions (discreteMatrixKernel p) = ∅ := by
  -- Proof comment: to show the set is empty, it suffices to rule out membership for an
  -- arbitrary candidate invariant distribution.
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  intro μ hμ
  exact not_mem_invariantDistribution_of_all_states_transient
    (p := p) (P := P) (X := X) htransient hμ

-- Proof sketch: Theorem 17.37 upgrades irreducibility plus one transient state to the global
-- transient regime, then the helper theorem above rules out invariant distributions.
/-- Theorem 17.46: in the irreducible countable-state setting used by the source proof, if some
state is transient, then the invariant-distribution set of `discreteMatrixKernel p` is empty. -/
theorem not_exists_invariantDistribution_of_exists_transientState
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [Countable E]
    (hirr : IsIrreducibleMarkovChain P X)
    (htransient : ∃ x : E, IsTransientState P X x) :
    invariantDistributions (discreteMatrixKernel p) = ∅ := by
  -- Proof comment: Theorem 17.37 splits irreducible chains into the recurrent and transient
  -- regimes; the transient branch is exactly the input required by the helper theorem above.
  rcases irreducibleMarkovChain_recurrent_or_transient (p := p) (P := P) (X := X) hirr with
    hrec | hallTransient
  · rcases htransient with ⟨x, hxtrans⟩
    -- Proof comment: the recurrent branch contradicts the assumed transient witness directly.
    exact False.elim <| recurrentState_not_transient (hrec x) hxtrans
  · exact not_exists_invariantDistribution_of_all_states_transient
      (p := p) (P := P) (X := X) hallTransient

end ProbabilityTheory
