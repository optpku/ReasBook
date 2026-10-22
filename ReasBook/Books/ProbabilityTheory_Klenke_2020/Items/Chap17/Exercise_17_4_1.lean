/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_47

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
variable {κ : ℕ → Kernel E E}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

-- API note: semantic recall points to Mathlib's `Kernel.Invariant`; the Chapter 17 bridge
-- remains local through `Definition_17_33` and `Definition_17_36`, so the direct item imports
-- above are the intended public dependency closure here.
-- Source alignment: Exercise 17.4.1 is a countable discrete-state communication statement.
-- The proof route stays on the textbook Chapter 17 surface: positive recurrence at `x` gives an
-- invariant distribution with positive mass at `{x}`, positive communication transfers that mass
-- to `{y}`, and the remaining closing step is the local Kac inequality at `y`.
section CommunicatingStates

variable [IsMarkovProcessRealization κ P X]
variable {x y : E}

/-- Helper for Exercise 17.4.1: one-step invariance propagates to every time-`n` kernel in the
Markov semigroup. -/
lemma kernelInvariant_nat
    (hκ : IsMarkovSemigroup κ) {ν : Measure E} (hν : Kernel.Invariant (κ 1) ν) :
    ∀ n : ℕ, Kernel.Invariant (κ n) ν
  | 0 => by
      -- Proof comment: the time-zero kernel is the identity kernel from the semigroup axioms.
      simpa [Kernel.Invariant, hκ.zero_eq]
  | n + 1 => by
      have hn : Kernel.Invariant (κ n) ν := kernelInvariant_nat hκ hν n
      -- Proof comment: compose the already-known invariances for `κ n` and `κ 1`.
      simpa [hκ.comp_eq n 1] using hν.comp hn

/-- Helper for Exercise 17.4.1: positive ever-hit probability yields a concrete positive-time
singleton transition mass. -/
lemma existsPosStepMass_of_everHitsProbability_pos
    (hxy : 0 < (F[P, X]) x y) :
    ∃ n : ℕ, 0 < n ∧ 0 < (κ n) x ({y} : Set E) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let hproc : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hgreen : 0 < (G[P, X; 1]) x y :=
    (greenFunctionFrom_one_pos_iff_everHitsProbability_pos P X hproc x y).2 hxy
  -- Proof comment: Definition 17.36 already packages the Green-function-to-step-mass bridge.
  exact existsPosStepMass_of_greenFunctionFrom_one_pos P X hgreen

/-- Helper for Exercise 17.4.1: an invariant measure that charges `{x}` positively also charges
`{y}` positively once some positive-time transition from `x` to `y` has positive mass. -/
lemma singletonMass_pos_of_invariant_of_posStepMass
    (hκ : IsMarkovSemigroup κ)
    {ν : Measure E} (hν : Kernel.Invariant (κ 1) ν) (hxmass : 0 < ν ({x} : Set E))
    (hstep : ∃ n : ℕ, 0 < n ∧ 0 < (κ n) x ({y} : Set E)) :
    0 < ν ({y} : Set E) := by
  rcases hstep with ⟨n, -, hxy⟩
  have hνn : Kernel.Invariant (κ n) ν := kernelInvariant_nat hκ hν n
  have hcomp_eq : ((κ n) ∘ₘ ν) ({y} : Set E) = ν ({y} : Set E) := by
    simpa using congrArg (fun μ : Measure E ↦ μ ({y} : Set E)) hνn.def
  have hsum :
      ((κ n) ∘ₘ ν) ({y} : Set E) =
        ∑' z : E, ν ({z} : Set E) * (κ n) z ({y} : Set E) := by
    rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ (MeasurableSet.singleton y)]
    refine tsum_congr fun z ↦ ?_
    rw [Measure.smul_apply]
    rfl
  have hle :
      ν ({x} : Set E) * (κ n) x ({y} : Set E) ≤ ((κ n) ∘ₘ ν) ({y} : Set E) := by
    rw [hsum]
    exact ENNReal.le_tsum x
  have hprod : 0 < ν ({x} : Set E) * (κ n) x ({y} : Set E) := by
    -- Proof comment: both factors are strictly positive by hypothesis.
    exact ENNReal.mul_pos hxmass.ne' hxy.ne'
  have hcomp_pos : 0 < ((κ n) ∘ₘ ν) ({y} : Set E) := lt_of_lt_of_le hprod hle
  rw [hcomp_eq] at hcomp_pos
  exact hcomp_pos

/-- Helper for Exercise 17.4.1: the first return time is at least one, so its expectation is
strictly positive. -/
lemma one_le_expectedFirstReturnTimeLocal (x : E) :
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

/-- Helper for Exercise 17.4.1: the positive-time first-return event is measurable. -/
lemma measurableSet_firstReturnTimeFiniteLocal
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω}
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

/-- Helper for Exercise 17.4.1: finite expected first return time forces recurrence. -/
lemma positiveRecurrentState_isRecurrentStateLocal
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x : E) (hx : IsPositiveRecurrentState P X x) :
    IsRecurrentState P X x := by
  -- Proof comment: if the complement of the finite-return event had positive mass, the first
  -- return time would dominate an `∞`-valued indicator on a positive-measure set, contradicting
  -- finiteness of the expectation.
  let A : Set Ω := {ω | (τ_[X, x]^1) ω < ⊤}
  have hA_meas : MeasurableSet A :=
    measurableSet_firstReturnTimeFiniteLocal (κ := κ) (P := P) (X := X) x
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

/-- Helper for Exercise 17.4.1: the first return time is at most `n` exactly when `x` is visited
between times `1` and `n`. -/
lemma firstReturnTime_le_iffLocal
    (x : E) (n : ℕ) (ω : Ω) :
    (τ_[X, x]^1) ω ≤ n ↔ ∃ j ∈ Set.Icc 1 n, X j ω = x := by
  simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using
    (hittingAfter_le_iff (u := X) (s := ({x} : Set E)) (n := 1) (ω := ω) (i := n))

/-- Helper for Exercise 17.4.1: the finite-horizon return event `{ω | τ_[X, x]^1 ≤ n}` is
measurable. -/
lemma measurableSet_firstReturnTimeLeLocal
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
    (x : E) (n : ℕ) :
    MeasurableSet {ω | (τ_[X, x]^1) ω ≤ n} := by
  -- Proof comment: rewrite the bounded return-time event as a finite union of singleton fibers
  -- of the coordinates `X j`.
  have hEq :
      {ω | (τ_[X, x]^1) ω ≤ n} =
        ⋃ j ∈ ((Finset.Icc 1 n : Finset ℕ) : Set ℕ), X j ⁻¹' ({x} : Set E) := by
    ext ω
    simp [firstReturnTime_le_iffLocal, Finset.mem_Icc]
  rw [hEq]
  refine MeasurableSet.biUnion (Set.to_countable _) ?_
  intro j hj
  exact
    (IsMarkovProcessRealization.measurable_process (κ := κ) (P := P) (X := X) j)
      (MeasurableSet.singleton x)

/-- Helper for Exercise 17.4.1: the strict tail event `{ω | n < τ_[X, x]^1 ω}` is measurable.
-/
lemma measurableSet_firstReturnTimeTailLocal
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
    (x : E) (n : ℕ) :
    MeasurableSet {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: the strict tail is the complement of the measurable bounded-horizon event.
  have hEq :
      {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} = {ω | (τ_[X, x]^1) ω ≤ n}ᶜ := by
    ext ω
    simp
  rw [hEq]
  exact (measurableSet_firstReturnTimeLeLocal (κ := κ) (P := P) (X := X) x n).compl

/-- Helper for Exercise 17.4.1: the counting measure of the initial segment below `t : ℕ∞`
recovers `t` itself. -/
lemma count_lt_enat_eqLocal (t : ℕ∞) :
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

/-- Helper for Exercise 17.4.1: the pointwise tail-indicator series is the counting measure of the
tail set `{n | n < τ_x^1(ω)}`. -/
lemma tsum_tailIndicators_eq_countTailMassLocal
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

/-- Helper for Exercise 17.4.1: the first return time equals the tail-indicator series of the
events `{ω | n < τ_[X, x]^1 ω}`. -/
lemma firstReturnTime_eq_tsum_tailIndicatorsLocal
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
          exact count_lt_enat_eqLocal ((τ_[X, x]^1) ω)
    _ = ∑' n : ℕ,
          Set.indicator
            {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'} (fun _ ↦ (1 : ℝ≥0∞)) ω := by
          symm
          exact tsum_tailIndicators_eq_countTailMassLocal (X := X) x ω

/-- Helper for Exercise 17.4.1: `𝔼_x[τ_x^1]` is the tail-probability series of the first return
time. -/
lemma expectedFirstReturnTime_eq_tsum_tailProbabilitiesLocal
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
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
            rw [firstReturnTime_eq_tsum_tailIndicatorsLocal (X := X) x ω]
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
                  (measurableSet_firstReturnTimeTailLocal (κ := κ) (P := P) (X := X) x n)
              exact hmeas.aemeasurable
            rw [lintegral_tsum hIndicator_meas]
    _ = ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          refine tsum_congr fun n ↦ ?_
          simpa using
            (lintegral_indicator_one (μ := (P x : Measure Ω))
              (s := {ω | (n : ℕ∞) < (τ_[X, x]^1) ω})
              (measurableSet_firstReturnTimeTailLocal (κ := κ) (P := P) (X := X) x n))

/-- Helper for Exercise 17.4.1: the raw excursion occupation mass before the first positive
return to `x`. -/
private def returnCycleOccupationMassLocal
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x y : E) : ℝ≥0∞ :=
  ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}

/-- Helper for Exercise 17.4.1: the corresponding discrete-state excursion occupation measure. -/
private def returnCycleOccupationMeasureLocal
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : Measure E :=
  Measure.count.withDensity (returnCycleOccupationMassLocal P X x)

/-- Helper for Exercise 17.4.1: evaluating the local excursion measure on a singleton recovers
its density. -/
private lemma returnCycleOccupationMeasureLocal_apply_singleton
    (x y : E) :
    returnCycleOccupationMeasureLocal P X x ({y} : Set E) =
      returnCycleOccupationMassLocal P X x y := by
  -- Proof comment: on the discrete state space, `withDensity` over counting measure evaluates to
  -- the density on singleton sets.
  rw [returnCycleOccupationMeasureLocal, withDensity_apply _ (MeasurableSet.singleton y)]
  simp [returnCycleOccupationMassLocal]

/-- Helper for Exercise 17.4.1: summing the fixed-time state slices over all states collapses to
the tail event `n < τ_[X, x]^1`. -/
private lemma tsum_stateSliceProbabilities_eq_tailProbabilityLocal
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    (x : E) (n : ℕ) :
    ∑' y : E, (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} =
      (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  classical
  let A : Set Ω := {ω | (n : ℕ∞) < (τ_[X, x]^1) ω}
  have hA_meas : MeasurableSet A :=
    measurableSet_firstReturnTimeTailLocal (κ := κ) (P := P) (X := X) x n
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

/-- Helper for Exercise 17.4.1: the total raw excursion occupation mass equals the first-return
tail-probability series. -/
private lemma tsum_returnCycleOccupationMassLocal_eq_tsum_tailProbabilitiesLocal
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    (x : E) :
    ∑' y : E, returnCycleOccupationMassLocal P X x y =
      ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: rewrite the outer state sum as a count integral, commute it past the time
  -- series, and collapse each fixed-time slice with the previous helper.
  calc
    ∑' y : E, returnCycleOccupationMassLocal P X x y
      = ∫⁻ y, returnCycleOccupationMassLocal P X x y ∂Measure.count := by
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
          exact tsum_stateSliceProbabilities_eq_tailProbabilityLocal
            (P := P) (X := X) (κ := κ) x n

/-- Helper for Exercise 17.4.1: the total mass of the local excursion measure is
`𝔼_x[τ_x^1]`. -/
private lemma returnCycleOccupationMeasureLocal_univ_eq_expectedFirstReturnTime
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    (x : E) :
    returnCycleOccupationMeasureLocal P X x Set.univ = expectedFirstReturnTime P X x := by
  -- Proof comment: evaluate `withDensity` on `Set.univ`, rewrite the count integral as a series,
  -- and identify that series with the first-return tail expansion.
  calc
    returnCycleOccupationMeasureLocal P X x Set.univ
      = ∫⁻ y, returnCycleOccupationMassLocal P X x y ∂Measure.count := by
          rw [returnCycleOccupationMeasureLocal, withDensity_apply _ MeasurableSet.univ,
            Measure.restrict_univ]
    _ = ∑' y : E, returnCycleOccupationMassLocal P X x y := by
          rw [lintegral_count]
    _ = ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          rw [tsum_returnCycleOccupationMassLocal_eq_tsum_tailProbabilitiesLocal
            (P := P) (X := X) (κ := κ) x]
    _ = expectedFirstReturnTime P X x := by
          symm
          exact expectedFirstReturnTime_eq_tsum_tailProbabilitiesLocal
            (P := P) (X := X) (κ := κ) x

/-- Helper for Exercise 17.4.1: positive recurrence normalizes the local excursion measure to a
probability measure. -/
private lemma isProbabilityMeasure_smul_returnCycleOccupationMeasureLocal
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    (x : E) (hx : IsPositiveRecurrentState P X x) :
    IsProbabilityMeasure
      ((expectedFirstReturnTime P X x)⁻¹ • returnCycleOccupationMeasureLocal P X x) := by
  have hmass :
      returnCycleOccupationMeasureLocal P X x Set.univ = expectedFirstReturnTime P X x :=
    returnCycleOccupationMeasureLocal_univ_eq_expectedFirstReturnTime
      (P := P) (X := X) (κ := κ) x
  have hmass_ne_zero : returnCycleOccupationMeasureLocal P X x Set.univ ≠ 0 := by
    have hpos :
        0 < expectedFirstReturnTime P X x := by
      exact lt_of_lt_of_le zero_lt_one
        (one_le_expectedFirstReturnTimeLocal (P := P) (X := X) x)
    rw [hmass]
    exact ne_of_gt hpos
  -- Proof comment: the total mass is finite and nonzero, so scaling by its inverse makes the
  -- total mass exactly `1`.
  refine isProbabilityMeasure_iff.2 ?_
  rw [Measure.smul_apply, hmass]
  exact ENNReal.inv_mul_cancel (by simpa [hmass] using hmass_ne_zero) (ne_of_lt hx)

/-- Helper for Exercise 17.4.1: the normalized local excursion law is the concrete candidate
distribution attached to a positive recurrent state. -/
private def positiveRecurrentInvariantDistributionCandidateLocal
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    (x : E) (hx : IsPositiveRecurrentState P X x) : ProbabilityMeasure E :=
  ⟨(expectedFirstReturnTime P X x)⁻¹ • returnCycleOccupationMeasureLocal P X x,
    isProbabilityMeasure_smul_returnCycleOccupationMeasureLocal
      (P := P) (X := X) (κ := κ) x hx⟩

/-- Helper for Exercise 17.4.1: the local excursion measure always charges the starting state
positively. -/
private lemma returnCycleOccupationMeasureLocal_selfMass_pos
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    (x : E) :
    0 < returnCycleOccupationMeasureLocal P X x ({x} : Set E) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hinit :
      (P x : Measure Ω) {ω | X 0 ω = x} = 1 := by
    have hpreimage : {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set E) := by
      ext ω
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x)]
    rw [hReal.initial_eq x]
    simp
  have hterm_eq_one :
      (P x : Measure Ω) {ω | X 0 ω = x ∧ (0 : ℕ∞) < (τ_[X, x]^1) ω} = 1 := by
    have hτpos : ∀ ω : Ω, (0 : ℕ∞) < (τ_[X, x]^1) ω := by
      intro ω
      have hτge1 : (1 : ℕ∞) ≤ (τ_[X, x]^1) ω := by
        simpa [iteratedEntranceTime_one] using
          (le_hittingAfter (u := X) (s := ({x} : Set E)) (n := 1) ω)
      exact lt_of_lt_of_le (by simp) hτge1
    have hEq :
        {ω | X 0 ω = x ∧ (0 : ℕ∞) < (τ_[X, x]^1) ω} = {ω | X 0 ω = x} := by
      ext ω
      constructor
      · intro hω
        exact hω.1
      · intro hω
        exact ⟨hω, hτpos ω⟩
    rw [hEq]
    exact hinit
  have hterm_le :
      (P x : Measure Ω) {ω | X 0 ω = x ∧ (0 : ℕ∞) < (τ_[X, x]^1) ω} ≤
        returnCycleOccupationMassLocal P X x x := by
    simpa [returnCycleOccupationMassLocal] using (ENNReal.le_tsum (0 : ℕ))
  -- Proof comment: the `n = 0` term already contributes mass `1`, so the singleton mass at `x`
  -- is automatically positive.
  rw [returnCycleOccupationMeasureLocal_apply_singleton]
  exact lt_of_lt_of_le (by simpa [hterm_eq_one] using zero_lt_one) hterm_le

/-- Helper for Exercise 17.4.1: the normalized local excursion candidate still charges the base
state positively. -/
private lemma positiveRecurrentInvariantDistributionCandidateLocal_selfMass_pos
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    (x : E) (hx : IsPositiveRecurrentState P X x) :
    0 <
      (positiveRecurrentInvariantDistributionCandidateLocal
        (P := P) (X := X) (κ := κ) x hx : Measure E) ({x} : Set E) := by
  have hraw_pos :
      0 < returnCycleOccupationMeasureLocal P X x ({x} : Set E) :=
    returnCycleOccupationMeasureLocal_selfMass_pos (P := P) (X := X) (κ := κ) x
  have hinv_pos : 0 < (expectedFirstReturnTime P X x)⁻¹ := by
    exact (ENNReal.inv_pos).2 (ne_of_lt hx)
  -- Proof comment: the normalization factor is positive because the expected first return time is
  -- bounded below by `1`.
  change 0 <
    (((expectedFirstReturnTime P X x)⁻¹ • returnCycleOccupationMeasureLocal P X x)
      ({x} : Set E))
  rw [Measure.smul_apply]
  exact ENNReal.mul_pos hinv_pos.ne' hraw_pos.ne'

omit [DiscreteMeasurableSpace E] in
/-- Helper for Exercise 17.4.1: scaling preserves kernel invariance of a measure. -/
private lemma kernelInvariant_smulLocal {μ : Measure E} {a : ℝ≥0∞}
    (hμ : Kernel.Invariant (κ 1) μ) :
    Kernel.Invariant (κ 1) (a • μ) := by
  -- Proof comment: `Measure.bind` is linear in the measure argument, so the invariance equation
  -- scales on both sides.
  rw [Kernel.Invariant] at hμ ⊢
  calc
    (a • μ).bind (κ 1) = a • (μ.bind (κ 1)) := Measure.bind_smul a μ (κ 1)
    _ = a • μ := by rw [hμ]

/-- Helper for Exercise 17.4.1: if a time-`n` history event already forces `X n = y`, then
intersecting it with a deterministic future singleton event factors through the `m`-step
transition mass from `y`. -/
private lemma measure_inter_prefix_stepEvent_eq_mulLocal
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
    {x y z : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
      ((κ m) y ({z} : Set E)).toReal * (P x : Measure Ω).real A := by
  let μ : Measure Ω := P x
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let B : Set Ω := X (n + m) ⁻¹' ({z} : Set E)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + m)) (MeasurableSet.singleton z)
  have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun k hk ↦ ?_
    exact (hReal.measurable_process k).comap_le
  have hA_measAmbient : MeasurableSet A := by
    -- Proof comment: the generated history filtration sits inside the ambient measurable space.
    dsimp [LE.le] at hFiltration_le
    exact hFiltration_le (s := A) hA_meas
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ ((κ m) (X n ω)).real ({z} : Set E) := by
    simpa [μ, B, add_comm] using
      hReal.markov_property x (A := ({z} : Set E)) (MeasurableSet.singleton z) n m
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  -- Proof comment: integrate the Markov conditional-expectation identity over `A`, then freeze
  -- the future law at `y` because `A` already pins down the state at time `n`.
  calc
    μ.real (A ∩ {ω | X (n + m) ω = z}) =
        ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
          rw [setIntegral_condExp hFiltration_le hIndicatorIntegrable hA_meas,
            ← integral_indicator hA_measAmbient]
          symm
          simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
            smul_eq_mul] using integral_indicator_const (1 : ℝ) (hA_measAmbient.inter hB_meas)
    _ = ∫ ω in A, ((κ m) (X n ω)).real ({z} : Set E) ∂ μ := by
          exact integral_congr_ae hMarkovGenerated.restrict
    _ = ∫ _ in A, ((κ m) y ({z} : Set E)).toReal ∂ μ := by
          refine integral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient] with ω hω
          have hω : X n ω = y := hA_sub hω
          rw [hω]
          simp [Measure.real_def]
    _ = ((κ m) y ({z} : Set E)).toReal * μ.real A := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- Helper for Exercise 17.4.1: the deterministic-time prefix factorization is cleaner in raw
`Measure` (`ℝ≥0∞`) form. -/
private lemma measure_inter_prefix_stepEvent_eq_mul_ennrealLocal
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
    {x y z : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
      ((κ m) y ({z} : Set E)) * (P x : Measure Ω) A := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let _ : IsMarkovKernel (κ m) := hReal.semigroup.isMarkovKernel m
  have hstep :
      (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
        ((κ m) y ({z} : Set E)).toReal * (P x : Measure Ω).real A :=
    measure_inter_prefix_stepEvent_eq_mulLocal
      (P := P) (X := X) (κ := κ) hA_meas hA_sub
  have hleft_ne_top :
      (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) ≠ ⊤ :=
    measure_ne_top _ _
  have hkernel_ne_top : ((κ m) y) ({z} : Set E) ≠ ⊤ :=
    measure_ne_top _ _
  have hA_ne_top : (P x : Measure Ω) A ≠ ⊤ :=
    measure_ne_top _ _
  -- Proof comment: compare the two finite ENNReal masses by converting the real-valued identity
  -- back with `ENNReal.ofReal`.
  calc
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
        ENNReal.ofReal ((P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z})) := by
          symm
          exact ENNReal.ofReal_toReal hleft_ne_top
    _ = ENNReal.ofReal (((κ m) y ({z} : Set E)).toReal * (P x : Measure Ω).real A) := by
          rw [hstep]
    _ = ((κ m) y ({z} : Set E)) * (P x : Measure Ω) A := by
          rw [ENNReal.ofReal_mul]
          · rw [ENNReal.ofReal_toReal hkernel_ne_top]
            change ((κ m) y ({z} : Set E)) * ENNReal.ofReal (((P x : Measure Ω) A).toReal) =
                ((κ m) y ({z} : Set E)) * (P x : Measure Ω) A
            rw [ENNReal.ofReal_toReal hA_ne_top]
          · positivity

/-- Helper for Exercise 17.4.1: the generated history filtration grows with time. -/
private lemma generatedFiltrationSpace_monoLocal
    (Y : ℕ → Ω → E) {s t : ℕ} (hst : s ≤ t) :
    generatedFiltrationSpace Y s ≤ generatedFiltrationSpace Y t := by
  refine iSup₂_le fun r hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hst) le_rfl

/-- Helper for Exercise 17.4.1: `futurePrefixEventLocal X n f` fixes a finite future path after
time `n`. -/
private def futurePrefixEventLocal (Y : ℕ → Ω → E) (n : ℕ) {M : ℕ}
    (f : Fin (M + 1) → E) : Set Ω :=
  {ω | ∀ i : Fin (M + 1), Y (n + (i : ℕ)) ω = f i}

/-- Helper for Exercise 17.4.1: a finite future-prefix event is measurable in the ambient space.
-/
private lemma measurableSet_futurePrefixEventLocal
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
    {M n : ℕ} (f : Fin (M + 1) → E) :
    MeasurableSet (futurePrefixEventLocal X n f) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hEq :
      futurePrefixEventLocal X n f = ⋂ i : Fin (M + 1), {ω | X (n + (i : ℕ)) ω = f i} := by
    ext ω
    simp [futurePrefixEventLocal]
  rw [hEq]
  refine MeasurableSet.iInter fun i ↦ ?_
  simpa [Set.preimage] using
    (hReal.measurable_process (n + (i : ℕ))) (MeasurableSet.singleton (f i))

/-- Helper for Exercise 17.4.1: a finite future-prefix event is measurable with respect to the
history filtration at its terminal time. -/
private lemma measurableSet_futurePrefixEvent_generatedLocal
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
    {M n : ℕ} (f : Fin (M + 1) → E) :
    MeasurableSet[generatedFiltrationSpace X (n + M)] (futurePrefixEventLocal X n f) := by
  have hEq :
      futurePrefixEventLocal X n f = ⋂ i : Fin (M + 1), {ω | X (n + (i : ℕ)) ω = f i} := by
    ext ω
    simp [futurePrefixEventLocal]
  rw [hEq]
  refine MeasurableSet.iInter fun i ↦ ?_
  have hXi : Measurable[generatedFiltrationSpace X (n + M)] (X (n + (i : ℕ))) := by
    refine Measurable.of_comap_le ?_
    exact
      le_iSup_of_le (n + (i : ℕ)) <|
        le_iSup_of_le (Nat.add_le_add_left (Nat.le_of_lt_succ i.2) n) le_rfl
  simpa [Set.preimage] using hXi (MeasurableSet.singleton (f i))

/-- Helper for Exercise 17.4.1: `noHitHorizonLocal X y n M` records that the path avoids `y`
during the next `M` strictly positive times after time `n`. -/
def noHitHorizonLocal (Y : ℕ → Ω → E) (y : E) (n M : ℕ) : Set Ω :=
  {ω | ∀ m : ℕ, 1 ≤ m → m ≤ M → Y (n + m) ω ≠ y}

/-- Helper for Exercise 17.4.1: finite-horizon no-hit events are measurable. -/
private lemma measurableSet_noHitHorizonLocal
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
    (x : E) (n M : ℕ) :
    MeasurableSet (noHitHorizonLocal X x n M) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hEq :
      noHitHorizonLocal X x n M =
        ⋂ m ∈ Finset.Icc 1 M, {ω | X (n + m) ω ≠ x} := by
    ext ω
    simp [noHitHorizonLocal]
  rw [hEq]
  refine MeasurableSet.iInter fun m ↦ ?_
  refine MeasurableSet.iInter fun _hm ↦ ?_
  exact ((hReal.measurable_process (n + m)) (MeasurableSet.singleton x)).compl

/-- Helper for Exercise 17.4.1: at horizon `0`, an exact future-prefix event is just the current
state event. -/
private lemma futurePrefixEvent_zero_eq_stateEventLocal
    (Y : ℕ → Ω → E) (n : ℕ) (f : Fin 1 → E) :
    futurePrefixEventLocal Y n f = {ω | Y n ω = f 0} := by
  ext ω
  simp [futurePrefixEventLocal]

/-- Helper for Exercise 17.4.1: a longer exact future-prefix event splits into its shorter prefix
and terminal one-step event. -/
private lemma futurePrefixEvent_succ_eqLocal
    (Y : ℕ → Ω → E) {M n : ℕ} (f : Fin (M + 2) → E) :
    futurePrefixEventLocal Y n f =
      futurePrefixEventLocal Y n (fun i : Fin (M + 1) ↦ f i.castSucc) ∩
        {ω | Y (n + (M + 1)) ω = f (Fin.last (M + 1))} := by
  ext ω
  constructor
  · intro hω
    refine ⟨?_, ?_⟩
    · intro i
      simpa [futurePrefixEventLocal] using hω i.castSucc
    · simpa [futurePrefixEventLocal] using hω (Fin.last (M + 1))
  · rintro ⟨hωPrefix, hωLast⟩
    intro i
    by_cases hi : i = Fin.last (M + 1)
    · subst hi
      simpa [futurePrefixEventLocal] using hωLast
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      simpa [futurePrefixEventLocal] using hωPrefix j

/-- Helper for Exercise 17.4.1: an exact future-prefix event determines its terminal state. -/
private lemma futurePrefixEvent_terminal_subsetLocal
    (Y : ℕ → Ω → E) {M n : ℕ} (f : Fin (M + 1) → E) :
    futurePrefixEventLocal Y n f ⊆ {ω | Y (n + M) ω = f (Fin.last M)} := by
  intro ω hω
  simpa [futurePrefixEventLocal] using hω (Fin.last M)

/-- Helper for Exercise 17.4.1: once a history event pins down the state at time `n`,
intersecting it with a finite exact future path factors through the path law started from that
state. -/
private lemma measure_inter_prefix_futurePrefixEvent_eq_mulLocal
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
    {x y : E} {A : Set Ω} {n M : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y})
    (f : Fin (M + 1) → E) :
    (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) =
      (P y : Measure Ω) (futurePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
  classical
  induction M with
  | zero =>
      let hReal : IsMarkovProcessRealization κ P X := inferInstance
      have hright_eval :
          (P y : Measure Ω) (futurePrefixEventLocal X 0 f) = if f 0 = y then 1 else 0 := by
        rw [futurePrefixEvent_zero_eq_stateEventLocal (Y := X) (n := 0) f]
        have hpreimage : {ω | X 0 ω = f 0} = X 0 ⁻¹' ({f 0} : Set E) := by
          ext ω
          simp
        rw [hpreimage]
        rw [← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton (f 0))]
        rw [hReal.initial_eq y]
        by_cases hf0 : f 0 = y <;> simp [hf0]
      by_cases hf0 : f 0 = y
      · have hleft_eq : A ∩ futurePrefixEventLocal X n f = A := by
          ext ω
          constructor
          · intro hω
            exact hω.1
          · intro hω
            refine ⟨hω, ?_⟩
            rw [futurePrefixEvent_zero_eq_stateEventLocal (Y := X) (n := n) f]
            simpa [hf0] using hA_sub hω
        calc
          (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) = (P x : Measure Ω) A := by
            rw [hleft_eq]
          _ = 1 * (P x : Measure Ω) A := by rw [one_mul]
          _ = (P y : Measure Ω) (futurePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
            rw [hright_eval, if_pos hf0]
      · have hleft_eq : A ∩ futurePrefixEventLocal X n f = ∅ := by
          ext ω
          constructor
          · rintro ⟨hωA, hωf⟩
            rw [futurePrefixEvent_zero_eq_stateEventLocal (Y := X) (n := n) f] at hωf
            exact hf0 (hωf.symm.trans (hA_sub hωA))
          · intro hω
            exact False.elim (by simpa using hω)
        calc
          (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) = 0 := by
            simp [hleft_eq]
          _ = (P y : Measure Ω) (futurePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
            rw [hright_eval, if_neg hf0]
            simp
  | succ M ih =>
      let g : Fin (M + 1) → E := fun i ↦ f i.castSucc
      let B : Set Ω := A ∩ futurePrefixEventLocal X n g
      have hA_meas_big : MeasurableSet[generatedFiltrationSpace X (n + M)] A := by
        let hmono :
            generatedFiltrationSpace X n ≤ generatedFiltrationSpace X (n + M) :=
          generatedFiltrationSpace_monoLocal
            (Y := X) (s := n) (t := n + M) (hst := Nat.le_add_right n M)
        exact hmono (s := A) hA_meas
      have hB_meas : MeasurableSet[generatedFiltrationSpace X (n + M)] B := by
        exact hA_meas_big.inter
          (measurableSet_futurePrefixEvent_generatedLocal
            (P := P) (X := X) (κ := κ) (n := n) g)
      have hB_sub : B ⊆ {ω | X (n + M) ω = g (Fin.last M)} := by
        intro ω hω
        exact futurePrefixEvent_terminal_subsetLocal (Y := X) (n := n) g hω.2
      have hleft_step :
          (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) =
            ((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
              (P x : Measure Ω) B := by
        calc
          (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) =
              (P x : Measure Ω)
                (B ∩ {ω | X ((n + M) + 1) ω = f (Fin.last (M + 1))}) := by
                  simp [B, g, futurePrefixEvent_succ_eqLocal, Nat.add_assoc, Set.inter_assoc,
                    Set.inter_left_comm, Set.inter_comm]
          _ =
              ((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
                (P x : Measure Ω) B := by
                  simpa [B] using
                    measure_inter_prefix_stepEvent_eq_mul_ennrealLocal
                      (P := P) (X := X) (κ := κ)
                      (x := x) (y := g (Fin.last M)) (z := f (Fin.last (M + 1)))
                      (A := B) (n := n + M) (m := 1) hB_meas hB_sub
      have hg_meas :
          MeasurableSet[generatedFiltrationSpace X M] (futurePrefixEventLocal X 0 g) := by
        have htmp :
            MeasurableSet[generatedFiltrationSpace X (0 + M)] (futurePrefixEventLocal X 0 g) :=
          measurableSet_futurePrefixEvent_generatedLocal
            (P := P) (X := X) (κ := κ) (n := 0) g
        convert htmp using 1 <;> simp [zero_add]
      have hg_sub : futurePrefixEventLocal X 0 g ⊆ {ω | X M ω = g (Fin.last M)} := by
        have htmp :
            futurePrefixEventLocal X 0 g ⊆ {ω | X (0 + M) ω = g (Fin.last M)} :=
          futurePrefixEvent_terminal_subsetLocal (Y := X) (n := 0) g
        simpa [zero_add] using htmp
      have hright_step :
          (P y : Measure Ω) (futurePrefixEventLocal X 0 f) =
            ((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
              (P y : Measure Ω) (futurePrefixEventLocal X 0 g) := by
        calc
          (P y : Measure Ω) (futurePrefixEventLocal X 0 f) =
              (P y : Measure Ω)
                (futurePrefixEventLocal X 0 g ∩
                  {ω | X (M + 1) ω = f (Fin.last (M + 1))}) := by
                  simp [g, futurePrefixEvent_succ_eqLocal, Nat.add_assoc, Set.inter_assoc,
                    Set.inter_left_comm, Set.inter_comm]
          _ =
              ((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
                (P y : Measure Ω) (futurePrefixEventLocal X 0 g) := by
                  simpa using
                    measure_inter_prefix_stepEvent_eq_mul_ennrealLocal
                      (P := P) (X := X) (κ := κ)
                      (x := y) (y := g (Fin.last M)) (z := f (Fin.last (M + 1)))
                      (A := futurePrefixEventLocal X 0 g) (n := M) (m := 1) hg_meas hg_sub
      -- Proof comment: split off the last coordinate of the future path and reuse the induction
      -- hypothesis on the shorter prefix.
      calc
        (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) =
            ((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
              (P x : Measure Ω) B := hleft_step
        _ =
            ((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
              ((P y : Measure Ω) (futurePrefixEventLocal X 0 g) * (P x : Measure Ω) A) := by
                rw [ih g]
        _ =
            (((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
              (P y : Measure Ω) (futurePrefixEventLocal X 0 g)) * (P x : Measure Ω) A := by
                rw [mul_assoc]
        _ = (P y : Measure Ω) (futurePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
                rw [hright_step]

/-- Helper for Exercise 17.4.1: finite-horizon no-hit events factor against a history event that
already fixes the current state. -/
lemma measure_inter_prefix_noHitHorizon_eq_mulLocal
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
    {x y : E} {A : Set Ω} {n M : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ noHitHorizonLocal X y n M) =
      (P y : Measure Ω) (noHitHorizonLocal X y 0 M) * (P x : Measure Ω) A := by
  classical
  let μx : Measure Ω := P x
  let T : Type v := {f : Fin (M + 1) → E // ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ y}
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hA_ambient : MeasurableSet A := by
    have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
      refine iSup₂_le fun k hk ↦ ?_
      exact (hReal.measurable_process k).comap_le
    exact hFiltration_le (s := A) hA_meas
  have hleft_union :
      A ∩ noHitHorizonLocal X y n M = ⋃ f : T, A ∩ futurePrefixEventLocal X n f.1 := by
    ext ω
    constructor
    · rintro ⟨hωA, hωNoHit⟩
      let f : Fin (M + 1) → E := fun i ↦ X (n + (i : ℕ)) ω
      have hf : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ y := by
        intro i hi
        exact hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
      refine Set.mem_iUnion.mpr ?_
      refine ⟨⟨f, hf⟩, ?_⟩
      refine ⟨hωA, ?_⟩
      intro i
      rfl
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨f, hωf⟩
      refine ⟨hωf.1, ?_⟩
      intro m hm hmM
      let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
      have hpath : X (n + m) ω = f.1 i := by
        simpa [futurePrefixEventLocal, i] using hωf.2 i
      exact hpath.trans_ne (f.2 i hm)
  have hright_union :
      noHitHorizonLocal X y 0 M = ⋃ f : T, futurePrefixEventLocal X 0 f.1 := by
    ext ω
    constructor
    · intro hωNoHit
      let f : Fin (M + 1) → E := fun i ↦ X (i : ℕ) ω
      have hf : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ y := by
        intro i hi
        simpa [f, zero_add] using hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
      refine Set.mem_iUnion.mpr ?_
      refine ⟨⟨f, hf⟩, ?_⟩
      intro i
      simp [f, zero_add]
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨f, hωf⟩
      intro m hm hmM
      let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
      have hpath : X (0 + m) ω = f.1 i := by
        simpa [futurePrefixEventLocal, i, zero_add] using hωf i
      exact hpath.trans_ne (f.2 i hm)
  have hpairwise_left :
      Pairwise (fun f g : T ↦ Disjoint (A ∩ futurePrefixEventLocal X n f.1)
        (A ∩ futurePrefixEventLocal X n g.1)) := by
    intro f g hfg
    refine Set.disjoint_left.2 ?_
    intro ω hωf hωg
    have hEq : f.1 = g.1 := by
      funext i
      exact (hωf.2 i).symm.trans (hωg.2 i)
    exact hfg (Subtype.ext hEq)
  have hpairwise_right :
      Pairwise (fun f g : T ↦ Disjoint (futurePrefixEventLocal X 0 f.1)
        (futurePrefixEventLocal X 0 g.1)) := by
    intro f g hfg
    refine Set.disjoint_left.2 ?_
    intro ω hωf hωg
    have hEq : f.1 = g.1 := by
      funext i
      exact (hωf i).symm.trans (hωg i)
    exact hfg (Subtype.ext hEq)
  have hleft_sum :
      μx (A ∩ noHitHorizonLocal X y n M) =
        ∑' f : T, μx (A ∩ futurePrefixEventLocal X n f.1) := by
    rw [hleft_union, measure_iUnion hpairwise_left]
    intro f
    exact hA_ambient.inter
      (measurableSet_futurePrefixEventLocal (P := P) (X := X) (κ := κ) (n := n) f.1)
  have hright_sum :
      (P y : Measure Ω) (noHitHorizonLocal X y 0 M) =
        ∑' f : T, (P y : Measure Ω) (futurePrefixEventLocal X 0 f.1) := by
    rw [hright_union, measure_iUnion hpairwise_right]
    intro f
    exact measurableSet_futurePrefixEventLocal (P := P) (X := X) (κ := κ) (n := 0) f.1
  -- Proof comment: partition the no-hit event by the entire future path over the finite horizon,
  -- then factor each cylinder set using the exact future-prefix lemma.
  calc
    μx (A ∩ noHitHorizonLocal X y n M) =
        ∑' f : T, μx (A ∩ futurePrefixEventLocal X n f.1) := hleft_sum
    _ = ∑' f : T, (P y : Measure Ω) (futurePrefixEventLocal X 0 f.1) * μx A := by
          refine tsum_congr fun f ↦ ?_
          exact measure_inter_prefix_futurePrefixEvent_eq_mulLocal
            (P := P) (X := X) (κ := κ) hA_meas hA_sub f.1
    _ = (∑' f : T, (P y : Measure Ω) (futurePrefixEventLocal X 0 f.1)) * μx A := by
          rw [ENNReal.tsum_mul_right]
    _ = (P y : Measure Ω) (noHitHorizonLocal X y 0 M) * μx A := by
          rw [← hright_sum]

/-- Helper for Exercise 17.4.1: a zero-based no-hit horizon is exactly the tail event of the
first positive return time. -/
private lemma noHitHorizon_zero_eq_firstReturnTailLocal
    (y : E) (M : ℕ) :
    noHitHorizonLocal X y 0 M = {ω | (M : ℕ∞) < (τ_[X, y]^1) ω} := by
  -- Proof comment: failing to hit `y` during the first `M` positive times is equivalent to saying
  -- that no visit to `y` occurs in the interval `1, …, M`, which is the same as `τ_y^1 > M`.
  ext ω
  constructor
  · intro hω
    change (M : ℕ∞) < (τ_[X, y]^1) ω
    by_contra hle
    have hle' : (τ_[X, y]^1) ω ≤ M := le_of_not_gt hle
    rcases (firstReturnTime_le_iffLocal (X := X) y M ω).1 hle' with ⟨j, hj, hjEq⟩
    exact hω j hj.1 hj.2 (by simpa [zero_add] using hjEq)
  · intro hω
    intro m hm1 hmM hmEq
    have hle : (τ_[X, y]^1) ω ≤ M :=
      (firstReturnTime_le_iffLocal (X := X) y M ω).2 ⟨m, ⟨hm1, hmM⟩, by simpa [zero_add] using hmEq⟩
    exact not_lt_of_ge hle hω

/-- Helper for Exercise 17.4.1: under a stationary start law, the finite no-hit window sum is
bounded by `1`. -/
private lemma stationaryNoHitWindowBoundLocal
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (κ 1) (π : Measure E))
    (y : E) (M : ℕ) :
    ((π : Measure E) ({y} : Set E)) *
      (Finset.sum (Finset.range (M + 1))
        (fun k ↦ (P y : Measure Ω) (noHitHorizonLocal X y 0 k))) ≤ 1 := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let μ : Measure Ω := ((Kernel.ofFunOfCountable fun z ↦ (P z : Measure Ω)) ∘ₘ (π : Measure E))
  let W : ℕ → Set Ω := fun k ↦ {ω | X k ω = y} ∩ noHitHorizonLocal X y k (M - k)
  let U : Set Ω := ⋃ k ∈ Finset.range (M + 1), W k
  letI : IsMarkovKernel (Kernel.ofFunOfCountable fun z ↦ (P z : Measure Ω)) := by
    refine ⟨?_⟩
    intro z
    change IsProbabilityMeasure (P z : Measure Ω)
    infer_instance
  have hμ_univ : μ Set.univ = 1 := by
    -- Proof comment: the stationary mixture starts from a probability law and uses a Markov
    -- kernel of probability measures, so its total mass is still `1`.
    change (((Kernel.ofFunOfCountable fun z ↦ (P z : Measure Ω)) ∘ₘ (π : Measure E)) Set.univ) = 1
    rw [Measure.comp_apply_univ]
    simp
  have hW_meas : ∀ k ∈ Finset.range (M + 1), MeasurableSet (W k) := by
    intro k hk
    have hstate : MeasurableSet {ω | X k ω = y} := by
      simpa [Set.preimage] using
        (hReal.measurable_process k) (MeasurableSet.singleton y)
    exact hstate.inter
      (measurableSet_noHitHorizonLocal (κ := κ) (P := P) (X := X) y k (M - k))
  have hW_disj : (↑(Finset.range (M + 1)) : Set ℕ).PairwiseDisjoint W := by
    intro i hi j hj hij
    refine Set.disjoint_left.2 ?_
    intro ω hωi hωj
    rcases hωi with ⟨hXi, hNoHit_i⟩
    rcases hωj with ⟨hXj, hNoHit_j⟩
    rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
    · have hXj_ne : X j ω ≠ y := by
        have hstep :=
          hNoHit_i (j - i)
            (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hij_lt))
            (Nat.sub_le_sub_right (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) i)
        simpa [Nat.add_sub_of_le (Nat.le_of_lt hij_lt)] using hstep
      exact hXj_ne hXj
    · have hXi_ne : X i ω ≠ y := by
        have hstep :=
          hNoHit_j (i - j)
            (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hji_lt))
            (Nat.sub_le_sub_right (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) j)
        simpa [Nat.add_sub_of_le (Nat.le_of_lt hji_lt)] using hstep
      exact hXi_ne hXi
  have hWindowMass :
      ∀ k ∈ Finset.range (M + 1),
        μ (W k) =
          ((π : Measure E) ({y} : Set E)) *
            (P y : Measure Ω) (noHitHorizonLocal X y 0 (M - k)) := by
    intro k hk
    let A : Set Ω := {ω | X k ω = y}
    have hA_meas : MeasurableSet[generatedFiltrationSpace X k] A := by
      let f : Fin 1 → E := fun _ ↦ y
      have hprefix :
          MeasurableSet[generatedFiltrationSpace X (k + 0)] (futurePrefixEventLocal X k f) :=
        measurableSet_futurePrefixEvent_generatedLocal
          (κ := κ) (P := P) (X := X) (n := k) f
      simpa [A, futurePrefixEvent_zero_eq_stateEventLocal (Y := X) (n := k) f] using hprefix
    have hA_sub : A ⊆ {ω | X k ω = y} := by
      intro ω hω
      exact hω
    have hstateMass :
        ∀ z : E, (P z : Measure Ω) A = (κ k) z ({y} : Set E) := by
      intro z
      have hpreimage : A = X k ⁻¹' ({y} : Set E) := by
        ext ω
        simp [A]
      rw [hpreimage, ← Measure.map_apply (hReal.measurable_process k) (MeasurableSet.singleton y)]
      simpa using congrArg (fun ν : Measure E ↦ ν ({y} : Set E)) (hReal.transition_eq z k)
    have hπk : Kernel.Invariant (κ k) (π : Measure E) :=
      kernelInvariant_nat hReal.semigroup hπ k
    have hcomp_eq :
        ((κ k) ∘ₘ (π : Measure E)) ({y} : Set E) = (π : Measure E) ({y} : Set E) := by
      simpa using congrArg (fun ν : Measure E ↦ ν ({y} : Set E)) hπk.def
    have hcomp_sum :
        ((κ k) ∘ₘ (π : Measure E)) ({y} : Set E) =
          ∑' z : E, (π : Measure E) ({z} : Set E) * (κ k) z ({y} : Set E) := by
      rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ (MeasurableSet.singleton y)]
      refine tsum_congr fun z ↦ ?_
      rw [Measure.smul_apply]
      rfl
    -- Proof comment: expand the stationary mixture only for a single window, factor the no-hit
    -- part through the Markov property, and then collapse the remaining start-state sum by
    -- stationarity of the time-`k` marginal.
    simp only [μ, Measure.comp_eq_sum_of_countable, Measure.sum_apply _ (hW_meas k hk)]
    calc
      ∑' z : E, (π : Measure E) ({z} : Set E) * (P z : Measure Ω) (W k)
        = ∑' z : E,
            (P y : Measure Ω) (noHitHorizonLocal X y 0 (M - k)) *
              ((π : Measure E) ({z} : Set E) * (P z : Measure Ω) A) := by
              refine tsum_congr fun z ↦ ?_
              have hz :
                  (P z : Measure Ω) (W k) =
                    (P y : Measure Ω) (noHitHorizonLocal X y 0 (M - k)) *
                      (P z : Measure Ω) A := by
                simpa [W, A, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
                  measure_inter_prefix_noHitHorizon_eq_mulLocal
                    (κ := κ) (P := P) (X := X)
                    (x := z) (y := y) (A := A) (n := k) (M := M - k) hA_meas hA_sub
              rw [hz]
              ac_rfl
      _ = (P y : Measure Ω) (noHitHorizonLocal X y 0 (M - k)) *
            ∑' z : E, (π : Measure E) ({z} : Set E) * (P z : Measure Ω) A := by
            rw [ENNReal.tsum_mul_left]
      _ = (P y : Measure Ω) (noHitHorizonLocal X y 0 (M - k)) *
            ((π : Measure E) ({y} : Set E)) := by
            congr 1
            calc
              ∑' z : E, (π : Measure E) ({z} : Set E) * (P z : Measure Ω) A
                = ∑' z : E, (π : Measure E) ({z} : Set E) * (κ k) z ({y} : Set E) := by
                    refine tsum_congr fun z ↦ ?_
                    rw [hstateMass z]
              _ = ((κ k) ∘ₘ (π : Measure E)) ({y} : Set E) := by
                    symm
                    exact hcomp_sum
              _ = (π : Measure E) ({y} : Set E) := hcomp_eq
      _ = ((π : Measure E) ({y} : Set E)) *
            (P y : Measure Ω) (noHitHorizonLocal X y 0 (M - k)) := by
            rw [mul_comm]
  have hsum_union :
      Finset.sum (Finset.range (M + 1)) (fun k ↦ μ (W k)) = μ U := by
    symm
    simpa [U] using MeasureTheory.measure_biUnion_finset hW_disj hW_meas
  have hsum_le_one : Finset.sum (Finset.range (M + 1)) (fun k ↦ μ (W k)) ≤ 1 := by
    -- Proof comment: the windows are pairwise disjoint and their union sits inside `Set.univ`,
    -- so the summed window mass is at most the total mass of the stationary mixture.
    calc
      Finset.sum (Finset.range (M + 1)) (fun k ↦ μ (W k)) = μ U := hsum_union
      _ ≤ μ Set.univ := by
        exact measure_mono (by intro ω hω; simp [U])
      _ = 1 := hμ_univ
  -- Proof comment: rewrite the finite window sum through the slice-mass formula and then use the
  -- standard reflection identity on `Finset.range (M + 1)` to normalize `M - k` back to `k`.
  calc
    ((π : Measure E) ({y} : Set E)) *
        (Finset.sum (Finset.range (M + 1))
          (fun k ↦ (P y : Measure Ω) (noHitHorizonLocal X y 0 k)))
      = Finset.sum (Finset.range (M + 1)) (fun k ↦ μ (W k)) := by
          calc
            ((π : Measure E) ({y} : Set E)) *
                (Finset.sum (Finset.range (M + 1))
                  (fun k ↦ (P y : Measure Ω) (noHitHorizonLocal X y 0 k)))
              =
                ((π : Measure E) ({y} : Set E)) *
                  (Finset.sum (Finset.range (M + 1))
                    (fun k ↦ (P y : Measure Ω) (noHitHorizonLocal X y 0 (M - k)))) := by
                      congr 1
                      simpa using
                        (Finset.sum_range_reflect
                          (fun k ↦ (P y : Measure Ω) (noHitHorizonLocal X y 0 k)) (M + 1)).symm
            _ = Finset.sum (Finset.range (M + 1))
                  (fun k ↦
                    ((π : Measure E) ({y} : Set E)) *
                      (P y : Measure Ω) (noHitHorizonLocal X y 0 (M - k))) := by
                  rw [Finset.mul_sum]
            _ = Finset.sum (Finset.range (M + 1)) (fun k ↦ μ (W k)) := by
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  symm
                  exact hWindowMass k hk
    _ ≤ 1 := hsum_le_one

/-- Helper for Exercise 17.4.1: the local excursion measure agrees with the owner return-cycle
measure from Theorem 17.47. -/
private lemma returnCycleOccupationMeasureLocal_eq_owner
    (x : E) :
    returnCycleOccupationMeasureLocal P X x = (μ[P, X] x) := by
  -- Proof comment: both measures are weighted counting measures with the same singleton masses,
  -- so equality on singletons identifies them on the discrete countable state space.
  refine Measure.ext_of_singleton fun z ↦ ?_
  rw [returnCycleOccupationMeasureLocal_apply_singleton, returnCycleOccupationMeasure_apply_singleton]
  rfl

/-- Helper for Exercise 17.4.1: an invariant singleton mass controls the expected first return
time through the stationary finite-window decomposition. -/
lemma invariantSingletonMass_mul_expectedFirstReturnTime_le_one
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (κ 1) (π : Measure E)) :
    ((π : Measure E) ({y} : Set E)) * expectedFirstReturnTime P X y ≤ 1 := by
  -- Proof comment: first prove the finite-window bound under the stationary path mixture, then
  -- rewrite the expected return time as the `tsum` of those no-hit tails and pass to the `iSup`.
  rw [expectedFirstReturnTime_eq_tsum_tailProbabilitiesLocal (P := P) (X := X) (κ := κ) y,
    ENNReal.tsum_eq_iSup_nat, ENNReal.mul_iSup]
  refine iSup_le fun n ↦ ?_
  cases n with
  | zero =>
      simp
  | succ M =>
      simpa [noHitHorizon_zero_eq_firstReturnTailLocal (X := X) y] using
        stationaryNoHitWindowBoundLocal (κ := κ) (P := P) (X := X) hπ y M

/-- Helper for Exercise 17.4.1: a positive recurrent state supplies an invariant distribution
that charges its own singleton positively. -/
lemma existsInvariantDistributionAtPositiveRecurrentState
    (x : E) (hx : IsPositiveRecurrentState P X x) :
    ∃ π : ProbabilityMeasure E, Kernel.Invariant (κ 1) (π : Measure E) ∧
      0 < (π : Measure E) ({x} : Set E) := by
  -- Route correction: reuse Theorem 17.47 for the owner raw excursion invariance theorem, then
  -- scale that owner identity on the local candidate measure.
  have hrec : IsRecurrentState P X x :=
    positiveRecurrentState_isRecurrentStateLocal (P := P) (X := X) (κ := κ) x hx
  have hownerRaw : Kernel.Invariant (κ 1) ((μ[P, X] x) : Measure E) :=
    recurrentState_returnCycleOccupationMeasure_comp_eq
      (κ := κ) (P := P) (X := X) hrec
  have hlocalRaw : Kernel.Invariant (κ 1) (returnCycleOccupationMeasureLocal P X x) := by
    simpa [returnCycleOccupationMeasureLocal_eq_owner (P := P) (X := X) x] using hownerRaw
  have hscaled :
      Kernel.Invariant (κ 1)
        ((expectedFirstReturnTime P X x)⁻¹ • returnCycleOccupationMeasureLocal P X x) :=
    kernelInvariant_smulLocal
      (κ := κ) (a := (expectedFirstReturnTime P X x)⁻¹) hlocalRaw
  refine ⟨positiveRecurrentInvariantDistributionCandidateLocal (P := P) (X := X) (κ := κ) x hx,
    ?_, positiveRecurrentInvariantDistributionCandidateLocal_selfMass_pos
      (P := P) (X := X) (κ := κ) x hx⟩
  simpa [positiveRecurrentInvariantDistributionCandidateLocal] using hscaled

/-- Helper for Exercise 17.4.1: an invariant distribution with positive singleton mass at `y`
forces `y` to be positive recurrent. -/
lemma isPositiveRecurrentState_of_invariantDistribution_singleton_pos
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (κ 1) (π : Measure E))
    (hπy : 0 < (π : Measure E) ({y} : Set E)) :
    IsPositiveRecurrentState P X y := by
  -- Proof comment: the local stationary Kac inequality controls the expected first return time of
  -- `y` by the reciprocal of the positive singleton mass `π {y}`.
  have hmul_le :
      ((π : Measure E) ({y} : Set E)) * expectedFirstReturnTime P X y ≤ 1 :=
    invariantSingletonMass_mul_expectedFirstReturnTime_le_one
      (κ := κ) (P := P) (X := X) (y := y) hπ
  -- Proof comment: if the expected first return time were infinite, the positive singleton mass
  -- would force the left-hand side to be `⊤`, contradicting the bound by `1`.
  by_contra hnot
  have htop : expectedFirstReturnTime P X y = ⊤ := by
    exact le_antisymm le_top (not_lt.mp hnot)
  have hprod_top :
      ((π : Measure E) ({y} : Set E)) * expectedFirstReturnTime P X y = ⊤ := by
    rw [htop]
    simp [hπy.ne', measure_ne_top _ _]
  have : (⊤ : ℝ≥0∞) ≤ 1 := by
    simpa [hprod_top] using hmul_le
  simp at this

-- Proof sketch: build an invariant distribution from the positive recurrent state `x`, transfer
-- positive singleton mass from `x` to `y` along a strictly positive-time transition, and then
-- close positive recurrence of `y` from that positive invariant mass.
include κ in
/-- Exercise 17.4.1: if `x` is positive recurrent and the probability `F(x, y)` of ever hitting
`y` from `x` is positive, then `y` is also positive recurrent. -/
theorem isPositiveRecurrentState_of_isPositiveRecurrentState_of_everHitsProbability_pos
    (hx : IsPositiveRecurrentState P X x) (hxy : 0 < (F[P, X]) x y) :
    IsPositiveRecurrentState P X y := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  -- Route correction: `include κ` keeps the realization kernel in scope, so the local
  -- communication-to-invariant-mass helper chain can be used directly.
  have hInvariantBuilder :
      IsPositiveRecurrentState P X x →
        ∃ π : ProbabilityMeasure E, Kernel.Invariant (κ 1) (π : Measure E) ∧
          0 < (π : Measure E) ({x} : Set E) :=
    existsInvariantDistributionAtPositiveRecurrentState x
  obtain ⟨π, hπinv, hπx⟩ := hInvariantBuilder hx
  -- Proof comment: positive communication from `x` to `y` gives a positive-time singleton mass.
  have hStepBuilder :
      0 < (F[P, X]) x y → ∃ n : ℕ, 0 < n ∧ 0 < (κ n) x ({y} : Set E) :=
    existsPosStepMass_of_everHitsProbability_pos
  have hstep : ∃ n : ℕ, 0 < n ∧ 0 < (κ n) x ({y} : Set E) :=
    hStepBuilder hxy
  -- Proof comment: invariance transports the positive singleton mass from `x` to `y`.
  have hπy : 0 < (π : Measure E) ({y} : Set E) :=
    singletonMass_pos_of_invariant_of_posStepMass
      hReal.semigroup hπinv hπx hstep
  -- Proof comment: a positive invariant singleton mass at `y` closes positive recurrence of `y`.
  have hPositiveBuilder :
      Kernel.Invariant (κ 1) (π : Measure E) →
        0 < (π : Measure E) ({y} : Set E) →
          IsPositiveRecurrentState P X y :=
    isPositiveRecurrentState_of_invariantDistribution_singleton_pos
  exact
    hPositiveBuilder hπinv hπy

end CommunicatingStates

end ProbabilityTheory
