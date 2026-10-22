/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_4_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_49

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

include p P X

/- Layering for Theorem 17.51:
- the equivalence with the nonempty set `I` of invariant distributions is the source-facing
  textbook statement;
- `Kernel.Invariant` is the owner predicate for a specific invariant distribution;
- the normalized return-cycle distribution used in the closing formula is built locally from the
  Theorem 17.47 owner excursion measure, to stay compatible with the current import chain. -/

/-- Helper for Theorem 17.51: irreducibility forces the discrete state space to be countable,
because every state lies in the countable union of the positive-mass singleton supports of the
iterated kernels started from one reference state. -/
private lemma countableOfIrreducibleMarkovChainTheorem1751
    (hirr : IsIrreducibleMarkovChain P X) :
    Countable E := by
  classical
  by_cases hE : IsEmpty E
  · letI := hE
    infer_instance
  · letI : Nonempty E := not_isEmpty_iff.mp hE
    let x₀ : E := Classical.choice ‹Nonempty E›
    let κ : Kernel E E := discreteMatrixKernel p
    let hReal : IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
    let hproc : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
    letI : IsMarkovKernel κ := by
      simpa [κ] using hReal.semigroup.isMarkovKernel 1
    let reachable : ℕ → Set E := fun n ↦ {y : E | 0 < (κ ^ n) x₀ ({y} : Set E)}
    have hreachable_countable : ∀ n : ℕ, (reachable n).Countable := by
      intro n
      let μ : Measure E := (κ ^ n) x₀
      have hκpow : IsMarkovKernel (κ ^ n) := by
        induction n with
        | zero =>
            simpa using (inferInstance : IsMarkovKernel (Kernel.id : Kernel E E))
        | succ n ih =>
            simpa [pow_succ] using (inferInstance : IsMarkovKernel ((κ ^ n) ∘ₖ κ))
      letI : IsMarkovKernel (κ ^ n) := hκpow
      letI : IsProbabilityMeasure μ := inferInstance
      -- Proof comment: each `n`-step law is a probability measure, so only countably many
      -- singleton states can carry positive mass.
      have hμ_countable : {y : E | 0 < μ ({y} : Set E)}.Countable := by
        simpa [μ] using
          (Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
            (As_mble := fun y : E ↦ MeasurableSet.singleton y)
            (As_disj := fun y z hyz ↦ Set.disjoint_singleton.2 hyz))
      simpa [reachable, κ, μ] using hμ_countable
    have hcover : (⋃ n : ℕ, reachable n) = Set.univ := by
      ext y
      constructor
      · intro _
        simp
      · intro _
        have hgreen : 0 < (G[P, X; 1]) x₀ y :=
          (greenFunctionFrom_one_pos_iff_everHitsProbability_pos P X hproc x₀ y).2 (hirr x₀ y)
        rcases existsPosStepMass_of_greenFunctionFrom_one_pos
            (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n)
            (P := P) (X := X) hgreen with
          ⟨n, -, hn⟩
        exact Set.mem_iUnion.2 ⟨n, by simpa [reachable, κ] using hn⟩
    -- Proof comment: the whole state space is this countable union of reachable singleton
    -- supports.
    have huniv_countable : (Set.univ : Set E).Countable := by
      simpa [hcover] using Set.countable_iUnion hreachable_countable
    exact Set.countable_univ_iff.mp huniv_countable

/-- Helper for Theorem 17.51: a probability measure on a countable discrete state space must
charge some singleton positively. -/
private lemma existsSingletonMassPosOfProbabilityMeasure [Countable E]
    (π : ProbabilityMeasure E) :
    ∃ x : E, 0 < (π : Measure E) ({x} : Set E) := by
  -- Proof comment: if every singleton had zero mass, the countable singleton decomposition of
  -- `Set.univ` would force the total mass of the probability measure to vanish.
  by_contra hmass
  have hzero : ∀ x : E, (π : Measure E) ({x} : Set E) = 0 := by
    intro x
    by_contra hx
    exact hmass ⟨x, bot_lt_iff_ne_bot.mpr hx⟩
  have huniv_zero : (π : Measure E) Set.univ = 0 := by
    calc
      (π : Measure E) Set.univ = ∑' x : E, (π : Measure E) ({x} : Set E) := by
        symm
        simpa using
          (π : Measure E).tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
      _ = 0 := by
        rw [ENNReal.tsum_eq_zero]
        exact hzero
  have hone : (1 : ℝ≥0∞) = 0 := by
    simp at huniv_zero
  exact one_ne_zero hone

/-- Helper for Theorem 17.51: irreducibility of the realized chain induces irreducibility of the
counting-measure kernel `discreteMatrixKernel p`. -/
private theorem discreteMatrixKernelIsIrreducibleTheorem1751
    (hirr : IsIrreducibleMarkovChain P X) :
    Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p) := by
  classical
  let hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let hproc : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  letI : IsMarkovKernel (discreteMatrixKernel p) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  refine ⟨?_⟩
  intro A hA hcount x
  obtain ⟨y, hyA⟩ : A.Nonempty := by
    exact MeasureTheory.nonempty_of_measure_ne_zero (μ := (Measure.count : Measure E))
      (ne_of_gt hcount)
  by_cases hxy : x = y
  · subst hxy
    -- Proof comment: if the starting point already lies in `A`, the time-zero kernel mass
    -- witnesses irreducibility immediately.
    have hxA : x ∈ A := hyA
    refine ⟨0, ?_⟩
    change 0 < (Kernel.id x) A
    simp [Kernel.id_apply, hxA]
  · have hgreen : 0 < (G[P, X; 1]) x y :=
        (greenFunctionFrom_one_pos_iff_everHitsProbability_pos P X hproc x y).2 (hirr x y)
    rcases existsPosStepMass_of_greenFunctionFrom_one_pos
      (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n)
      (P := P) (X := X) hgreen with ⟨n, -, hn⟩
    -- Proof comment: a positive step mass to a singleton inside `A` upgrades to positive mass on
    -- `A` by monotonicity.
    refine ⟨n, lt_of_lt_of_le hn ?_⟩
    exact measure_mono (Set.singleton_subset_iff.2 hyA)

/-- Helper for Theorem 17.51: an invariant distribution of an irreducible chain assigns strictly
positive mass to every singleton. -/
private lemma invariantSingletonMassPosOfIrreducible [Countable E]
    (hirr : IsIrreducibleMarkovChain P X) {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E)) (x : E) :
    0 < (π : Measure E) ({x} : Set E) := by
  let hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hπ' :
      Kernel.Invariant ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) (π : Measure E) := by
    simpa using hπ
  obtain ⟨y, hymass⟩ := existsSingletonMassPosOfProbabilityMeasure
    (Ω := Ω) (p := p) (P := P) (X := X) (E := E) (π := π)
  have hyx : 0 < (F[P, X]) y x := hirr y x
  have hstep :
      ∃ n : ℕ, 0 < n ∧ 0 < ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) n) y ({x} : Set E) := by
    exact existsPosStepMass_of_everHitsProbability_pos
      (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n)
      (P := P) (X := X) (x := y) (y := x) hyx
  -- Proof comment: start from one positive singleton of `π`, then propagate that mass to `x`
  -- along a positive-time step guaranteed by irreducibility.
  exact singletonMass_pos_of_invariant_of_posStepMass hReal.semigroup hπ' hymass hstep

/-- Helper for Theorem 17.51: the return-cycle occupation mass of the base state itself is `1`. -/
private lemma returnCycleOccupationMassSelfEqOneTheorem1751
    (x : E) :
    returnCycleOccupationMass P X x x = 1 := by
  let hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hinit :
      (P x : Measure Ω) {ω | X 0 ω = x} = 1 := by
    have hpreimage : {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set E) := by
      ext ω
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x)]
    rw [hReal.initial_eq x]
    simp
  have hterm0 :
      (P x : Measure Ω) {ω | X 0 ω = x ∧ (0 : ℕ∞) < (τ_[X, x]^1) ω} = 1 := by
    have hτpos : ∀ ω : Ω, (0 : ℕ∞) < (τ_[X, x]^1) ω := by
      intro ω
      have hτge1 : (1 : ℕ∞) ≤ (τ_[X, x]^1) ω := by
        have h :
            (1 : ℕ) ≤ MeasureTheory.hittingAfter X ({x} : Set E) 1 ω :=
          le_hittingAfter ω
        simpa [iteratedEntranceTime_one] using h
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
  have htailZero :
      ∀ m : ℕ,
        ite (m = 0) 0
          ((P x : Measure Ω) {ω | X m ω = x ∧ (m : ℕ∞) < (τ_[X, x]^1) ω}) = 0 := by
    intro m
    by_cases hm : m = 0
    · simp [hm]
    · rcases Nat.exists_eq_succ_of_ne_zero hm with ⟨n, rfl⟩
      have hempty :
          {ω | X (n + 1) ω = x ∧ (((n + 1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} = ∅ := by
        ext ω
        constructor
        · intro hω
          have hle : (τ_[X, x]^1) ω ≤ n + 1 := by
            have h :
                MeasureTheory.hittingAfter X ({x} : Set E) 1 ω ≤ n + 1 :=
              hittingAfter_le_of_mem (by simp) (by simpa [Set.mem_singleton_iff] using hω.1)
            simpa [iteratedEntranceTime_one] using h
          exact False.elim <| (not_lt_of_ge hle) hω.2
        · simp
      rw [hempty]
      simp
  have htailTsum :
      (∑' m : ℕ,
        ite (m = 0) 0
          ((P x : Measure Ω) {ω | X m ω = x ∧ (m : ℕ∞) < (τ_[X, x]^1) ω})) = 0 := by
    exact ENNReal.tsum_eq_zero.2 htailZero
  have hterm0' :
      (P x : Measure Ω) {ω | X 0 ω = x ∧ ((0 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} = 1 := by
    simpa using hterm0
  have htailTsum' :
      (∑' i : ℕ,
        if i = 0 then 0 else (P x : Measure Ω) {ω | X i ω = x ∧ (i : ℕ∞) < (τ_[X, x]^1) ω}) = 0 := by
    simpa using htailTsum
  -- Proof comment: time `0` contributes mass `1`, and every later diagonal slice is empty
  -- because a positive-time return would contradict `m < τ_x^1`.
  rw [returnCycleOccupationMass, ENNReal.tsum_eq_add_tsum_ite 0, hterm0']
  have hsum1 :
      1 + (∑' i : ℕ,
        if i = 0 then 0 else (P x : Measure Ω) {ω | X i ω = x ∧ (i : ℕ∞) < (τ_[X, x]^1) ω}) =
          1 + 0 := congrArg (fun t : ℝ≥0∞ ↦ 1 + t) htailTsum'
  simpa using hsum1

/-- Helper for Theorem 17.51: at a fixed time `n`, summing the state-slice probabilities over
all states recovers the tail probability `ℙ_x[n < τ_x^1]`. -/
private lemma tsumStateSliceProbabilitiesEqTailProbabilityTheorem1751 [Countable E]
    (x : E) (n : ℕ) :
    ∑' y : E, (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} =
      (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  classical
  let A : Set Ω := {ω | (n : ℕ∞) < (τ_[X, x]^1) ω}
  have hA_meas : MeasurableSet A :=
    measurableSet_firstReturnTimeTailLocal
      (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X) x n
  have hSlice_meas : ∀ y : E, MeasurableSet {ω | X n ω = y ∧ ω ∈ A} := by
    intro y
    have hState :
        MeasurableSet (X n ⁻¹' ({y} : Set E)) :=
      (IsMarkovProcessRealization.measurable_process
        (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X) n)
        (MeasurableSet.singleton y)
    have hEq :
        {ω | X n ω = y ∧ ω ∈ A} = (X n ⁻¹' ({y} : Set E)) ∩ A := by
      ext ω
      simp [A]
    rw [hEq]
    exact hState.inter hA_meas
  -- Proof comment: rewrite each slice probability as an indicator integral, commute the
  -- countable state sum with the integral, and collapse pointwise to the unique state `X n ω`.
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

/-- Helper for Theorem 17.51: the total excursion occupation mass agrees with the tail
probability series of `τ_[X, x]^1`. -/
private lemma tsumReturnCycleOccupationMassEqTsumTailProbabilitiesTheorem1751 [Countable E]
    (x : E) :
    ∑' y : E, returnCycleOccupationMass P X x y =
      ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: rewrite the outer state sum as a count integral, commute it past the time
  -- series, and collapse each fixed-time slice with the previous lemma.
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
          exact tsumStateSliceProbabilitiesEqTailProbabilityTheorem1751
            (p := p) (P := P) (X := X) x n

/-- Helper for Theorem 17.51: the excursion occupation measure has total mass
`𝔼_x[τ_x^1]`. -/
private lemma returnCycleOccupationMeasureUnivEqExpectedFirstReturnTimeTheorem1751 [Countable E]
    (x : E) :
    (μ[P, X] x) Set.univ = expectedFirstReturnTime P X x := by
  -- Proof comment: evaluate the owner excursion measure on `Set.univ`, rewrite the count
  -- integral as a series, and identify that series with the first-return tail expansion.
  calc
    (μ[P, X] x) Set.univ
      = ∫⁻ y, returnCycleOccupationMass P X x y ∂Measure.count := by
          rw [returnCycleOccupationMeasure, withDensity_apply _ MeasurableSet.univ,
            Measure.restrict_univ]
    _ = ∑' y : E, returnCycleOccupationMass P X x y := by
          rw [lintegral_count]
    _ = ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          rw [tsumReturnCycleOccupationMassEqTsumTailProbabilitiesTheorem1751
            (p := p) (P := P) (X := X) x]
    _ = expectedFirstReturnTime P X x := by
          symm
          exact expectedFirstReturnTime_eq_tsum_tailProbabilitiesLocal
            (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X) x

/-- Helper for Theorem 17.51: scaling an invariant measure preserves kernel invariance. -/
private lemma kernelInvariantSmulMeasureTheorem1751
    {μ : Measure E} {a : ℝ≥0∞}
    (hμ : Kernel.Invariant (discreteMatrixKernel p) μ) :
    Kernel.Invariant (discreteMatrixKernel p) (a • μ) := by
  -- Proof comment: `Measure.bind` is linear in the measure argument, so the invariance identity
  -- scales on both sides.
  rw [Kernel.Invariant] at hμ ⊢
  calc
    (a • μ).bind (discreteMatrixKernel p) = a • (μ.bind (discreteMatrixKernel p)) := by
      exact Measure.bind_smul a μ (discreteMatrixKernel p)
    _ = a • μ := by rw [hμ]

/-- Helper for Theorem 17.51: the normalized return-cycle law at a positive recurrent state is a
probability distribution. -/
private theorem normalizedReturnCycleInvariantDistribution_isProbabilityMeasure [Countable E]
    (x : E) (hx : IsPositiveRecurrentState P X x) :
    IsProbabilityMeasure ((expectedFirstReturnTime P X x)⁻¹ • (μ[P, X] x)) := by
  have hmass :
      (μ[P, X] x) Set.univ = expectedFirstReturnTime P X x :=
    returnCycleOccupationMeasureUnivEqExpectedFirstReturnTimeTheorem1751
      (p := p) (P := P) (X := X) x
  have hmass_ne_zero : (μ[P, X] x) Set.univ ≠ 0 := by
    have hpos :
        0 < expectedFirstReturnTime P X x := by
      exact lt_of_lt_of_le zero_lt_one
        (one_le_expectedFirstReturnTimeLocal (P := P) (X := X) x)
    rw [hmass]
    exact ne_of_gt hpos
  -- Proof comment: the total mass is finite and nonzero, so scaling by its inverse normalizes
  -- it to `1`.
  refine isProbabilityMeasure_iff.2 ?_
  rw [Measure.smul_apply, hmass]
  exact ENNReal.inv_mul_cancel (by simpa [hmass] using hmass_ne_zero) (ne_of_lt hx)

/-- Helper for Theorem 17.51: the normalized return-cycle law rooted at `x`. -/
private def normalizedReturnCycleInvariantDistribution [Countable E]
    (x : E) (hx : IsPositiveRecurrentState P X x) : ProbabilityMeasure E :=
  ⟨(expectedFirstReturnTime P X x)⁻¹ • (μ[P, X] x),
    normalizedReturnCycleInvariantDistribution_isProbabilityMeasure
      (p := p) (P := P) (X := X) x hx⟩

/-- Helper for Theorem 17.51: the normalized return-cycle law is invariant under the one-step
kernel. -/
private theorem normalizedReturnCycleInvariantDistribution_isInvariant [Countable E]
    (x : E) (hx : IsPositiveRecurrentState P X x) :
    Kernel.Invariant (discreteMatrixKernel p)
      (normalizedReturnCycleInvariantDistribution (p := p) (P := P) (X := X) x hx : Measure E) := by
  have hrec : IsRecurrentState P X x :=
    positiveRecurrentState_isRecurrentStateLocal
      (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X) x hx
  have hraw : Kernel.Invariant (discreteMatrixKernel p) ((μ[P, X] x) : Measure E) := by
    simpa using
      recurrentState_returnCycleOccupationMeasure_comp_eq
        (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X) hrec
  have hscaled :
      Kernel.Invariant (discreteMatrixKernel p)
        ((expectedFirstReturnTime P X x)⁻¹ • (μ[P, X] x)) :=
    kernelInvariantSmulMeasureTheorem1751
      (Ω := Ω) (p := p) (P := P) (X := X) (μ := ((μ[P, X] x) : Measure E))
      (a := (expectedFirstReturnTime P X x)⁻¹) hraw
  simpa [normalizedReturnCycleInvariantDistribution] using hscaled

/-- Helper for Theorem 17.51: the normalized return-cycle law charges its base state by the
reciprocal first-return expectation. -/
private lemma normalizedReturnCycleInvariantDistributionApplySingletonSelfTheorem1751 [Countable E]
    (x : E) (hx : IsPositiveRecurrentState P X x) :
    normalizedReturnCycleInvariantDistribution (p := p) (P := P) (X := X) x hx {x} =
      1 / expectedFirstReturnTime P X x := by
  have hfin : expectedFirstReturnTime P X x ≠ ∞ := ne_of_lt hx
  have hpos : 0 < expectedFirstReturnTime P X x := by
    exact lt_of_lt_of_le zero_lt_one
      (one_le_expectedFirstReturnTimeLocal (P := P) (X := X) x)
  have htoNNReal_ne_zero : (expectedFirstReturnTime P X x).toNNReal ≠ 0 := by
    exact ne_of_gt (ENNReal.toNNReal_pos hpos.ne' hfin)
  -- Proof comment: unfold the normalized return-cycle law, evaluate it on `{x}`, and then insert
  -- the self-mass computation for the owner excursion measure.
  calc
    ((normalizedReturnCycleInvariantDistribution (p := p) (P := P) (X := X) x hx {x} : ℝ≥0∞))
      = ↑(expectedFirstReturnTime P X x).toNNReal⁻¹ *
          ↑(returnCycleOccupationMass P X x x).toNNReal := by
          simp [normalizedReturnCycleInvariantDistribution, Measure.smul_apply, measure_ne_top,
            returnCycleOccupationMeasure_apply_singleton]
    _ = ↑(expectedFirstReturnTime P X x).toNNReal⁻¹ * 1 := by
          rw [returnCycleOccupationMassSelfEqOneTheorem1751 (p := p) (P := P) (X := X) x]
          simp
    _ = (expectedFirstReturnTime P X x)⁻¹ := by
          rw [mul_one]
          calc
            ↑(expectedFirstReturnTime P X x).toNNReal⁻¹
              = (((expectedFirstReturnTime P X x).toNNReal : ℝ≥0∞))⁻¹ := by
                  rw [ENNReal.coe_inv]
                  exact htoNNReal_ne_zero
            _ = (expectedFirstReturnTime P X x)⁻¹ := by
                  rw [ENNReal.coe_toNNReal hfin]
    _ = 1 / expectedFirstReturnTime P X x := by
          simp [one_div]

-- Proof sketch: use Corollary 17.48 for the forward implication. For the converse, any invariant
-- distribution of an irreducible chain charges every singleton positively, and Exercise 17.4.1
-- turns that positive singleton mass into positive recurrence state by state.
/-- Theorem 17.51: for an irreducible discrete Markov chain with transition matrix `p`, the chain
is positive recurrent if and only if the set `I` of invariant distributions of
`discreteMatrixKernel p` is nonempty. -/
theorem isPositiveRecurrentMarkovChain_iff_invariantDistributions_ne_empty
    [Nonempty E]
    (hirr : IsIrreducibleMarkovChain P X) :
    IsPositiveRecurrentMarkovChain P X ↔ invariantDistributions (discreteMatrixKernel p) ≠ ∅ := by
  classical
  letI : Countable E := countableOfIrreducibleMarkovChainTheorem1751
    (p := p) (P := P) (X := X) hirr
  constructor
  · intro hX
    let π : ProbabilityMeasure E :=
      normalizedReturnCycleInvariantDistribution
        (p := p) (P := P) (X := X) (Classical.choice ‹Nonempty E›) (hX _)
    have hπinv : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E) := by
      simpa [π] using
        normalizedReturnCycleInvariantDistribution_isInvariant
          (p := p) (P := P) (X := X) (Classical.choice ‹Nonempty E›) (hX _)
    have hπmem : π ∈ invariantDistributions (discreteMatrixKernel p) :=
      (mem_invariantDistributions_iff (discreteMatrixKernel p) π).2 hπinv
    -- Proof comment: one invariant distribution already witnesses `I ≠ ∅`.
    exact (Set.nonempty_iff_ne_empty.1) ⟨π, hπmem⟩
  · intro hI
    obtain ⟨π, hπmem⟩ := Set.nonempty_iff_ne_empty.2 hI
    have hπinv : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E) :=
      (mem_invariantDistributions_iff (discreteMatrixKernel p) π).1 hπmem
    intro x
    have hπx :
        0 < (π : Measure E) ({x} : Set E) :=
      invariantSingletonMassPosOfIrreducible (p := p) (P := P) (X := X) hirr hπinv x
    -- Proof comment: positive invariant mass at `{x}` forces `x` to be positive recurrent.
    exact isPositiveRecurrentState_of_invariantDistribution_singleton_pos
      (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X)
      (by simpa using hπinv) hπx

-- Proof sketch: irreducibility of the realized chain induces kernel irreducibility of
-- `discreteMatrixKernel p`. Theorem 17.49 then makes the invariant-distribution set a singleton.
/-- If an irreducible chain admits an invariant distribution `π`, then that distribution is the
unique element of the invariant-distribution set. -/
theorem invariantDistributions_eq_singleton_of_mem
    (hirr : IsIrreducibleMarkovChain P X) {π : ProbabilityMeasure E}
    (hπ : π ∈ invariantDistributions (discreteMatrixKernel p)) :
    invariantDistributions (discreteMatrixKernel p) = {π} := by
  let hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel p) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  letI : Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p) :=
    discreteMatrixKernelIsIrreducibleTheorem1751 (p := p) (P := P) (X := X) hirr
  have hπinv : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E) :=
    (mem_invariantDistributions_iff (discreteMatrixKernel p) π).1 hπ
  ext ν
  constructor
  · intro hν
    have hνinv : Kernel.Invariant (discreteMatrixKernel p) (ν : Measure E) :=
      (mem_invariantDistributions_iff (discreteMatrixKernel p) ν).1 hν
    have hEq : ν = π :=
      eq_of_isInvariantDistribution_of_irreducible (p := discreteMatrixKernel p) hνinv hπinv
    simpa [hEq]
  · intro hν
    rcases Set.mem_singleton_iff.1 hν with rfl
    exact hπ

-- Proof sketch: once an invariant distribution `π` exists, the equivalence above yields positive
-- recurrence. Route correction: compare `π` directly with the local normalized return-cycle law
-- built from the owner excursion measure, rather than importing the conflicting Corollary 17.48
-- wrapper module.
/-- If `π` is an invariant distribution of an irreducible chain, then the singleton mass of `π`
at `x` is the reciprocal of the expected first return time to `x`. -/
theorem invariantDistribution_apply_singleton_eq_one_div_expectedFirstReturnTime
    (hirr : IsIrreducibleMarkovChain P X) {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E)) (x : E) :
    π {x} = 1 / expectedFirstReturnTime P X x := by
  letI : Countable E := countableOfIrreducibleMarkovChainTheorem1751
    (p := p) (P := P) (X := X) hirr
  letI : Nonempty E := ⟨x⟩
  let hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel p) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  letI : Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p) :=
    discreteMatrixKernelIsIrreducibleTheorem1751 (p := p) (P := P) (X := X) hirr
  have hπmem : π ∈ invariantDistributions (discreteMatrixKernel p) :=
    (mem_invariantDistributions_iff (discreteMatrixKernel p) π).2 hπ
  have hI : invariantDistributions (discreteMatrixKernel p) ≠ ∅ :=
    Set.nonempty_iff_ne_empty.1 ⟨π, hπmem⟩
  have hX : IsPositiveRecurrentMarkovChain P X :=
    (isPositiveRecurrentMarkovChain_iff_invariantDistributions_ne_empty
      (p := p) (P := P) (X := X) hirr).2 hI
  have hμinv :
      Kernel.Invariant (discreteMatrixKernel p)
        (normalizedReturnCycleInvariantDistribution
          (p := p) (P := P) (X := X) x (hX x) : Measure E) := by
    simpa using
      normalizedReturnCycleInvariantDistribution_isInvariant
        (p := p) (P := P) (X := X) x (hX x)
  have hEq :
      π =
        normalizedReturnCycleInvariantDistribution
          (p := p) (P := P) (X := X) x (hX x) :=
    eq_of_isInvariantDistribution_of_irreducible (p := discreteMatrixKernel p) hπ hμinv
  -- Proof comment: uniqueness identifies `π` with the normalized return-cycle law at `x`, so the
  -- singleton formula comes from the explicit self-mass computation above.
  simpa [hEq] using
    normalizedReturnCycleInvariantDistributionApplySingletonSelfTheorem1751
      (p := p) (P := P) (X := X) x (hX x)

-- Proof sketch: once the state space is known countable, irreducibility transports one positive
-- singleton mass of `π` to every target state.
/-- Any invariant distribution of an irreducible chain assigns strictly positive mass to every
singleton. -/
theorem invariantDistribution_apply_singleton_pos
    (hirr : IsIrreducibleMarkovChain P X) {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E)) (x : E) :
    0 < π {x} := by
  letI : Countable E := countableOfIrreducibleMarkovChainTheorem1751
    (p := p) (P := P) (X := X) hirr
  have hmass :
      0 < (π : Measure E) ({x} : Set E) :=
    invariantSingletonMassPosOfIrreducible (p := p) (P := P) (X := X) hirr hπ x
  have hlt_top : (π : Measure E) ({x} : Set E) < ∞ := by
    have hsubset : ({x} : Set E) ⊆ Set.univ := Set.singleton_subset_iff.2 (Set.mem_univ x)
    exact lt_of_le_of_lt (measure_mono hsubset) (by simpa using (show ((π : Measure E) Set.univ) < ∞ by simp))
  -- Proof comment: the file-local singleton-positivity bridge applies directly once countability
  -- is installed from irreducibility; convert the owner `ℝ≥0∞` mass to the `NNReal` value of
  -- the probability measure.
  simpa using ENNReal.toNNReal_pos hmass.ne' hlt_top.ne

end ProbabilityTheory
