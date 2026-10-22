/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_47
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_4_1

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/- Layering for Exercise 17.6.6:
- `IsIrreducibleMarkovChain P X` and `IsRecurrentMarkovChain P X` are the source-facing Chapter 17
  hypotheses.
- Semantic recall hit: the canonical mathlib owner predicate for invariant measures here is
  `Kernel.Invariant`.
- `Kernel.Invariant` is the core/canonical owner predicate for invariant measures of a fixed
  kernel.
- `discreteMatrixKernel p` remains only the concrete bridge/view turning a stochastic matrix into
  the kernel whose invariant measures are being compared. -/

section

variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]

include p P X

/-- Helper for Exercise 17.6.6: irreducibility forces the discrete state space to be countable,
because every state is reached with positive mass at some deterministic time from a fixed
reference state. -/
lemma countableOfIsIrreducibleMarkovChain
    (hirr : IsIrreducibleMarkovChain P X) :
    Countable E := by
  classical
  by_cases hE : IsEmpty E
  · letI := hE
    infer_instance
  · letI : Nonempty E := not_isEmpty_iff.mp hE
    let x₀ : E := Classical.choice ‹Nonempty E›
    let reachable : ℕ → Set E :=
      fun n ↦ {y : E | 0 < ((discreteMatrixKernel p ^ n) x₀) ({y} : Set E)}
    have hreachable_countable : ∀ n : ℕ, (reachable n).Countable := by
      intro n
      let μ : Measure E := ((discreteMatrixKernel p ^ n) x₀)
      let hReal : IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
      letI : IsMarkovKernel (discreteMatrixKernel p ^ n) := hReal.semigroup.isMarkovKernel n
      letI : IsProbabilityMeasure μ := inferInstance
      -- Proof comment: each `n`-step law is a probability measure, so only countably many
      -- singleton fibers can carry positive mass.
      have hμ_countable : {y : E | 0 < μ ({y} : Set E)}.Countable := by
        simpa [μ] using
          (Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
            (As_mble := fun y : E ↦ MeasurableSet.singleton y)
            (As_disj := fun y z hyz ↦ Set.disjoint_singleton.2 hyz))
      simpa [reachable, μ] using hμ_countable
    have hcover : (⋃ n : ℕ, reachable n) = Set.univ := by
      ext y
      constructor
      · intro _
        simp
      · intro _
        let hReal : IsMarkovProcessRealization
            (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
        let hproc : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
        have hgreen : 0 < (G[P, X; 1]) x₀ y := by
          exact (greenFunctionFrom_one_pos_iff_everHitsProbability_pos P X hproc x₀ y).2
            (hirr x₀ y)
        rcases existsPosStepMass_of_greenFunctionFrom_one_pos
            (κ := fun n ↦ discreteMatrixKernel p ^ n) P X hgreen with ⟨n, _, hmass⟩
        exact Set.mem_iUnion.2 ⟨n, by simpa [reachable] using hmass⟩
    have huniv_countable : (Set.univ : Set E).Countable := by
      simpa [hcover] using Set.countable_iUnion hreachable_countable
    exact Set.countable_univ_iff.mp huniv_countable

/-- Helper for Exercise 17.6.6: on a countable discrete state space, a nonzero measure must put
strictly positive mass on at least one singleton. -/
lemma existsPositiveSingletonMassOfNeZero [Countable E] {π : Measure E}
    (hπ_ne : π ≠ 0) :
    ∃ x : E, 0 < π ({x} : Set E) := by
  classical
  by_contra hnone
  have hzero : π = 0 := by
    refine Measure.ext_of_singleton fun x ↦ ?_
    have hx_not_pos : ¬ 0 < π ({x} : Set E) := by
      intro hx
      exact hnone ⟨x, hx⟩
    exact le_antisymm (le_of_not_gt hx_not_pos) bot_le
  exact hπ_ne hzero

/-- Helper for Exercise 17.6.6: invariance under `discreteMatrixKernel p` propagates to every
iterate, and on singleton sets this gives the usual countable discrete convolution identity. -/
lemma invariantMeasureApplySingletonEqTsumPow [Countable E] {π : Measure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π) (n : ℕ) (y : E) :
    π ({y} : Set E) =
      ∑' z : E, π ({z} : Set E) * ((discreteMatrixKernel p ^ n) z ({y} : Set E)) := by
  let hReal : IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
  have hπn : Kernel.Invariant (discreteMatrixKernel p ^ n) π :=
    kernelInvariant_nat hReal.semigroup (by simpa using hπ) n
  -- Proof comment: evaluate the `n`-step invariance identity on the singleton `{y}`.
  have hy :
      ((discreteMatrixKernel p ^ n) ∘ₘ π) ({y} : Set E) = π ({y} : Set E) :=
    congrArg (fun ρ : Measure E ↦ ρ ({y} : Set E)) hπn.def
  calc
    π ({y} : Set E) = ((discreteMatrixKernel p ^ n) ∘ₘ π) ({y} : Set E) := hy.symm
    _ = ∑' z : E, π ({z} : Set E) * ((discreteMatrixKernel p ^ n) z ({y} : Set E)) := by
          rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ (MeasurableSet.singleton y)]
          refine tsum_congr fun z ↦ ?_
          rw [Measure.smul_apply]
          rfl

/-- Helper for Exercise 17.6.6: a nonzero invariant measure with finite singleton masses agrees
singletonwise with its mass at `x` times the return-cycle occupation measure rooted at the
recurrent state `x`. -/
lemma returnCycleOccupationMeasure_apply_singleton_self
    (x : E) :
    (μ[P, X] x) ({x} : Set E) = 1 := by
  let hReal : IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
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
        have h : (1 : ℕ) ≤ MeasureTheory.hittingAfter X ({x} : Set E) 1 ω := le_hittingAfter ω
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
        ite (m = 0) 0 ((P x : Measure Ω) {ω | X m ω = x ∧ (m : ℕ∞) < (τ_[X, x]^1) ω})) = 0 := by
    exact ENNReal.tsum_eq_zero.2 htailZero
  have hterm0' :
      (P x : Measure Ω) {ω | X 0 ω = x ∧ ((0 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} = 1 := by
    simpa using hterm0
  have htailTsum' :
      (∑' i : ℕ,
        if i = 0 then 0 else (P x : Measure Ω) {ω | X i ω = x ∧ (i : ℕ∞) < (τ_[X, x]^1) ω}) = 0 := by
    simpa using htailTsum
  -- Proof comment: only the initial visit contributes to the diagonal before-return occupation
  -- mass, because any later visit to `x` would already be the first positive return.
  rw [returnCycleOccupationMeasure_apply_singleton, returnCycleOccupationMass,
    ENNReal.tsum_eq_add_tsum_ite 0, hterm0']
  have hsum1 :
      1 + (∑' i : ℕ,
        if i = 0 then 0 else (P x : Measure Ω) {ω | X i ω = x ∧ (i : ℕ∞) < (τ_[X, x]^1) ω}) =
          1 + 0 := congrArg (fun t : ℝ≥0∞ ↦ 1 + t) htailTsum'
  simpa using hsum1

/-- Helper for Exercise 17.6.6: the weighted start law attached to the singleton masses of `π`
starts from `z` with weight `π ({z})`. -/
private def weightedStartLaw (π : Measure E) : Measure Ω :=
  Measure.sum fun z : E ↦ π ({z} : Set E) • (P z : Measure Ω)

/-- Helper for Exercise 17.6.6: finite-horizon no-hit events are measurable. -/
private lemma measurableSet_noHitHorizonLocal
    (x : E) (n M : ℕ) :
    MeasurableSet (noHitHorizonLocal X x n M) := by
  let hReal : IsMarkovProcessRealization
      (fun k ↦ discreteMatrixKernel p ^ k) P X := inferInstance
  have hEq :
      noHitHorizonLocal X x n M =
        ⋂ m ∈ Finset.Icc 1 M, {ω | X (n + m) ω ≠ x} := by
    ext ω
    simp [noHitHorizonLocal]
  rw [hEq]
  refine MeasurableSet.iInter fun m ↦ ?_
  refine MeasurableSet.iInter fun _hm ↦ ?_
  exact ((hReal.measurable_process (n + m)) (MeasurableSet.singleton x)).compl

/-- Helper for Exercise 17.6.6: the last-visit slice records that time `n - k` is the final
visit to `x` before landing at `y` at time `n`. -/
private def lastVisitSlice (x y : E) (n k : ℕ) : Set Ω :=
  {ω | X (n - k) ω = x ∧ noHitHorizonLocal X x (n - k) k ω ∧ X n ω = y}

/-- Helper for Exercise 17.6.6: the weighted start law evaluates the time-`n` state event by the
singleton mass of the invariant measure. -/
private lemma weightedStartLaw_apply_stateEvent [Countable E] {π : Measure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π)
    (n : ℕ) (y : E) :
    weightedStartLaw (P := P) (π := π) {ω | X n ω = y} = π ({y} : Set E) := by
  classical
  let hReal : IsMarkovProcessRealization
      (fun k ↦ discreteMatrixKernel p ^ k) P X := inferInstance
  have hStateMeas : MeasurableSet {ω | X n ω = y} := by
    simpa [Set.preimage] using
      (hReal.measurable_process n) (MeasurableSet.singleton y)
  rw [weightedStartLaw, Measure.sum_apply _ hStateMeas]
  symm
  calc
    π ({y} : Set E) =
        ∑' z : E, π ({z} : Set E) * ((discreteMatrixKernel p ^ n) z ({y} : Set E)) :=
      invariantMeasureApplySingletonEqTsumPow (p := p) (P := P) (X := X) hπ n y
    _ = ∑' z : E, π ({z} : Set E) * (P z : Measure Ω) {ω | X n ω = y} := by
          refine tsum_congr fun z ↦ ?_
          have hz :
              (P z : Measure Ω) {ω | X n ω = y} =
                ((discreteMatrixKernel p ^ n) z) ({y} : Set E) := by
            have hpreimage : {ω | X n ω = y} = X n ⁻¹' ({y} : Set E) := by
              ext ω
              simp
            rw [hpreimage]
            rw [← Measure.map_apply (hReal.measurable_process n) (MeasurableSet.singleton y)]
            rw [hReal.transition_eq z n]
          simpa [hz]

/-- Helper for Exercise 17.6.6: `noHitHorizonLocal X x 0 n` is exactly the tail event
`{ω | n < τ_[X, x]^1(ω)}`. -/
private lemma noHitHorizon_zero_eq_firstReturnTail [Countable E]
    (x : E) (n : ℕ) :
    noHitHorizonLocal X x 0 n = {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: avoiding `x` during the first `n` positive times is equivalent to saying
  -- that no return to `x` occurs before time `n + 1`.
  ext ω
  constructor
  · intro hω
    change (n : ℕ∞) < (τ_[X, x]^1) ω
    by_contra hle
    have hle' : (τ_[X, x]^1) ω ≤ n := le_of_not_gt hle
    rcases (firstReturnTime_le_iffLocal (X := X) x n ω).1 hle' with ⟨j, hj, hjEq⟩
    exact hω j hj.1 hj.2 (by simpa [zero_add] using hjEq)
  · intro hω
    intro m hm1 hmn hmEq
    have hle : (τ_[X, x]^1) ω ≤ n :=
      (firstReturnTime_le_iffLocal (X := X) x n ω).2
        ⟨m, ⟨hm1, hmn⟩, by simpa [zero_add] using hmEq⟩
    exact not_lt_of_ge hle hω

/-- Helper for Exercise 17.6.6: if a time-`n` history event already forces `X n = z`, then
intersecting it with the time-`n + m` singleton event factors through the `m`-step transition
mass from `z`. -/
private lemma measure_inter_prefix_stepEvent_eq_mulLocal
    {s z y : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = z}) :
    (P s : Measure Ω) (A ∩ {ω | X (n + m) ω = y}) =
      ((discreteMatrixKernel p ^ m) z ({y} : Set E)) * (P s : Measure Ω) A := by
  let μ : Measure Ω := P s
  let hReal : IsMarkovProcessRealization
      (fun k ↦ discreteMatrixKernel p ^ k) P X := inferInstance
  let B : Set Ω := X (n + m) ⁻¹' ({y} : Set E)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + m)) (MeasurableSet.singleton y)
  have hA_measAmbient : MeasurableSet A := by
    exact (generatedFiltrationSpace_le_ambient X hReal.measurable_process n) _ hA_meas
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ (((discreteMatrixKernel p ^ m) (X n ω)).real ({y} : Set E)) := by
    simpa [μ, B, add_comm] using
      hReal.markov_property s (A := ({y} : Set E)) (MeasurableSet.singleton y) n m
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  have hstep :
      μ.real (A ∩ {ω | X (n + m) ω = y}) =
        (((discreteMatrixKernel p ^ m) z ({y} : Set E)).toReal) * μ.real A := by
    -- Proof comment: integrate the Markov conditional-expectation identity over `A`, then freeze
    -- the future row at `z` because `A` already pins down the state at time `n`.
    calc
      μ.real (A ∩ {ω | X (n + m) ω = y}) =
          ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
            rw [setIntegral_condExp
              (generatedFiltrationSpace_le_ambient X hReal.measurable_process n)
              hIndicatorIntegrable hA_meas, ← integral_indicator hA_measAmbient]
            symm
            simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
              smul_eq_mul] using integral_indicator_const (1 : ℝ) (hA_measAmbient.inter hB_meas)
      _ = ∫ ω in A, (((discreteMatrixKernel p ^ m) (X n ω)).real ({y} : Set E)) ∂ μ := by
            exact integral_congr_ae hMarkovGenerated.restrict
      _ = ∫ _ in A, (((discreteMatrixKernel p ^ m) z ({y} : Set E)).toReal) ∂ μ := by
            refine integral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient] with ω hω
            have hω : X n ω = z := hA_sub hω
            rw [hω]
            rfl
      _ = (((discreteMatrixKernel p ^ m) z ({y} : Set E)).toReal) * μ.real A := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hleft_ne_top :
      (P s : Measure Ω) (A ∩ {ω | X (n + m) ω = y}) ≠ ⊤ :=
    measure_ne_top _ _
  letI : IsMarkovKernel (discreteMatrixKernel p ^ m) := hReal.semigroup.isMarkovKernel m
  have hkernel_ne_top : ((discreteMatrixKernel p ^ m) z) ({y} : Set E) ≠ ⊤ :=
    measure_ne_top _ _
  have hA_ne_top : (P s : Measure Ω) A ≠ ⊤ :=
    measure_ne_top _ _
  have hkernel_toReal_nonneg : 0 ≤ (((discreteMatrixKernel p ^ m) z ({y} : Set E)).toReal) :=
    ENNReal.toReal_nonneg
  -- Proof comment: transport the real-valued factorization back to `ℝ≥0∞`.
  calc
    (P s : Measure Ω) (A ∩ {ω | X (n + m) ω = y}) =
        ENNReal.ofReal ((P s : Measure Ω).real (A ∩ {ω | X (n + m) ω = y})) := by
          symm
          exact ENNReal.ofReal_toReal hleft_ne_top
    _ = ENNReal.ofReal
        ((((discreteMatrixKernel p ^ m) z ({y} : Set E)).toReal) * (P s : Measure Ω).real A) := by
          rw [hstep]
    _ = ((discreteMatrixKernel p ^ m) z ({y} : Set E)) * (P s : Measure Ω) A := by
          rw [ENNReal.ofReal_mul hkernel_toReal_nonneg, ENNReal.ofReal_toReal hkernel_ne_top, Measure.real_def,
            ENNReal.ofReal_toReal hA_ne_top]

/-- Helper for Exercise 17.6.6: the weighted start law evaluates a start-state event by keeping
only the `x`-row of the weighted sum. -/
private lemma weightedStartLaw_apply_startState_beforeReturn [Countable E] {π : Measure E}
    (x y : E) (k : ℕ) :
    weightedStartLaw (P := P) (π := π)
      {ω | X 0 ω = x ∧ X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} =
        π ({x} : Set E) *
          (P x : Measure Ω) {ω | X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} := by
  classical
  let hReal : IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let A : Set Ω := {ω | X 0 ω = x ∧ X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}
  let B : Set Ω := {ω | X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}
  have hState0_meas : MeasurableSet {ω | X 0 ω = x} := by
    simpa [Set.preimage] using
      (hReal.measurable_process 0) (MeasurableSet.singleton x)
  have hTail_meas : MeasurableSet {ω | (k : ℕ∞) < (τ_[X, x]^1) ω} :=
    measurableSet_firstReturnTimeTailLocal (κ := fun n ↦ discreteMatrixKernel p ^ n)
      (P := P) (X := X) x k
  have hB_meas : MeasurableSet B := by
    have hStateK : MeasurableSet {ω | X k ω = y} := by
      simpa [Set.preimage] using
        (hReal.measurable_process k) (MeasurableSet.singleton y)
    exact hStateK.inter hTail_meas
  have hA_eq : A = {ω | X 0 ω = x} ∩ B := by
    ext ω
    simp [A, B, and_left_comm, and_assoc]
  have hA_meas : MeasurableSet A := by
    rw [hA_eq]
    exact hState0_meas.inter hB_meas
  rw [weightedStartLaw, Measure.sum_apply _ hA_meas]
  simp_rw [Measure.smul_apply]
  have hPx_stateNe_zero : (P x : Measure Ω) {ω | X 0 ω ≠ x} = 0 := by
    have hpreimage : {ω | X 0 ω ≠ x} = X 0 ⁻¹' ({x} : Set E)ᶜ := by
      ext ω
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x).compl]
    rw [hReal.initial_eq x]
    simp
  have hAx : (P x : Measure Ω) A = (P x : Measure Ω) B := by
    have hDecomp : B = A ∪ (B ∩ {ω | X 0 ω ≠ x}) := by
      ext ω
      by_cases hω : X 0 ω = x <;> simp [A, B, hω]
    have hDisj : Disjoint A (B ∩ {ω | X 0 ω ≠ x}) := by
      refine Set.disjoint_left.2 ?_
      intro ω hωA hωB
      exact hωB.2 hωA.1
    have hRest_zero : (P x : Measure Ω) (B ∩ {ω | X 0 ω ≠ x}) = 0 := by
      exact measure_mono_null Set.inter_subset_right hPx_stateNe_zero
    calc
      (P x : Measure Ω) A = (P x : Measure Ω) A + 0 := by simp
      _ = (P x : Measure Ω) A + (P x : Measure Ω) (B ∩ {ω | X 0 ω ≠ x}) := by
            rw [hRest_zero]
      _ = (P x : Measure Ω) (A ∪ (B ∩ {ω | X 0 ω ≠ x})) := by
            rw [measure_union hDisj (hB_meas.inter hState0_meas.compl)]
      _ = (P x : Measure Ω) B := by
            simpa using congrArg (fun s : Set Ω ↦ (P x : Measure Ω) s) hDecomp.symm
  have hz_zero : ∀ z : E, z ≠ x → (P z : Measure Ω) A = 0 := by
    intro z hzx
    have hStateZero : (P z : Measure Ω) {ω | X 0 ω = x} = 0 := by
      have hpreimage : {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set E) := by
        ext ω
        simp
      rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x)]
      rw [hReal.initial_eq z]
      simp [hzx]
    have hA_sub : A ⊆ {ω | X 0 ω = x} := by
      intro ω hω
      exact hω.1
    exact le_antisymm
      (le_trans (measure_mono hA_sub) (by simpa [hStateZero]))
      bot_le
  -- Proof comment: the event already forces `X 0 = x`, so every row except the `x`-row vanishes.
  calc
    ∑' z : E, π ({z} : Set E) * (P z : Measure Ω) A
        = π ({x} : Set E) * (P x : Measure Ω) A := by
            refine tsum_eq_single x ?_
            intro z hzx
            simp [hz_zero z hzx]
    _ = π ({x} : Set E) * (P x : Measure Ω) B := by rw [hAx]

/-- Helper for Exercise 17.6.6: off the reference diagonal, the time-`k + 1` before-return event
already implies that the chain is still before the first return at time `k + 1`. -/
private lemma beforeReturnStep_offDiag_eq_succTail
    {x y : E} (hyx : y ≠ x) (k : ℕ) :
    (P x : Measure Ω) {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} =
      (P x : Measure Ω) {ω | X (k + 1) ω = y ∧ (((k + 1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} := by
  have hSet :
      {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} =
        {ω | X (k + 1) ω = y ∧ (((k + 1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} := by
    ext ω
    constructor
    · rintro ⟨hstate, htail⟩
      have hsuccTail : (((k + 1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω) := by
        by_contra hnot
        have hle : (τ_[X, x]^1) ω ≤ k + 1 := le_of_not_gt hnot
        have hlt_top : (τ_[X, x]^1) ω < ⊤ := lt_of_le_of_lt hle (by simp)
        let m := ENat.lift ((τ_[X, x]^1) ω) hlt_top
        have hm_eq : (m : ℕ∞) = (τ_[X, x]^1) ω :=
          ENat.coe_lift ((τ_[X, x]^1) ω) hlt_top
        have hm_le : m ≤ k + 1 := by
          simpa [m, hm_eq] using hle
        have hk_lt_m : k < m := by
          simpa [m, hm_eq] using htail
        have hm : m = k + 1 := Nat.le_antisymm hm_le (Nat.succ_le_of_lt hk_lt_m)
        have hτeq : (τ_[X, x]^1) ω = k + 1 := by
          calc
            (τ_[X, x]^1) ω = (m : ℕ∞) := hm_eq.symm
            _ = k + 1 := by simpa [hm]
        have hxstate :
            X (k + 1) ω = x := by
          have hcoene : ((k + 1 : ℕ) : ℕ∞) ≠ ⊤ := ENat.coe_ne_top (k + 1)
          have hne_top : (τ_[X, x]^1) ω ≠ ⊤ := by simpa [hτeq] using hcoene
          have hmem :
              X (((τ_[X, x]^1) ω).untopA) ω = x := by
            have h :
                X (MeasureTheory.hittingAfter X ({x} : Set E) 1 ω).untopA ω ∈ ({x} : Set E) :=
              hittingAfter_mem_set_of_ne_top (by simpa [iteratedEntranceTime_one] using hne_top)
            simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using h
          have huntop : ((τ_[X, x]^1) ω).untopA = k + 1 := by
            rw [WithTop.untopA_eq_untop hne_top]
            simpa [ENat.lift, hτeq] using (ENat.lift_coe (k + 1))
          simpa [huntop] using hmem
        exact hyx (hstate.symm.trans hxstate)
      exact ⟨hstate, hsuccTail⟩
    · rintro ⟨hstate, htail⟩
      exact ⟨hstate, lt_trans (by exact_mod_cast Nat.lt_succ_self k) htail⟩
  rw [hSet]

/-- Helper for Exercise 17.6.6: the remainder term in the textbook induction is the weighted-start
mass of paths that start away from `x`, land at `y` at time `n`, and have not yet returned to
`x`. -/
private def offDiagFirstReturnRemainder (x y : E) (n : ℕ) : Set Ω :=
  {ω | X 0 ω ≠ x ∧ X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}

/-- Helper for Exercise 17.6.6: the off-diagonal remainder event is measurable. -/
private lemma measurableSet_offDiagFirstReturnRemainder [Countable E]
    (x y : E) (n : ℕ) :
    MeasurableSet (offDiagFirstReturnRemainder (X := X) x y n) := by
  let hReal : IsMarkovProcessRealization
      (fun k ↦ discreteMatrixKernel p ^ k) P X := inferInstance
  have hState0 : MeasurableSet {ω | X 0 ω ≠ x} := by
    have hEq : {ω | X 0 ω ≠ x} = {ω | X 0 ω = x}ᶜ := by
      ext ω
      simp
    rw [hEq]
    exact ((hReal.measurable_process 0) (MeasurableSet.singleton x)).compl
  have hStateN : MeasurableSet {ω | X n ω = y} := by
    simpa [Set.preimage] using
      (hReal.measurable_process n) (MeasurableSet.singleton y)
  have hTail : MeasurableSet {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} :=
    measurableSet_firstReturnTimeTailLocal (κ := fun k ↦ discreteMatrixKernel p ^ k)
      (P := P) (X := X) x n
  -- Proof comment: the remainder event is the intersection of one time-zero event, one time-`n`
  -- event, and the first-return tail event.
  exact hState0.inter (hStateN.inter hTail)

/-- Helper for Exercise 17.6.6: the off-diagonal remainder event is already measurable with
respect to the time-`n` history filtration. -/
private lemma measurableSet_offDiagFirstReturnRemainderInFiltration [Countable E]
    (x y : E) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace X n]
      (offDiagFirstReturnRemainder (X := X) x y n) := by
  have hX0_meas :
      Measurable[generatedFiltrationSpace X n] (X 0) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le 0 <| le_iSup_of_le (Nat.zero_le n) le_rfl
  have hXn_meas :
      Measurable[generatedFiltrationSpace X n] (X n) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le n <| le_iSup_of_le le_rfl le_rfl
  have hState0 : MeasurableSet[generatedFiltrationSpace X n] {ω | X 0 ω ≠ x} := by
    have hEq : {ω | X 0 ω ≠ x} = X 0 ⁻¹' ({x} : Set E)ᶜ := by
      ext ω
      simp
    rw [hEq]
    exact (hX0_meas (MeasurableSet.singleton x)).compl
  have hStateN : MeasurableSet[generatedFiltrationSpace X n] {ω | X n ω = y} := by
    simpa [Set.preimage] using hXn_meas (MeasurableSet.singleton y)
  have hTail : MeasurableSet[generatedFiltrationSpace X n] {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
    have hEq :
        {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} = {ω | (τ_[X, x]^1) ω ≤ n}ᶜ := by
      ext ω
      simp
    rw [hEq]
    have hLe :
        MeasurableSet[generatedFiltrationSpace X n] {ω | (τ_[X, x]^1) ω ≤ n} := by
      have hEqLe :
          {ω | (τ_[X, x]^1) ω ≤ n} =
            ⋃ j ∈ ((Finset.Icc 1 n : Finset ℕ) : Set ℕ), X j ⁻¹' ({x} : Set E) := by
        ext ω
        simp [firstReturnTime_le_iffLocal, Finset.mem_Icc]
      rw [hEqLe]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
      have hXj :
          Measurable[generatedFiltrationSpace X n] (X j) := by
        refine Measurable.of_comap_le ?_
        exact le_iSup_of_le j <| le_iSup_of_le hjn le_rfl
      simpa using hXj (MeasurableSet.singleton x)
    exact hLe.compl
  -- Proof comment: the same three ingredients as in the ambient measurability proof all live in
  -- the time-`n` filtration.
  exact hState0.inter (hStateN.inter hTail)

/-- Helper for Exercise 17.6.6: a filtration-measurable event that already pins down the state at
time `n` factors under the weighted start law through the `m`-step transition mass from that
state. -/
private lemma weightedStartLaw_inter_prefix_stepEvent_eq_mul [Countable E] {π : Measure E}
    {A : Set Ω} {z y : E} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = z}) :
    weightedStartLaw (P := P) (π := π) (A ∩ {ω | X (n + m) ω = y}) =
      ((discreteMatrixKernel p ^ m) z ({y} : Set E)) *
        weightedStartLaw (P := P) (π := π) A := by
  classical
  let hReal : IsMarkovProcessRealization
      (fun k ↦ discreteMatrixKernel p ^ k) P X := inferInstance
  have hA_measAmbient : MeasurableSet A := by
    exact (generatedFiltrationSpace_le_ambient X hReal.measurable_process n) _ hA_meas
  have hStep_meas : MeasurableSet {ω | X (n + m) ω = y} := by
    simpa [Set.preimage] using
      (hReal.measurable_process (n + m)) (MeasurableSet.singleton y)
  -- Proof comment: factor each start-state row through the fixed state `z`, then pull the common
  -- transition mass out of the countable weighted sum.
  calc
    weightedStartLaw (P := P) (π := π) (A ∩ {ω | X (n + m) ω = y})
        = ∑' s : E, π ({s} : Set E) * (P s : Measure Ω) (A ∩ {ω | X (n + m) ω = y}) := by
            rw [weightedStartLaw, Measure.sum_apply _ (hA_measAmbient.inter hStep_meas)]
            simpa [Measure.smul_apply, smul_eq_mul]
    _ = ∑' s : E, π ({s} : Set E) *
          (((discreteMatrixKernel p ^ m) z ({y} : Set E)) * (P s : Measure Ω) A) := by
            refine tsum_congr fun s ↦ ?_
            rw [measure_inter_prefix_stepEvent_eq_mulLocal
              (p := p) (P := P) (X := X) (s := s) (z := z) (y := y)
              (n := n) (m := m) hA_meas hA_sub]
    _ = ∑' s : E, ((discreteMatrixKernel p ^ m) z ({y} : Set E)) *
          (π ({s} : Set E) * (P s : Measure Ω) A) := by
            refine tsum_congr fun s ↦ ?_
            simpa [mul_assoc, mul_left_comm, mul_comm]
    _ = ((discreteMatrixKernel p ^ m) z ({y} : Set E)) *
          ∑' s : E, π ({s} : Set E) * (P s : Measure Ω) A := by
            rw [ENNReal.tsum_mul_left]
    _ = ((discreteMatrixKernel p ^ m) z ({y} : Set E)) *
          weightedStartLaw (P := P) (π := π) A := by
            rw [weightedStartLaw, Measure.sum_apply _ hA_measAmbient]
            simpa [Measure.smul_apply, smul_eq_mul]

/-- Helper for Exercise 17.6.6: the weighted start law sees the one-step `x → y` contribution as
exactly the first before-return excursion term. -/
private lemma weightedStartLaw_startStep_offDiag [Countable E] {π : Measure E}
    {x y : E} (hyx : y ≠ x) :
    π ({x} : Set E) * ((discreteMatrixKernel p ^ 1) x ({y} : Set E)) =
      weightedStartLaw (P := P) (π := π)
        {ω | X 0 ω = x ∧ X 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} := by
  let hReal : IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hStateOne :
      (P x : Measure Ω) {ω | X 1 ω = y} =
        ((discreteMatrixKernel p ^ 1) x) ({y} : Set E) := by
    have hpreimage : {ω | X 1 ω = y} = X 1 ⁻¹' ({y} : Set E) := by
      ext ω
      simp
    rw [hpreimage]
    rw [← Measure.map_apply (hReal.measurable_process 1) (MeasurableSet.singleton y)]
    rw [hReal.transition_eq x 1]
  have hTauPos : ∀ ω : Ω, (0 : ℕ∞) < (τ_[X, x]^1) ω := by
    intro ω
    have hτge1 : (1 : ℕ∞) ≤ (τ_[X, x]^1) ω := by
      have h : (1 : ℕ) ≤ MeasureTheory.hittingAfter X ({x} : Set E) 1 ω := le_hittingAfter ω
      simpa [iteratedEntranceTime_one] using h
    exact lt_of_lt_of_le (by simp) hτge1
  have hTailZero :
      {ω | X 1 ω = y} = {ω | X 1 ω = y ∧ ((0 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} := by
    ext ω
    constructor
    · intro hω
      exact ⟨hω, hTauPos ω⟩
    · intro hω
      exact hω.1
  -- Proof comment: first rewrite the one-step kernel row as a path event, then upgrade the
  -- tail condition from `0 < τ_x^1` to `1 < τ_x^1` using the off-diagonal hypothesis.
  calc
    π ({x} : Set E) * ((discreteMatrixKernel p ^ 1) x ({y} : Set E))
        = π ({x} : Set E) * (P x : Measure Ω) {ω | X 1 ω = y} := by rw [hStateOne]
    _ = π ({x} : Set E) * (P x : Measure Ω)
          {ω | X 1 ω = y ∧ ((0 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} := by
            rw [← hTailZero]
    _ = π ({x} : Set E) * (P x : Measure Ω)
          {ω | X 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} := by
            rw [beforeReturnStep_offDiag_eq_succTail
              (p := p) (P := P) (X := X) (x := x) (y := y) hyx 0]
    _ = weightedStartLaw (P := P) (π := π)
          {ω | X 0 ω = x ∧ X 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} := by
            symm
            simpa using
              weightedStartLaw_apply_startState_beforeReturn
                (p := p) (P := P) (X := X) (π := π) x y 1

/-- Helper for Exercise 17.6.6: summing the off-diagonal remainder slices over the intermediate
state at time `n` recovers the propagated remainder event at time `n + 1`. -/
private lemma weightedStartLaw_remainderStepSliceSum [Countable E] {π : Measure E}
    {x y : E} (n : ℕ) :
    (∑' z : E,
      weightedStartLaw (P := P) (π := π)
        {ω | X 0 ω ≠ x ∧ X n ω = z ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω = y}) =
      weightedStartLaw (P := P) (π := π)
        {ω | X 0 ω ≠ x ∧ X (n + 1) ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  let A : E → Set Ω := fun z ↦
    {ω | X 0 ω ≠ x ∧ X n ω = z ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω = y}
  have hPairwise : Pairwise fun z₁ z₂ ↦ Disjoint (A z₁) (A z₂) := by
    intro z₁ z₂ hz
    refine Set.disjoint_left.2 ?_
    intro ω hω₁ hω₂
    exact hz (hω₁.2.1.symm.trans hω₂.2.1)
  have hMeas : ∀ z : E, MeasurableSet (A z) := by
    intro z
    have hBase :
        MeasurableSet (offDiagFirstReturnRemainder (X := X) x z n) :=
      measurableSet_offDiagFirstReturnRemainder (p := p) (P := P) (X := X) x z n
    let hReal : IsMarkovProcessRealization
        (fun k ↦ discreteMatrixKernel p ^ k) P X := inferInstance
    have hNext : MeasurableSet {ω | X (n + 1) ω = y} := by
      simpa [Set.preimage] using
        (hReal.measurable_process (n + 1)) (MeasurableSet.singleton y)
    have hEq :
        A z =
          offDiagFirstReturnRemainder (X := X) x z n ∩ {ω | X (n + 1) ω = y} := by
      ext ω
      simp [A, offDiagFirstReturnRemainder, and_assoc, and_left_comm, and_comm]
    rw [hEq]
    exact hBase.inter hNext
  have hUnion :
      (⋃ z : E, A z) =
        {ω | X 0 ω ≠ x ∧ X (n + 1) ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨z, hz⟩
      exact ⟨hz.1, hz.2.2.2, hz.2.2.1⟩
    · intro hω
      refine Set.mem_iUnion.2 ⟨X n ω, ?_⟩
      exact ⟨hω.1, rfl, hω.2.2, hω.2.1⟩
  -- Proof comment: the time-`n` state slices are pairwise disjoint and cover the propagated
  -- remainder event.
  rw [← hUnion]
  symm
  exact measure_iUnion hPairwise hMeas

/-- Helper for Exercise 17.6.6: summing the time-`k` before-return slices over the intermediate
state recovers the time-`k + 1` before-return event. -/
private lemma beforeReturnStepSliceSum_eq [Countable E]
    {x y : E} (k : ℕ) :
    (∑' z : E,
      (P x : Measure Ω)
        {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y}) =
      (P x : Measure Ω) {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} := by
  let A : E → Set Ω := fun z ↦
    {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y}
  have hPairwise : Pairwise fun z₁ z₂ ↦ Disjoint (A z₁) (A z₂) := by
    intro z₁ z₂ hz
    refine Set.disjoint_left.2 ?_
    intro ω hω₁ hω₂
    exact hz (hω₁.1.symm.trans hω₂.1)
  have hMeas : ∀ z : E, MeasurableSet (A z) := by
    intro z
    let hReal : IsMarkovProcessRealization
        (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
    have hXk : MeasurableSet {ω | X k ω = z} := by
      simpa [Set.preimage] using
        (hReal.measurable_process k) (MeasurableSet.singleton z)
    have hTail : MeasurableSet {ω | (k : ℕ∞) < (τ_[X, x]^1) ω} :=
      measurableSet_firstReturnTimeTailLocal (κ := fun n ↦ discreteMatrixKernel p ^ n)
        (P := P) (X := X) x k
    have hNext : MeasurableSet {ω | X (k + 1) ω = y} := by
      simpa [Set.preimage] using
        (hReal.measurable_process (k + 1)) (MeasurableSet.singleton y)
    have hEq :
        A z =
          {ω | X k ω = z} ∩
            ({ω | (k : ℕ∞) < (τ_[X, x]^1) ω} ∩ {ω | X (k + 1) ω = y}) := by
      ext ω
      simp [A, and_assoc]
    rw [hEq]
    exact hXk.inter (hTail.inter hNext)
  have hUnion :
      (⋃ z : E, A z) =
        {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨z, hz⟩
      exact ⟨hz.2.2, hz.2.1⟩
    · intro hω
      refine Set.mem_iUnion.2 ⟨X k ω, ?_⟩
      exact ⟨rfl, hω.2, hω.1⟩
  -- Proof comment: the state slices at time `k` are pairwise disjoint and cover the target
  -- before-return event.
  rw [← hUnion]
  symm
  exact measure_iUnion hPairwise hMeas

/-- Helper for Exercise 17.6.6: the event `X n = z` together with the first-return tail is
already measurable in the time-`n` filtration. -/
private lemma measurableSet_beforeReturnStateInFiltration [Countable E]
    (x z : E) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace X n]
      {ω | X n ω = z ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  have hXn :
      Measurable[generatedFiltrationSpace X n] (X n) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le n <| le_iSup_of_le le_rfl le_rfl
  have hState : MeasurableSet[generatedFiltrationSpace X n] {ω | X n ω = z} := by
    simpa [Set.preimage] using hXn (MeasurableSet.singleton z)
  have hTail :
      MeasurableSet[generatedFiltrationSpace X n] {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
    have hEq :
        {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} = {ω | (τ_[X, x]^1) ω ≤ n}ᶜ := by
      ext ω
      simp
    rw [hEq]
    have hLe :
        MeasurableSet[generatedFiltrationSpace X n] {ω | (τ_[X, x]^1) ω ≤ n} := by
      have hEqLe :
          {ω | (τ_[X, x]^1) ω ≤ n} =
            ⋃ j ∈ ((Finset.Icc 1 n : Finset ℕ) : Set ℕ), X j ⁻¹' ({x} : Set E) := by
        ext ω
        simp [firstReturnTime_le_iffLocal]
      rw [hEqLe]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
      have hXj :
          Measurable[generatedFiltrationSpace X n] (X j) := by
        refine Measurable.of_comap_le ?_
        exact le_iSup_of_le j <| le_iSup_of_le hjn le_rfl
      simpa using hXj (MeasurableSet.singleton x)
    exact hLe.compl
  exact hState.inter hTail

/-- Helper for Exercise 17.6.6: the off-diagonal remainder cannot already be at the reference
state `x` at time `n`. -/
private lemma offDiagFirstReturnRemainder_self_empty [Countable E]
    (x : E) (n : ℕ) :
    offDiagFirstReturnRemainder (X := X) x x n = (∅ : Set Ω) := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨hStart, hState, hTail⟩
    by_cases hn : n = 0
    · subst hn
      exact hStart hState
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hle : (τ_[X, x]^1) ω ≤ n :=
        (firstReturnTime_le_iffLocal (X := X) x n ω).2
          ⟨n, ⟨hn_pos, le_rfl⟩, hState⟩
      exact False.elim <| (not_lt_of_ge hle) hTail
  · simp

/-- Helper for Exercise 17.6.6: starting from `x`, the before-return event cannot be back at `x`
at any positive time. -/
private lemma beforeReturnStateMass_self_eq_zero [Countable E]
    (x : E) {k : ℕ} (hk : 0 < k) :
    (P x : Measure Ω) {ω | X k ω = x ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} = 0 := by
  have hEmpty :
      {ω | X k ω = x ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} = (∅ : Set Ω) := by
    ext ω
    constructor
    · intro hω
      have hle : (τ_[X, x]^1) ω ≤ k :=
        (firstReturnTime_le_iffLocal (X := X) x k ω).2
          ⟨k, ⟨hk, le_rfl⟩, hω.1⟩
      exact False.elim <| (not_lt_of_ge hle) hω.2
    · simp
  rw [hEmpty]
  simp

/-- Helper for Exercise 17.6.6: off the diagonal, the propagated weighted-start remainder event
already forces the stronger tail condition at time `n + 1`. -/
private lemma offDiagRemainderStep_eq_succ [Countable E]
    {x y : E} (hyx : y ≠ x) (n : ℕ) :
    {ω | X 0 ω ≠ x ∧ X (n + 1) ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} =
      offDiagFirstReturnRemainder (X := X) x y (n + 1) := by
  ext ω
  constructor
  · rintro ⟨hStart, hState, hTail⟩
    have hSuccTail : (((n + 1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω) := by
      by_contra hnot
      have hle : (τ_[X, x]^1) ω ≤ n + 1 := le_of_not_gt hnot
      have hlt_top : (τ_[X, x]^1) ω < ⊤ := lt_of_le_of_lt hle (by simp)
      let m := ENat.lift ((τ_[X, x]^1) ω) hlt_top
      have hm_eq : (m : ℕ∞) = (τ_[X, x]^1) ω :=
        ENat.coe_lift ((τ_[X, x]^1) ω) hlt_top
      have hm_le : m ≤ n + 1 := by
        simpa [m, hm_eq] using hle
      have hn_lt_m : n < m := by
        simpa [m, hm_eq] using hTail
      have hm : m = n + 1 := Nat.le_antisymm hm_le (Nat.succ_le_of_lt hn_lt_m)
      have hτeq : (τ_[X, x]^1) ω = n + 1 := by
        calc
          (τ_[X, x]^1) ω = (m : ℕ∞) := hm_eq.symm
          _ = n + 1 := by simpa [hm]
      have hxState : X (n + 1) ω = x := by
        have hcoene : ((n + 1 : ℕ) : ℕ∞) ≠ ⊤ := ENat.coe_ne_top (n + 1)
        have hne_top : (τ_[X, x]^1) ω ≠ ⊤ := by simpa [hτeq] using hcoene
        have hmem :
            X (((τ_[X, x]^1) ω).untopA) ω = x := by
          have h :
              X (MeasureTheory.hittingAfter X ({x} : Set E) 1 ω).untopA ω ∈ ({x} : Set E) :=
            hittingAfter_mem_set_of_ne_top (by simpa [iteratedEntranceTime_one] using hne_top)
          simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using h
        have huntop : ((τ_[X, x]^1) ω).untopA = n + 1 := by
          rw [WithTop.untopA_eq_untop hne_top]
          simpa [ENat.lift, hτeq] using ENat.lift_coe (n + 1)
        simpa [huntop] using hmem
      exact False.elim <| hyx (hState.symm.trans hxState)
    exact ⟨hStart, hState, hSuccTail⟩
  · rintro ⟨hStart, hState, hTail⟩
    exact ⟨hStart, hState, lt_trans (by exact_mod_cast Nat.lt_succ_self n) hTail⟩

/-- Helper for Exercise 17.6.6: the first excursion term together with the shifted
before-return tail over `Finset.Icc 1 n` is exactly the `Finset.Icc 1 (n + 1)` partial sum used
in the textbook decomposition. -/
private lemma sumBeforeReturnShift_eq_IccSucc
    {x y : E} (hyx : y ≠ x) (n : ℕ) :
    (P x : Measure Ω) {ω | X 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} +
      Finset.sum (Finset.Icc 1 n)
        (fun k ↦ (P x : Measure Ω) {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) =
      Finset.sum (Finset.Icc 1 (n + 1))
        (fun k ↦ (P x : Measure Ω) {ω | X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) := by
  have hShift :
      Finset.sum (Finset.Icc 1 n)
        (fun k ↦ (P x : Measure Ω) {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) =
      Finset.sum (Finset.Icc 2 (n + 1))
        (fun k ↦ (P x : Measure Ω) {ω | X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) := by
    -- Proof comment: first upgrade each tail event from `k < τ_x^1` to `(k + 1) < τ_x^1`,
    -- then reindex the interval by the successor map.
    calc
      Finset.sum (Finset.Icc 1 n)
          (fun k ↦ (P x : Measure Ω) {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) =
        Finset.sum (Finset.Icc 1 n)
          (fun k ↦ (P x : Measure Ω)
            {ω | X (k + 1) ω = y ∧ (((k + 1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)}) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              exact beforeReturnStep_offDiag_eq_succTail
                (p := p) (P := P) (X := X) (x := x) (y := y) hyx k
      _ = Finset.sum ((Finset.Icc 1 n).image (fun k : ℕ ↦ k + 1))
          (fun k ↦ (P x : Measure Ω) {ω | X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) := by
            symm
            refine Finset.sum_image ?_
            intro a _ b _ hab
            exact Nat.succ.inj hab
      _ = Finset.sum (Finset.Icc 2 (n + 1))
          (fun k ↦ (P x : Measure Ω) {ω | X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) := by
            have hImage :
                (Finset.Icc 1 n).image (fun k : ℕ ↦ k + 1) = Finset.Icc 2 (n + 1) := by
              ext k
              simp [Finset.mem_Icc]
            rw [hImage]
  -- Proof comment: insert the `k = 1` term back into the shifted tail to recover the full
  -- `Finset.Icc 1 (n + 1)` partial sum.
  calc
    (P x : Measure Ω) {ω | X 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} +
        Finset.sum (Finset.Icc 1 n)
          (fun k ↦ (P x : Measure Ω) {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) =
      (P x : Measure Ω) {ω | X 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} +
        Finset.sum (Finset.Icc 2 (n + 1))
          (fun k ↦ (P x : Measure Ω) {ω | X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) := by
            rw [hShift]
    _ = Finset.sum (insert 1 (Finset.Icc 2 (n + 1)))
        (fun k ↦ (P x : Measure Ω) {ω | X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) := by
          have hnotin : 1 ∉ Finset.Icc 2 (n + 1) := by
            simp
          rw [Finset.sum_insert hnotin]
    _ = Finset.sum (Finset.Icc 1 (n + 1))
        (fun k ↦ (P x : Measure Ω) {ω | X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) := by
          have hInsert :
              insert 1 (Finset.Icc 2 (n + 1)) = Finset.Icc 1 (n + 1) := by
            ext k
            simp [Finset.mem_Icc]
            omega
          rw [hInsert]

/-- Helper for Exercise 17.6.6: intersecting the off-diagonal remainder event with the next-state
singleton gives the canonical four-conjunct step slice used in the reassembly lemma. -/
private lemma offDiagFirstReturnRemainder_stepSlice_eq
    (x z y : E) (n : ℕ) :
    offDiagFirstReturnRemainder (X := X) x z n ∩ {ω | X (n + 1) ω = y} =
      {ω | X 0 ω ≠ x ∧ X n ω = z ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω = y} := by
  -- Proof comment: this is the canonical reassociation of the remainder event with the one-step
  -- state event.
  ext ω
  simp [offDiagFirstReturnRemainder, and_assoc, and_left_comm, and_comm]

/-- Helper for Exercise 17.6.6: intersecting a before-return state slice with the next-state
singleton gives the canonical three-conjunct step slice used in the reassembly lemma. -/
private lemma beforeReturnState_stepSlice_eq
    (x z y : E) (k : ℕ) :
    {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} ∩ {ω | X (k + 1) ω = y} =
      {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y} := by
  -- Proof comment: the before-return slice only needs a single reassociation with the next-step
  -- singleton event.
  ext ω
  simp [and_assoc]

/-- Helper for Exercise 17.6.6: a time-`k` before-return state slice transports through one more
step to the corresponding canonical step slice. -/
private lemma beforeReturnStepSliceMass_eq [Countable E]
    (x z y : E) (k : ℕ) :
    (P x : Measure Ω) {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} *
      ((discreteMatrixKernel p ^ 1) z ({y} : Set E)) =
        (P x : Measure Ω)
          {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y} := by
  -- Proof comment: first transport the one-step factor through the prefix event, then rewrite
  -- the resulting intersection into the canonical step-slice form.
  calc
    (P x : Measure Ω) {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} *
        ((discreteMatrixKernel p ^ 1) z ({y} : Set E)) =
        ((discreteMatrixKernel p ^ 1) z ({y} : Set E)) *
          (P x : Measure Ω) {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} := by
            rw [mul_comm]
    _ = (P x : Measure Ω)
        ({ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} ∩ {ω | X (k + 1) ω = y}) := by
          symm
          exact measure_inter_prefix_stepEvent_eq_mulLocal
            (p := p) (P := P) (X := X) (s := x) (z := z) (y := y) (n := k) (m := 1)
            (measurableSet_beforeReturnStateInFiltration (p := p) (P := P) (X := X) x z k)
            (by
              intro ω hω
              exact hω.1)
    _ = (P x : Measure Ω)
        {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y} := by
          rw [beforeReturnState_stepSlice_eq (p := p) (P := P) (X := X) x z y k]

/-- Helper for Exercise 17.6.6: the canonical step slice at time `k` vanishes on the reference
state `x`, because the chain cannot return to `x` before the first positive return time. -/
private lemma beforeReturnSelfStepSliceMass_eq_zero [Countable E]
    (x y : E) {k : ℕ} (hk : 0 < k) :
    (P x : Measure Ω)
      {ω | X k ω = x ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y} = 0 := by
  have hBase :
      (P x : Measure Ω) {ω | X k ω = x ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} = 0 :=
    beforeReturnStateMass_self_eq_zero (p := p) (P := P) (X := X) x hk
  have hSub :
      {ω | X k ω = x ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y} ⊆
        {ω | X k ω = x ∧ (k : ℕ∞) < (τ_[X, x]^1) ω} := by
    intro ω hω
    exact ⟨hω.1, hω.2.1⟩
  exact le_antisymm
    (le_trans (measure_mono hSub) (by simpa using hBase))
    bot_le

/-- Helper for Exercise 17.6.6: after the before-return slices are in canonical step form, the
outer `tsum` over states commutes with the finite sum over `k ∈ Finset.Icc 1 n`. -/
private lemma tsum_beforeReturnStepSlice_comm [Countable E]
    {x y : E} (n : ℕ) :
    (∑' z : E,
      Finset.sum (Finset.Icc 1 n)
        (fun k ↦ (P x : Measure Ω)
          {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y})) =
      Finset.sum (Finset.Icc 1 n)
        (fun k ↦ ∑' z : E,
          (P x : Measure Ω)
            {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y}) := by
  -- Proof comment: rewrite the finite sum as a `tsum` over the finite subtype, swap the two
  -- `tsum`s once, and then return to the `Finset` presentation.
  let stepSlice : E → ℕ → ℝ≥0∞ := fun z k ↦
    (P x : Measure Ω)
      {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y}
  calc
    (∑' z : E,
      Finset.sum (Finset.Icc 1 n)
        (fun k ↦ (P x : Measure Ω)
          {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y})) =
        ∑' z : E, ∑' k : Finset.Icc 1 n, stepSlice z k := by
          refine tsum_congr fun z ↦ ?_
          rw [← Finset.sum_attach, Finset.attach_eq_univ, tsum_fintype]
    _ = ∑' k : Finset.Icc 1 n, ∑' z : E, stepSlice z k := ENNReal.tsum_comm
    _ = Finset.sum (Finset.Icc 1 n)
          (fun k ↦ ∑' z : E,
            (P x : Measure Ω)
              {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y}) := by
            rw [← Finset.sum_attach, Finset.attach_eq_univ, tsum_fintype]

/-- Helper for Exercise 17.6.6: propagating the off-diagonal remainder one more step and summing
over the intermediate state yields the next remainder term. -/
private lemma weightedStartLaw_remainderTail_eq [Countable E] {π : Measure E}
    [DecidableEq E]
    {x y : E} (hyx : y ≠ x) (n : ℕ) :
    (∑' z : E, ite (z = x) 0
      (weightedStartLaw (P := P) (π := π)
        (offDiagFirstReturnRemainder (X := X) x z n) *
          ((discreteMatrixKernel p ^ 1) z ({y} : Set E)))) =
      weightedStartLaw (P := P) (π := π)
        (offDiagFirstReturnRemainder (X := X) x y (n + 1)) := by
  classical
  -- Proof comment: first rewrite every summand into the canonical step-slice measure, using the
  -- empty `z = x` slice and the one-step transport lemma off the diagonal.
  calc
    (∑' z : E, ite (z = x) 0
      (weightedStartLaw (P := P) (π := π)
        (offDiagFirstReturnRemainder (X := X) x z n) *
          ((discreteMatrixKernel p ^ 1) z ({y} : Set E)))) =
        ∑' z : E,
          weightedStartLaw (P := P) (π := π)
            {ω | X 0 ω ≠ x ∧ X n ω = z ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω = y} := by
              refine tsum_congr fun z ↦ ?_
              by_cases hzx : z = x
              · subst z
                have hZero :
                    weightedStartLaw (P := P) (π := π)
                      {ω | X 0 ω ≠ x ∧ X n ω = x ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧
                        X (n + 1) ω = y} = 0 := by
                  rw [← offDiagFirstReturnRemainder_stepSlice_eq
                    (p := p) (P := P) (X := X) x x y n,
                    offDiagFirstReturnRemainder_self_empty (p := p) (P := P) (X := X) x n]
                  simp
                simpa [hZero]
              · calc
                  ite (z = x) 0
                      (weightedStartLaw (P := P) (π := π)
                        (offDiagFirstReturnRemainder (X := X) x z n) *
                          ((discreteMatrixKernel p ^ 1) z ({y} : Set E))) =
                      weightedStartLaw (P := P) (π := π)
                        (offDiagFirstReturnRemainder (X := X) x z n) *
                          ((discreteMatrixKernel p ^ 1) z ({y} : Set E)) := by
                            simp [hzx]
                  _ = ((discreteMatrixKernel p ^ 1) z ({y} : Set E)) *
                      weightedStartLaw (P := P) (π := π)
                        (offDiagFirstReturnRemainder (X := X) x z n) := by
                          rw [mul_comm]
                  _ = weightedStartLaw (P := P) (π := π)
                      (offDiagFirstReturnRemainder (X := X) x z n ∩
                        {ω | X (n + 1) ω = y}) := by
                          symm
                          exact weightedStartLaw_inter_prefix_stepEvent_eq_mul
                            (p := p) (P := P) (X := X) (π := π)
                            (A := offDiagFirstReturnRemainder (X := X) x z n)
                            (z := z) (y := y) (n := n) (m := 1)
                            (measurableSet_offDiagFirstReturnRemainderInFiltration
                              (p := p) (P := P) (X := X) x z n)
                            (by
                              intro ω hω
                              exact hω.2.1)
                  _ = weightedStartLaw (P := P) (π := π)
                      {ω | X 0 ω ≠ x ∧ X n ω = z ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧
                        X (n + 1) ω = y} := by
                          rw [offDiagFirstReturnRemainder_stepSlice_eq
                            (p := p) (P := P) (X := X) x z y n]
    _ = weightedStartLaw (P := P) (π := π)
          {ω | X 0 ω ≠ x ∧ X (n + 1) ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
            simpa using
              weightedStartLaw_remainderStepSliceSum
                (p := p) (P := P) (X := X) (π := π) (x := x) (y := y) n
    _ = weightedStartLaw (P := P) (π := π)
          (offDiagFirstReturnRemainder (X := X) x y (n + 1)) := by
            rw [offDiagRemainderStep_eq_succ (p := p) (P := P) (X := X) hyx n]

/-- Helper for Exercise 17.6.6: propagating the finite before-return excursion partial sums one
step forward and summing over the intermediate state yields the shifted excursion tail. -/
private lemma beforeReturnExcursionTail_eq [Countable E] {π : Measure E}
    [DecidableEq E]
    {x y : E} (n : ℕ) :
    (∑' z : E, ite (z = x) 0
      ((π ({x} : Set E) *
        Finset.sum (Finset.Icc 1 n)
          (fun k ↦ (P x : Measure Ω)
            {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω})) *
          ((discreteMatrixKernel p ^ 1) z ({y} : Set E)))) =
      π ({x} : Set E) *
        Finset.sum (Finset.Icc 1 n)
          (fun k ↦ (P x : Measure Ω)
            {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) := by
  classical
  -- Proof comment: rewrite each `z`-summand into a finite sum of canonical step slices, kill the
  -- `z = x` branch via the self-return zero lemma, and only then commute the finite sum with
  -- the outer `tsum`.
  calc
    (∑' z : E, ite (z = x) 0
      ((π ({x} : Set E) *
        Finset.sum (Finset.Icc 1 n)
          (fun k ↦ (P x : Measure Ω)
            {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω})) *
          ((discreteMatrixKernel p ^ 1) z ({y} : Set E)))) =
        ∑' z : E, π ({x} : Set E) *
          Finset.sum (Finset.Icc 1 n)
            (fun k ↦ (P x : Measure Ω)
              {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y}) := by
              refine tsum_congr fun z ↦ ?_
              by_cases hzx : z = x
              · subst z
                have hSumZero :
                    Finset.sum (Finset.Icc 1 n)
                      (fun k ↦ (P x : Measure Ω)
                        {ω | X k ω = x ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y}) = 0 := by
                  refine Finset.sum_eq_zero ?_
                  intro k hk
                  exact beforeReturnSelfStepSliceMass_eq_zero
                    (p := p) (P := P) (X := X) x y ((Finset.mem_Icc.mp hk).1)
                simpa [hSumZero]
              · calc
                  ite (z = x) 0
                      ((π ({x} : Set E) *
                        Finset.sum (Finset.Icc 1 n)
                          (fun k ↦ (P x : Measure Ω)
                            {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω})) *
                        ((discreteMatrixKernel p ^ 1) z ({y} : Set E))) =
                      (π ({x} : Set E) *
                        Finset.sum (Finset.Icc 1 n)
                          (fun k ↦ (P x : Measure Ω)
                            {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω})) *
                        ((discreteMatrixKernel p ^ 1) z ({y} : Set E)) := by
                          simp [hzx]
                  _ = π ({x} : Set E) *
                      (Finset.sum (Finset.Icc 1 n)
                        (fun k ↦ (P x : Measure Ω)
                          {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) *
                            ((discreteMatrixKernel p ^ 1) z ({y} : Set E))) := by
                              rw [mul_assoc, Finset.sum_mul]
                  _ = π ({x} : Set E) *
                      Finset.sum (Finset.Icc 1 n)
                        (fun k ↦ (P x : Measure Ω)
                          {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧
                            X (k + 1) ω = y}) := by
                              have hStepSlices :
                                  (Finset.sum (Finset.Icc 1 n)
                                    (fun k ↦ (P x : Measure Ω)
                                      {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω})) *
                                        ((discreteMatrixKernel p ^ 1) z ({y} : Set E)) =
                                    Finset.sum (Finset.Icc 1 n)
                                      (fun k ↦ (P x : Measure Ω)
                                        {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧
                                          X (k + 1) ω = y}) := by
                                    rw [Finset.sum_mul]
                                    refine Finset.sum_congr rfl ?_
                                    intro k hk
                                    exact beforeReturnStepSliceMass_eq
                                      (p := p) (P := P) (X := X) x z y k
                              exact congrArg (fun t : ℝ≥0∞ ↦ π ({x} : Set E) * t) hStepSlices
    _ = π ({x} : Set E) *
          (∑' z : E,
            Finset.sum (Finset.Icc 1 n)
              (fun k ↦ (P x : Measure Ω)
                {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y})) := by
            rw [ENNReal.tsum_mul_left]
    _ = π ({x} : Set E) *
          Finset.sum (Finset.Icc 1 n)
            (fun k ↦ ∑' z : E,
              (P x : Measure Ω)
                {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω ∧ X (k + 1) ω = y}) := by
            rw [tsum_beforeReturnStepSlice_comm (p := p) (P := P) (X := X) (x := x) (y := y) n]
    _ = π ({x} : Set E) *
          Finset.sum (Finset.Icc 1 n)
            (fun k ↦ (P x : Measure Ω)
              {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) := by
            refine congrArg (fun t : ℝ≥0∞ ↦ π ({x} : Set E) * t) ?_
            refine Finset.sum_congr rfl ?_
            intro k hk
            simpa using
              beforeReturnStepSliceSum_eq (p := p) (P := P) (X := X) (x := x) (y := y) k

/-- Helper for Exercise 17.6.6: the source induction identifies the singleton mass `π ({y})`
with the weighted-start remainder plus the finite before-return excursion sum. -/
private lemma weightedStartLaw_offDiag_firstReturnDecomposition [Countable E] {π : Measure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π)
    {x y : E} (hyx : y ≠ x) (n : ℕ) :
    π ({y} : Set E) =
      weightedStartLaw (P := P) (π := π) (offDiagFirstReturnRemainder (X := X) x y n) +
        π ({x} : Set E) *
          Finset.sum (Finset.Icc 1 n)
            (fun k ↦ (P x : Measure Ω) {ω | X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) := by
  -- Route correction: the old `lastVisitSlice` transport tried to move a future path slice from
  -- an over-expanded last-visit decomposition. The corrected route uses one-step invariance,
  -- splits off the `z = x` term, and propagates the remainder and excursion pieces separately.
  classical
  induction n generalizing y with
  | zero =>
      have hTauPos : ∀ ω : Ω, (0 : ℕ∞) < (τ_[X, x]^1) ω := by
        intro ω
        have hτge1 : (1 : ℕ∞) ≤ (τ_[X, x]^1) ω := by
          have h : (1 : ℕ) ≤ MeasureTheory.hittingAfter X ({x} : Set E) 1 ω := le_hittingAfter ω
          simpa [iteratedEntranceTime_one] using h
        exact lt_of_lt_of_le (by simp) hτge1
      have hRem0 :
          offDiagFirstReturnRemainder (X := X) x y 0 = {ω | X 0 ω = y} := by
        ext ω
        constructor
        · intro hω
          exact hω.2.1
        · intro hω
          refine ⟨?_, hω, hTauPos ω⟩
          intro hxω
          exact hyx (hω.symm.trans hxω)
      -- Proof comment: at time `0`, the remainder event is just the singleton state event, and
      -- the excursion sum is empty.
      calc
        π ({y} : Set E) = weightedStartLaw (P := P) (π := π) {ω | X 0 ω = y} := by
          symm
          exact weightedStartLaw_apply_stateEvent (p := p) (P := P) (X := X) hπ 0 y
        _ = weightedStartLaw (P := P) (π := π)
              (offDiagFirstReturnRemainder (X := X) x y 0) := by
                rw [hRem0]
        _ = weightedStartLaw (P := P) (π := π)
              (offDiagFirstReturnRemainder (X := X) x y 0) +
            π ({x} : Set E) *
              Finset.sum (Finset.Icc 1 0)
                (fun k ↦ (P x : Measure Ω) {ω | X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) := by
                  simp
  | succ n ih =>
      have hInv1 :
          π ({y} : Set E) =
            π ({x} : Set E) * ((discreteMatrixKernel p ^ 1) x ({y} : Set E)) +
              ∑' z : E, ite (z = x) 0 (π ({z} : Set E) *
                ((discreteMatrixKernel p ^ 1) z ({y} : Set E))) := by
        rw [invariantMeasureApplySingletonEqTsumPow (p := p) (P := P) (X := X) hπ 1 y,
          ENNReal.tsum_eq_add_tsum_ite x]
      have hStart :
          π ({x} : Set E) * ((discreteMatrixKernel p ^ 1) x ({y} : Set E)) =
            π ({x} : Set E) *
              (P x : Measure Ω)
                {ω | X 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} := by
        -- Proof comment: the `z = x` branch is the first excursion term of the decomposition.
        calc
          π ({x} : Set E) * ((discreteMatrixKernel p ^ 1) x ({y} : Set E)) =
              weightedStartLaw (P := P) (π := π)
                {ω | X 0 ω = x ∧ X 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} := by
                  exact weightedStartLaw_startStep_offDiag
                    (p := p) (P := P) (X := X) (π := π) hyx
          _ = π ({x} : Set E) *
                (P x : Measure Ω)
                  {ω | X 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} := by
                    simpa using
                      weightedStartLaw_apply_startState_beforeReturn
                        (p := p) (P := P) (X := X) (π := π) x y 1
      have hTail :
          (∑' z : E, ite (z = x) 0 (π ({z} : Set E) *
              ((discreteMatrixKernel p ^ 1) z ({y} : Set E)))) =
            weightedStartLaw (P := P) (π := π)
              (offDiagFirstReturnRemainder (X := X) x y (n + 1)) +
              π ({x} : Set E) *
                Finset.sum (Finset.Icc 1 n)
                  (fun k ↦ (P x : Measure Ω)
                    {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) := by
        have hExpand :
            (∑' z : E, ite (z = x) 0 (π ({z} : Set E) *
                ((discreteMatrixKernel p ^ 1) z ({y} : Set E)))) =
              (∑' z : E, ite (z = x) 0
                (weightedStartLaw (P := P) (π := π)
                  (offDiagFirstReturnRemainder (X := X) x z n) *
                    ((discreteMatrixKernel p ^ 1) z ({y} : Set E)))) +
              (∑' z : E, ite (z = x) 0
                ((π ({x} : Set E) *
                  Finset.sum (Finset.Icc 1 n)
                    (fun k ↦ (P x : Measure Ω)
                      {ω | X k ω = z ∧ (k : ℕ∞) < (τ_[X, x]^1) ω})) *
                    ((discreteMatrixKernel p ^ 1) z ({y} : Set E)))) := by
          rw [← ENNReal.tsum_add]
          refine tsum_congr fun z ↦ ?_
          by_cases hzx : z = x
          · subst z
            simp
          · rw [if_neg hzx, ih hzx, add_mul]
            simp [hzx]
        -- Proof comment: after applying the induction hypothesis to each off-diagonal state,
        -- the remainder slices recombine into the new remainder term and the excursion slices
        -- recombine into the shifted finite before-return sum.
        rw [hExpand,
          weightedStartLaw_remainderTail_eq
            (p := p) (P := P) (X := X) (π := π) (x := x) (y := y) hyx n,
          beforeReturnExcursionTail_eq
            (p := p) (P := P) (X := X) (π := π) (x := x) (y := y) n]
      -- Proof comment: combine the `z = x` contribution with the shifted excursion tail to
      -- recover the `Finset.Icc 1 (n + 1)` partial sum.
      calc
        π ({y} : Set E) =
            π ({x} : Set E) * ((discreteMatrixKernel p ^ 1) x ({y} : Set E)) +
              ∑' z : E, ite (z = x) 0 (π ({z} : Set E) *
                ((discreteMatrixKernel p ^ 1) z ({y} : Set E))) := hInv1
        _ =
            π ({x} : Set E) *
                (P x : Measure Ω)
                  {ω | X 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} +
              (weightedStartLaw (P := P) (π := π)
                (offDiagFirstReturnRemainder (X := X) x y (n + 1)) +
                π ({x} : Set E) *
                  Finset.sum (Finset.Icc 1 n)
                    (fun k ↦ (P x : Measure Ω)
                      {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω})) := by
                rw [hStart, hTail]
        _ =
            weightedStartLaw (P := P) (π := π)
              (offDiagFirstReturnRemainder (X := X) x y (n + 1)) +
                (π ({x} : Set E) *
                  (P x : Measure Ω)
                    {ω | X 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} +
                  π ({x} : Set E) *
                    Finset.sum (Finset.Icc 1 n)
                      (fun k ↦ (P x : Measure Ω)
                        {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω})) := by
                          simpa [add_assoc, add_left_comm, add_comm]
        _ =
            weightedStartLaw (P := P) (π := π)
              (offDiagFirstReturnRemainder (X := X) x y (n + 1)) +
                π ({x} : Set E) *
                  ((P x : Measure Ω)
                    {ω | X 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} +
                    Finset.sum (Finset.Icc 1 n)
                      (fun k ↦ (P x : Measure Ω)
                        {ω | X (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω})) := by
                          rw [← mul_add]
        _ =
            weightedStartLaw (P := P) (π := π)
              (offDiagFirstReturnRemainder (X := X) x y (n + 1)) +
                π ({x} : Set E) *
                  Finset.sum (Finset.Icc 1 (n + 1))
                    (fun k ↦ (P x : Measure Ω)
                      {ω | X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) := by
                        rw [sumBeforeReturnShift_eq_IccSucc
                          (p := p) (P := P) (X := X) (x := x) (y := y) hyx n]

/-- Helper for Exercise 17.6.6: the time-zero before-return term vanishes away from the
reference state `x`. -/
private lemma beforeReturnStateMassAtZero_eq_zero
    {x y : E} (hyx : y ≠ x) :
    (P x : Measure Ω) {ω | X 0 ω = y ∧ ((0 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} = 0 := by
  let hReal : IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hxy : x ≠ y := by
    simpa [eq_comm] using hyx
  have hStateZero :
      (P x : Measure Ω) {ω | X 0 ω = y} = 0 := by
    have hpreimage : {ω | X 0 ω = y} = X 0 ⁻¹' ({y} : Set E) := by
      ext ω
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton y)]
    rw [hReal.initial_eq x]
    simp [hxy]
  have hSubset :
      {ω | X 0 ω = y ∧ ((0 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} ⊆ {ω | X 0 ω = y} := by
    intro ω hω
    exact hω.1
  exact le_antisymm
    (by
      calc
        (P x : Measure Ω) {ω | X 0 ω = y ∧ ((0 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω}
            ≤ (P x : Measure Ω) {ω | X 0 ω = y} := measure_mono hSubset
        _ = 0 := hStateZero)
    bot_le

/-- Helper for Exercise 17.6.6: after zeroing the time-zero term, the finite range partial sums
match the `Finset.Icc 1 n` partial sums used in the last-visit decomposition. -/
private lemma sum_range_beforeReturn_eq_sum_Icc
    {x y : E} (hyx : y ≠ x) (n : ℕ) :
    Finset.sum (Finset.range (n + 1))
      (fun i ↦ if i = 0 then 0 else
        (P x : Measure Ω) {ω | X i ω = y ∧ (i : ℕ∞) < (τ_[X, x]^1) ω}) =
          Finset.sum (Finset.Icc 1 n)
            (fun i ↦ (P x : Measure Ω) {ω | X i ω = y ∧ (i : ℕ∞) < (τ_[X, x]^1) ω}) := by
  let a : ℕ → ℝ≥0∞ :=
    fun i ↦ (P x : Measure Ω) {ω | X i ω = y ∧ (i : ℕ∞) < (τ_[X, x]^1) ω}
  rw [Nat.range_succ_eq_Icc_zero]
  have hIcc :
      Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
    symm
    exact Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le n)
  have hnotin : 0 ∉ Finset.Icc 1 n := by
    simp
  rw [hIcc, Finset.sum_insert hnotin]
  simp only [a, if_pos rfl, zero_add]
  suffices
      ∀ i ∈ Finset.Icc 1 n, (if i = 0 then 0 else a i) = a i by
    simpa using Finset.sum_congr rfl this
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hi0 : i ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hi1)
  simp [a, hi0]

/-- Helper for Exercise 17.6.6: every invariant measure dominates its mass at the recurrent
reference state `x` times the return-cycle occupation measure rooted at `x`. -/
lemma invariantMeasureSingletonGeReferenceMassMulReturnCycle [Countable E] {x : E}
    {π : Measure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π)
    (hx : IsRecurrentState P X x)
    (hπ_finite : ∀ z : E, π ({z} : Set E) < ∞)
    (hπx_pos : 0 < π ({x} : Set E)) :
    ∀ y : E, π ({y} : Set E) ≥ π ({x} : Set E) * (μ[P, X] x) ({y} : Set E) := by
  intro y
  by_cases hyx : y = x
  · subst y
    -- Proof comment: on the diagonal, the return-cycle occupation measure has singleton mass `1`.
    rw [returnCycleOccupationMeasure_apply_singleton_self (p := p) (P := P) (X := X) x, mul_one]
  · have hSeries :
        (μ[P, X] x) ({y} : Set E) =
          ∑' i : ℕ,
            if i = 0 then 0 else
              (P x : Measure Ω) {ω | X i ω = y ∧ (i : ℕ∞) < (τ_[X, x]^1) ω} := by
      rw [returnCycleOccupationMeasure_apply_singleton, returnCycleOccupationMass]
      refine tsum_congr fun i ↦ ?_
      by_cases hi : i = 0
      · subst hi
        simpa using
          beforeReturnStateMassAtZero_eq_zero (p := p) (P := P) (X := X) (x := x) (y := y) hyx
      · simp [hi]
    have hPartial :
        ∀ n : ℕ,
          π ({x} : Set E) *
            Finset.sum (Finset.Icc 1 n)
              (fun k ↦ (P x : Measure Ω) {ω | X k ω = y ∧ (k : ℕ∞) < (τ_[X, x]^1) ω}) ≤
                π ({y} : Set E) := by
      intro n
      -- Proof comment: the textbook decomposition writes `π ({y})` as the partial sum plus a
      -- nonnegative weighted-start remainder term, so each finite partial sum is bounded by
      -- `π ({y})`.
      rw [weightedStartLaw_offDiag_firstReturnDecomposition
        (p := p) (P := P) (X := X) (π := π) hπ hyx n]
      exact le_add_of_nonneg_left (zero_le _)
    -- Proof comment: compare each finite excursion partial sum against `π ({y})`, then pass to
    -- the supremum representation of the return-cycle series.
    calc
      π ({x} : Set E) * (μ[P, X] x) ({y} : Set E)
          = π ({x} : Set E) *
              ∑' i : ℕ,
                if i = 0 then 0 else
                  (P x : Measure Ω) {ω | X i ω = y ∧ (i : ℕ∞) < (τ_[X, x]^1) ω} := by
                    rw [hSeries]
      _ = π ({x} : Set E) *
            ⨆ n : ℕ, Finset.sum (Finset.range n)
              (fun i ↦ if i = 0 then 0 else
                (P x : Measure Ω) {ω | X i ω = y ∧ (i : ℕ∞) < (τ_[X, x]^1) ω}) := by
              rw [ENNReal.tsum_eq_iSup_nat]
      _ = ⨆ n : ℕ, π ({x} : Set E) *
            Finset.sum (Finset.range n)
              (fun i ↦ if i = 0 then 0 else
                (P x : Measure Ω) {ω | X i ω = y ∧ (i : ℕ∞) < (τ_[X, x]^1) ω}) := by
              rw [ENNReal.mul_iSup]
      _ ≤ π ({y} : Set E) := by
            refine iSup_le fun n ↦ ?_
            cases n with
            | zero =>
                simp
            | succ m =>
                rw [sum_range_beforeReturn_eq_sum_Icc
                  (p := p) (P := P) (X := X) (x := x) (y := y) hyx m]
                exact hPartial m

/-- Helper for Exercise 17.6.6: a strict singleton gap above the return-cycle reference measure
propagates back to the reference state `x`, contradicting `(μ[P, X] x) ({x} : Set E) = 1`. -/
lemma strictGapAgainstReturnCyclePropagatesToReference [Countable E] {x y : E}
    {π : Measure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π)
    (hx : IsRecurrentState P X x)
    (hπ_finite : ∀ z : E, π ({z} : Set E) < ∞)
    (hπx_pos : 0 < π ({x} : Set E))
    (hLower :
      ∀ z : E, π ({z} : Set E) ≥ π ({x} : Set E) * (μ[P, X] x) ({z} : Set E))
    (hgap : π ({y} : Set E) > π ({x} : Set E) * (μ[P, X] x) ({y} : Set E))
    (hstep : ∃ n : ℕ, 0 < n ∧ 0 < (discreteMatrixKernel p ^ n) y ({x} : Set E)) :
    False := by
  rcases hstep with ⟨n, -, hyx_pos⟩
  let hReal : IsMarkovProcessRealization
      (fun m ↦ discreteMatrixKernel p ^ m) P X := inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel p ^ n) := hReal.semigroup.isMarkovKernel n
  have hπ_singleton :
      π ({x} : Set E) =
        ∑' z : E, π ({z} : Set E) * ((discreteMatrixKernel p ^ n) z ({x} : Set E)) :=
    invariantMeasureApplySingletonEqTsumPow (p := p) (P := P) (X := X) hπ n x
  have hμinv :
      Kernel.Invariant (discreteMatrixKernel p) ((μ[P, X] x) : Measure E) := by
    simpa using
      (recurrentState_returnCycleOccupationMeasure_comp_eq
        (κ := fun m ↦ discreteMatrixKernel p ^ m) (P := P) (X := X) hx)
  have hμ_singleton :
      (μ[P, X] x) ({x} : Set E) =
        ∑' z : E, (μ[P, X] x) ({z} : Set E) * ((discreteMatrixKernel p ^ n) z ({x} : Set E)) :=
    invariantMeasureApplySingletonEqTsumPow (p := p) (P := P) (X := X) (π := (μ[P, X] x)) hμinv n x
  let f : E → ℝ≥0∞ :=
    fun z ↦ π ({x} : Set E) *
      ((μ[P, X] x) ({z} : Set E) * ((discreteMatrixKernel p ^ n) z ({x} : Set E)))
  let g : E → ℝ≥0∞ :=
    fun z ↦ π ({z} : Set E) * ((discreteMatrixKernel p ^ n) z ({x} : Set E))
  have hf_tsum :
      ∑' z : E, f z = π ({x} : Set E) * (μ[P, X] x) ({x} : Set E) := by
    -- Proof comment: scale the singleton invariance formula for the return-cycle occupation
    -- measure by the positive reference mass `π ({x})`.
    calc
      ∑' z : E, f z
          = π ({x} : Set E) *
              ∑' z : E, (μ[P, X] x) ({z} : Set E) * ((discreteMatrixKernel p ^ n) z ({x} : Set E)) := by
              simp only [f, ENNReal.tsum_mul_left]
      _ = π ({x} : Set E) * (μ[P, X] x) ({x} : Set E) := by
            rw [← hμ_singleton]
  have hg_tsum :
      ∑' z : E, g z = π ({x} : Set E) := by
    -- Proof comment: the `n`-step singleton convolution of `π` at `x` is exactly `π ({x})`.
    exact hπ_singleton.symm
  have hf_tsum_ne_top : (∑' z : E, f z) ≠ ⊤ := by
    rw [hf_tsum,
      returnCycleOccupationMeasure_apply_singleton_self (p := p) (P := P) (X := X) x, mul_one]
    exact (hπ_finite x).ne
  have hfg : ∀ z : E, f z ≤ g z := by
    intro z
    calc
      f z = (π ({x} : Set E) * (μ[P, X] x) ({z} : Set E)) *
          ((discreteMatrixKernel p ^ n) z ({x} : Set E)) := by
            simp only [f, mul_assoc]
      _ ≤ π ({z} : Set E) * ((discreteMatrixKernel p ^ n) z ({x} : Set E)) := by
            exact mul_le_mul_right' (hLower z) ((discreteMatrixKernel p ^ n) z ({x} : Set E))
      _ = g z := by simp only [g]
  have hfgy : f y < g y := by
    have hyx_ne_top : ((discreteMatrixKernel p ^ n) y ({x} : Set E)) ≠ ⊤ :=
      measure_ne_top _ _
    calc
      f y = (π ({x} : Set E) * (μ[P, X] x) ({y} : Set E)) *
          ((discreteMatrixKernel p ^ n) y ({x} : Set E)) := by
            simp only [f, mul_assoc]
      _ < π ({y} : Set E) * ((discreteMatrixKernel p ^ n) y ({x} : Set E)) := by
            exact ENNReal.mul_lt_mul_right' hyx_pos.ne' hyx_ne_top hgap
      _ = g y := by simp only [g]
  have hsum_lt : (∑' z : E, f z) < ∑' z : E, g z :=
    ENNReal.tsum_lt_tsum hf_tsum_ne_top hfg hfgy
  have hself_lt :
      π ({x} : Set E) * (μ[P, X] x) ({x} : Set E) < π ({x} : Set E) := by
    calc
      π ({x} : Set E) * (μ[P, X] x) ({x} : Set E) = ∑' z : E, f z := hf_tsum.symm
      _ < ∑' z : E, g z := hsum_lt
      _ = π ({x} : Set E) := hg_tsum
  rw [returnCycleOccupationMeasure_apply_singleton_self (p := p) (P := P) (X := X) x, mul_one] at hself_lt
  exact lt_irrefl _ hself_lt

/-- Helper for Exercise 17.6.6: a nonzero invariant measure with finite singleton masses agrees
singletonwise with its mass at `x` times the return-cycle occupation measure rooted at the
recurrent state `x`. -/
lemma invariantMeasureSingletonEqReferenceMassMulReturnCycle [Countable E]
    (hirr : IsIrreducibleMarkovChain P X) {x : E}
    {π : Measure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π)
    (hx : IsRecurrentState P X x)
    (hπ_finite : ∀ z : E, π ({z} : Set E) < ∞)
    (hπx_pos : 0 < π ({x} : Set E)) :
    ∀ y : E, π ({y} : Set E) = π ({x} : Set E) * (μ[P, X] x) ({y} : Set E) := by
  -- Route correction: the boilerplate setup for countability, positive singleton masses, and
  -- iterated invariance is handled above, so the remaining work is to combine the textbook lower
  -- bound with the irreducibility-driven strict-gap contradiction.
  intro y
  have hLower :
      π ({y} : Set E) ≥ π ({x} : Set E) * (μ[P, X] x) ({y} : Set E) :=
    invariantMeasureSingletonGeReferenceMassMulReturnCycle
      (p := p) (P := P) (X := X) hπ hx hπ_finite hπx_pos y
  have hnot_gt :
      ¬ π ({y} : Set E) > π ({x} : Set E) * (μ[P, X] x) ({y} : Set E) := by
    intro hgap
    have hstep :
        ∃ n : ℕ, 0 < n ∧ 0 < (discreteMatrixKernel p ^ n) y ({x} : Set E) :=
      existsPosStepMass_of_everHitsProbability_pos
        (κ := fun n ↦ discreteMatrixKernel p ^ n) (P := P) (X := X) (x := y) (y := x) (hirr y x)
    exact strictGapAgainstReturnCyclePropagatesToReference
      (p := p) (P := P) (X := X) hπ hx hπ_finite hπx_pos
      (fun z ↦ invariantMeasureSingletonGeReferenceMassMulReturnCycle
        (p := p) (P := P) (X := X) hπ hx hπ_finite hπx_pos z)
      hgap hstep
  exact le_antisymm (le_of_not_gt hnot_gt) hLower

-- Proof sketch: for a fixed nonzero invariant measure `π`, use the exercise's induction on the
-- first return to a reference state `x` to identify every singleton mass `π {y}` with
-- `π {x} * μ_x {y}`, where `μ_x` is the return-cycle occupation measure from Theorem 17.47.
-- Applying this description to two invariant measures and comparing the same reference state
-- yields a strictly positive finite scalar relating them. The source argument works with ordinary
-- constant multiples, so the source-style finiteness of singleton masses is kept explicit.
/-- Exercise 17.6.6: if the realized discrete-time chain with transition matrix `p` is
irreducible in the Chapter 17 sense and recurrent, then any two nonzero invariant measures for
`discreteMatrixKernel p` with finite singleton masses are proportional by a positive finite
constant. Equivalently, the invariant measure is unique up to multiplication by a positive
ordinary constant. -/
theorem invariantMeasures_unique_up_to_scale_of_irreducible_recurrent
    (hirr : IsIrreducibleMarkovChain P X) (hrec : IsRecurrentMarkovChain P X) {μ ν : Measure E}
    (hμ : Kernel.Invariant (discreteMatrixKernel p) μ)
    (hν : Kernel.Invariant (discreteMatrixKernel p) ν)
    (hμ_finite : ∀ x : E, μ ({x} : Set E) < ∞)
    (hν_finite : ∀ x : E, ν ({x} : Set E) < ∞)
    (hμ_ne : μ ≠ 0) (hν_ne : ν ≠ 0) :
    ∃ c : NNReal, 0 < c ∧ ν = (c : ℝ≥0∞) • μ := by
  classical
  letI : Countable E := countableOfIsIrreducibleMarkovChain
    (p := p) (P := P) (X := X) hirr
  obtain ⟨x, hμx_pos⟩ := existsPositiveSingletonMassOfNeZero
    (p := p) (P := P) (X := X) (π := μ) hμ_ne
  have hx : IsRecurrentState P X x := hrec x
  -- Proof comment: first identify both invariant measures through the same return-cycle
  -- occupation measure rooted at the recurrent reference state `x`.
  have hμ_singleton :
      ∀ y : E, μ ({y} : Set E) = μ ({x} : Set E) * (μ[P, X] x) ({y} : Set E) :=
    invariantMeasureSingletonEqReferenceMassMulReturnCycle
      (p := p) (P := P) (X := X) hirr hμ hx hμ_finite hμx_pos
  obtain ⟨z, hνz_pos⟩ := existsPositiveSingletonMassOfNeZero
    (p := p) (P := P) (X := X) (π := ν) hν_ne
  let hReal : IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hzx_step :
      ∃ n : ℕ, 0 < n ∧ 0 < (discreteMatrixKernel p ^ n) z ({x} : Set E) := by
    exact existsPosStepMass_of_everHitsProbability_pos
      (κ := fun n ↦ discreteMatrixKernel p ^ n) (P := P) (X := X) (x := z) (y := x) (hirr z x)
  have hνx_pos : 0 < ν ({x} : Set E) := by
    -- Proof comment: irreducibility reaches the chosen reference state `x`, and invariance
    -- transports the positive singleton mass of `ν` along that positive-time step.
    exact singletonMass_pos_of_invariant_of_posStepMass
      hReal.semigroup (by simpa using hν) hνz_pos hzx_step
  have hν_singleton :
      ∀ y : E, ν ({y} : Set E) = ν ({x} : Set E) * (μ[P, X] x) ({y} : Set E) :=
    invariantMeasureSingletonEqReferenceMassMulReturnCycle
      (p := p) (P := P) (X := X) hirr hν hx hν_finite hνx_pos
  have hratio_finite : ν ({x} : Set E) / μ ({x} : Set E) < ∞ :=
    ENNReal.div_lt_top (hν_finite x).ne hμx_pos.ne'
  have hratio_pos : 0 < ν ({x} : Set E) / μ ({x} : Set E) := by
    exact (ENNReal.div_pos_iff).2 ⟨hνx_pos.ne', (hμ_finite x).ne⟩
  let c : NNReal := (ν ({x} : Set E) / μ ({x} : Set E)).toNNReal
  have hc_pos : 0 < c := by
    exact ENNReal.toNNReal_pos hratio_pos.ne' (ne_of_lt hratio_finite)
  have hc_coe :
      (c : ℝ≥0∞) = ν ({x} : Set E) / μ ({x} : Set E) := by
    simpa [c] using (ENNReal.coe_toNNReal (ne_of_lt hratio_finite))
  refine ⟨c, hc_pos, ?_⟩
  refine Measure.ext_of_singleton fun y ↦ ?_
  rw [Measure.smul_apply]
  calc
    ν ({y} : Set E) = ν ({x} : Set E) * (μ[P, X] x) ({y} : Set E) := hν_singleton y
    _ = ((ν ({x} : Set E) / μ ({x} : Set E)) * μ ({x} : Set E)) *
          (μ[P, X] x) ({y} : Set E) := by
            rw [ENNReal.div_mul_cancel hμx_pos.ne' (hμ_finite x).ne]
    _ = (ν ({x} : Set E) / μ ({x} : Set E)) *
          (μ ({x} : Set E) * (μ[P, X] x) ({y} : Set E)) := by
            rw [mul_assoc, mul_left_comm]
    _ = (ν ({x} : Set E) / μ ({x} : Set E)) * μ ({y} : Set E) := by
          rw [← hμ_singleton y]
    _ = (c : ℝ≥0∞) * μ ({y} : Set E) := by
          rw [hc_coe]

-- Proof sketch: apply Theorem 17.37 to pass from the kernel irreducibility of
-- `discreteMatrixKernel p` to the source-facing predicate `IsIrreducibleMarkovChain P X`, then
-- invoke Exercise 17.6.6.
/-- Kernel-style specialization of Exercise 17.6.6 for realizations of a stochastic matrix. -/
theorem
    invariantMeasures_unique_up_to_scale_of_irreducible_recurrent_of_discreteMatrixKernel_isIrreducible
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)]
    (hrec : IsRecurrentMarkovChain P X) {μ ν : Measure E}
    (hμ : Kernel.Invariant (discreteMatrixKernel p) μ)
    (hν : Kernel.Invariant (discreteMatrixKernel p) ν)
    (hμ_finite : ∀ x : E, μ ({x} : Set E) < ∞)
    (hν_finite : ∀ x : E, ν ({x} : Set E) < ∞)
    (hμ_ne : μ ≠ 0) (hν_ne : ν ≠ 0) :
    ∃ c : NNReal, 0 < c ∧ ν = (c : ℝ≥0∞) • μ := by
  let hirr : IsIrreducibleMarkovChain P X := by
    have hgreen :
        ∀ ⦃x y : E⦄, x ≠ y → 0 < (G[P, X; 1]) x y := by
      intro x y hxy
      have hy_pos : 0 < (Measure.count : Measure E) ({y} : Set E) := by
        simp
      -- Proof comment: kernel irreducibility gives a positive singleton mass at some positive
      -- time, and the positive-time Green function records that positive step.
      rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E)
          (discreteMatrixKernel p)).irreducible
          (A := ({y} : Set E)) (MeasurableSet.singleton y) hy_pos x with ⟨n, hn⟩
      have hn_pos : 0 < n := by
        by_contra hn_pos
        have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn_pos
        subst hn_zero
        have hzero : ((discreteMatrixKernel p ^ 0) x) ({y} : Set E) = 0 := by
          change (Kernel.id x) ({y} : Set E) = 0
          simp [Kernel.id_apply, hxy]
        rw [hzero] at hn
        exact lt_irrefl _ hn
      exact greenFunctionFrom_one_pos_of_posStepMass
        (κ := fun m ↦ discreteMatrixKernel p ^ m) P X hn_pos hn
    exact
      (isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
        (κ := fun n ↦ discreteMatrixKernel p ^ n) P X).2 hgreen
  -- Proof comment: now apply the source-facing theorem to the irreducible recurrent realization.
  exact invariantMeasures_unique_up_to_scale_of_irreducible_recurrent
    (p := p) (P := P) (X := X) hirr
    hrec hμ hν hμ_finite hν_finite hμ_ne hν_ne

end

end ProbabilityTheory
