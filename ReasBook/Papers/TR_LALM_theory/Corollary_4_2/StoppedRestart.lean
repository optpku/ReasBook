/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Probability.Process.HittingTime
public import TR_LALM_theory.Corollary_4_2.StoppedScheduledAttempt
public import TR_LALM_theory.Theorem_3_6.UniformOutput

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LALM.Correction

universe u v

open StochasticRun.Localization

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}
variable {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}
variable {Q B b : ℕ+}

/-- Corollary 4.2: the finite observable type supplied by one stopped
scheduled attempt. Only rows used by the horizon and states/paths through the
terminal index are exposed. -/
abbrev stoppedAttemptFiniteObservableType
    (Ξ : Type u) (n m K : ℕ) :=
  (Fin K → ℕ → Ξ) ×
    (Fin (K + 1) → EuclideanSpace ℝ (Fin n)) ×
      (Fin (K + 1) → EuclideanSpace ℝ (Fin m)) ×
        (Fin K → EuclideanSpace ℝ (Fin n))

/-- Corollary 4.2: the observable supplied by one stopped scheduled attempt.
The outer indices are finite; each sample row is a latent `ℕ`-indexed supply,
of which only the finite horizon can affect the stopped transition. -/
noncomputable def stoppedAttemptFiniteObservable
    (attempt : StoppedAttempt h oracle ℙ x₀ multiplier₀ params Q B b
      confidence K X) (ω : Ω) :
    stoppedAttemptFiniteObservableType Ξ n m K :=
  (fun k i ↦ attempt.sample k.1 i ω,
    fun k ↦ StoppedAttempt.point attempt k.1 ω,
    fun k ↦ StoppedAttempt.multiplier attempt k.1 ω,
    fun k ↦ StoppedAttempt.baseStep attempt k.1 ω)

/-- Helper for Corollary 4.2: a supported finite-record coordinate agrees with
the stopped primal path at the corresponding natural index. -/
theorem stoppedAttemptFiniteObservable_point
    (attempt : StoppedAttempt h oracle ℙ x₀ multiplier₀ params Q B b
      confidence K X)
    (k : ℕ) (hk : k < K + 1) (ω : Ω) :
    (stoppedAttemptFiniteObservable attempt ω).2.1
        (Fin.ofNat (K + 1) k) =
      StoppedAttempt.point attempt k ω := by
  unfold stoppedAttemptFiniteObservable
  simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.mod_eq_of_lt hk]

/-- Helper for Corollary 4.2: a supported finite-record coordinate agrees with
the stopped multiplier path at the corresponding natural index. -/
theorem stoppedAttemptFiniteObservable_multiplier
    (attempt : StoppedAttempt h oracle ℙ x₀ multiplier₀ params Q B b
      confidence K X)
    (k : ℕ) (hk : k < K + 1) (ω : Ω) :
    (stoppedAttemptFiniteObservable attempt ω).2.2.1
        (Fin.ofNat (K + 1) k) =
      StoppedAttempt.multiplier attempt k ω := by
  unfold stoppedAttemptFiniteObservable
  simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.mod_eq_of_lt hk]

/-- Corollary 4.2: the record-level success set checks the finite positive
point prefix and ignores the latent sample tail and auxiliary coordinates. -/
def successRecord
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    Set (stoppedAttemptFiniteObservableType Ξ n m K) :=
  {z | ∀ k : Fin K, z.2.1 k.succ ∈ X}

omit [MeasurableSpace Ξ] in
/-- Helper for Corollary 4.2: membership in a finite success record means that
every positive primal coordinate through the horizon lies in `X`. -/
theorem mem_successRecord_iff
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (z : stoppedAttemptFiniteObservableType Ξ n m K) :
    z ∈ successRecord (Ξ := Ξ) (n := n) (m := m) K X ↔
      ∀ k : Fin K, z.2.1 k.succ ∈ X := by
  rfl

/-- Helper for Corollary 4.2: pulling the finite success record back through
one stopped-attempt observable gives its terminal success event. -/
theorem stoppedAttemptFiniteObservable_mem_successRecord_iff
    (attempt : StoppedAttempt h oracle ℙ x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    stoppedAttemptFiniteObservable attempt omega ∈
        successRecord (Ξ := Ξ) (n := n) (m := m) K X ↔
      omega ∈ StoppedAttempt.successEvent attempt := by
  change (∀ k : Fin K,
      StoppedAttempt.point attempt k.succ.val omega ∈ X) ↔
    omega ∈ StoppedAttempt.successEvent attempt
  constructor
  · intro hrecord
    apply (StoppedAttempt.mem_successEvent_iff_points_mem attempt omega).mpr
    intro j hjOne hjK
    let k : Fin K := ⟨j - 1, by omega⟩
    have hk : k.succ.val = j := by
      dsimp [k]
      omega
    rw [← hk]
    exact hrecord k
  · intro hsuccess k
    have hkOne : 1 ≤ k.succ.val := Nat.succ_pos k.val
    have hkK : k.succ.val ≤ K := by omega
    exact (StoppedAttempt.mem_successEvent_iff_points_mem attempt omega).mp
      hsuccess k.succ.val hkOne hkK

/-- Corollary 4.2: the record-level finite success set is measurable whenever
the localization set is measurable. -/
theorem measurableSet_successRecord
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) :
    MeasurableSet (successRecord (Ξ := Ξ) (n := n) (m := m) K X) := by
  change MeasurableSet {z : stoppedAttemptFiniteObservableType Ξ n m K |
    ∀ k : Fin K, z.2.1 k.succ ∈ X}
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun k ↦
    hX.preimage ((measurable_pi_apply k.succ).comp measurable_snd.fst)

/-- Corollary 4.2: the finite stopped-attempt observable is measurable in the
underlying probability space. -/
theorem measurable_stoppedAttemptFiniteObservable
    (attempt : StoppedAttempt h oracle ℙ x₀ multiplier₀ params Q B b
      confidence K X) :
    Measurable (stoppedAttemptFiniteObservable attempt) := by
  have hsample : Measurable
      (fun (ω : Ω) (k : Fin K) (i : ℕ) ↦ attempt.sample k.1 i ω) := by
    apply measurable_pi_lambda
    intro k
    apply measurable_pi_lambda
    intro i
    exact attempt.measurable_sample k.1 i
  have hpoint : Measurable
      (fun (ω : Ω) (k : Fin (K + 1)) ↦
        StoppedAttempt.point attempt k.1 ω) := by
    apply measurable_pi_lambda
    intro k
    exact StoppedAttempt.measurable_point attempt k.1
  have hmultiplier : Measurable
      (fun (ω : Ω) (k : Fin (K + 1)) ↦
        StoppedAttempt.multiplier attempt k.1 ω) := by
    apply measurable_pi_lambda
    intro k
    exact StoppedAttempt.measurable_multiplier attempt k.1
  have hbaseStep : Measurable
      (fun (ω : Ω) (k : Fin K) ↦ StoppedAttempt.baseStep attempt k.1 ω) := by
    apply measurable_pi_lambda
    intro k
    exact StoppedAttempt.measurable_baseStep attempt k.1
  change Measurable (fun ω ↦
    ((fun (k : Fin K) (i : ℕ) ↦ attempt.sample k.1 i ω),
      (fun (k : Fin (K + 1)) ↦ StoppedAttempt.point attempt k.1 ω),
      (fun (k : Fin (K + 1)) ↦ StoppedAttempt.multiplier attempt k.1 ω),
      (fun (k : Fin K) ↦ StoppedAttempt.baseStep attempt k.1 ω)))
  exact hsample.prodMk (hpoint.prodMk (hmultiplier.prodMk hbaseStep))

variable {hK : 2 ≤ K}

/-- Corollary 4.2: a safeguarded restart whose attempts are finite absorbing
stopped scheduled processes. -/
structure StoppedSafeguardedRestart where
  /-- The finite stopped scheduled attempt used at each restart index. -/
  attempt : ℕ → StoppedAttempt h oracle ℙ x₀ multiplier₀ params
    (SPIDER.refreshPeriod K) (SPIDER.refreshBatchSize K)
    (SPIDER.Correction.innerBatchSize h oracle params K)
    confidence K X
  /-- The independent uniform output selector for each stopped attempt. -/
  outputIndex : ℕ → Ω → ℕ
  /-- Every selector has the prescribed uniform index law. -/
  outputIndex_hasLaw : ∀ i,
    ProbabilityTheory.HasLaw (outputIndex i)
      (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure ℙ
  /-- The selector is independent of the complete stopped-attempt observable. -/
  outputIndex_indep_attempt : ∀ i,
    ProbabilityTheory.IndepFun (outputIndex i)
      (fun ω ↦ stoppedAttemptFiniteObservable (attempt i) ω) ℙ
  /-- Complete stopped attempts, including selectors, are mutually independent. -/
  independent_attempt : ProbabilityTheory.iIndepFun
    (fun i ω ↦ (outputIndex i ω, stoppedAttemptFiniteObservable (attempt i) ω)) ℙ

namespace StoppedSafeguardedRestart

/-- Corollary 4.2: construct a stopped restart from explicit attempts and
uniform selectors. -/
def ofAttempts
    (attempt : ℕ → StoppedAttempt h oracle ℙ x₀ multiplier₀ params
      (SPIDER.refreshPeriod K) (SPIDER.refreshBatchSize K)
      (SPIDER.Correction.innerBatchSize h oracle params K)
      confidence K X)
    (outputIndex : ℕ → Ω → ℕ)
    (outputIndex_hasLaw : ∀ i,
      ProbabilityTheory.HasLaw (outputIndex i)
        (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure ℙ)
    (outputIndex_indep_attempt : ∀ i,
      ProbabilityTheory.IndepFun (outputIndex i)
        (fun ω ↦ stoppedAttemptFiniteObservable (attempt i) ω) ℙ)
    (independent_attempt : ProbabilityTheory.iIndepFun
      (fun i ω ↦ (outputIndex i ω,
        stoppedAttemptFiniteObservable (attempt i) ω)) ℙ) :
    StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X) :=
  { attempt
    outputIndex
    outputIndex_hasLaw
    outputIndex_indep_attempt
    independent_attempt }

/-- Corollary 4.2: every stopped attempt carries the measurable localization
set used by the restart. -/
theorem attempt_localization_measurableSet
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : MeasurableSet X :=
  (restart.attempt i).measurableSet_localization

/-- Corollary 4.2: every stopped attempt starts from the prescribed primal
initialization inside the localization set. -/
theorem attempt_initial_mem
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : x₀ ∈ X :=
  (restart.attempt i).initial_mem

/-- Corollary 4.2: every stopped attempt carries the regularity buffer needed
for its active transitions. -/
theorem attempt_region_condition
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : RegionCondition h oracle params confidence X :=
  (restart.attempt i).region_condition

/-- Corollary 4.2: success means that every transition before the horizon is
still active; the state after an exit is never charged as an oracle call. -/
def successEvent
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : Set Ω :=
  StoppedAttempt.successEvent (restart.attempt i)

/-- Corollary 4.2: the restart-level success event is the stopped attempt's
terminal active event, preserving the first-exit convention at index `K`. -/
theorem successEvent_eq_attempt_success
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    successEvent (restart := restart) (confidence := confidence) (K := K)
        (X := X) i = StoppedAttempt.successEvent (restart.attempt i) := by
  rfl

/-- Corollary 4.2: every stopped restart success event is measurable. -/
theorem measurableSet_successEvent
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : MeasurableSet (successEvent restart i) := by
  rw [successEvent_eq_attempt_success restart i]
  exact StoppedAttempt.measurableSet_successEvent (restart.attempt i)

/-- Corollary 4.2: every stopped restart selector is almost surely supported
on the finite output range `1, ..., K - 1`. -/
theorem ae_outputIndex_mem_uniformRange
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    ∀ᵐ omega ∂ℙ, restart.outputIndex i omega ∈ Finset.Icc 1 (K - 1) := by
  let p := LALM.StochasticRun.UniformOutput.indexLaw K hK
  let s := Finset.Icc 1 (K - 1)
  have hpSupport : ∀ᵐ k ∂p.toMeasure, k ∈ s := by
    rw [ae_iff_of_countable]
    intro k hkMeasure
    by_contra hk
    have hk' : k ∉ Finset.Icc 1 (K - 1) := by
      simpa only [s] using hk
    have hpZero : p k = 0 := by
      simp only [p, LALM.StochasticRun.UniformOutput.indexLaw,
        PMF.uniformOfFinset_apply, if_neg hk']
    have hsingleton : p.toMeasure {k} = p k :=
      PMF.toMeasure_apply_singleton p k (MeasurableSet.singleton k)
    exact hkMeasure (hsingleton.trans hpZero)
  have hpSupport' :
      ∀ᵐ k ∂(LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure,
        k ∈ Finset.Icc 1 (K - 1) := by
    simpa only [p, s] using hpSupport
  exact ((restart.outputIndex_hasLaw i).ae_iff (measurable_of_countable _)).mpr
    hpSupport'

/-- Corollary 4.2: lift the record-level success set to the selector-record
product used by the restart independence hypothesis. -/
def successRecordWithSelector
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    Set (ℕ × stoppedAttemptFiniteObservableType Ξ n m K) :=
  Prod.snd ⁻¹' successRecord (Ξ := Ξ) (n := n) (m := m) K X

/-- Corollary 4.2: the lifted finite success set is measurable. -/
theorem measurableSet_successRecordWithSelector
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) :
    MeasurableSet
      (successRecordWithSelector (Ξ := Ξ) (n := n) (m := m) K X) :=
  (measurableSet_successRecord (Ξ := Ξ) (n := n) (m := m) K X hX).preimage
    measurable_snd

/-- Corollary 4.2: pulling the finite record success set back to one attempt
gives the stopped terminal success event. -/
theorem successRecord_preimage
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun ω ↦ stoppedAttemptFiniteObservable (restart.attempt i) ω) ⁻¹'
        successRecord (Ξ := Ξ) (n := n) (m := m) K X =
      successEvent restart i := by
  ext ω
  change (∀ k : Fin K,
      StoppedAttempt.point (restart.attempt i) k.succ.val ω ∈ X) ↔
    ω ∈ successEvent restart i
  rw [successEvent_eq_attempt_success restart i]
  constructor
  · intro hrecord
    apply (StoppedAttempt.mem_successEvent_iff_points_mem
      (restart.attempt i) ω).mpr
    intro j hjOne hjK
    let k : Fin K := ⟨j - 1, by omega⟩
    have hk : k.succ.val = j := by
      dsimp [k]
      omega
    rw [← hk]
    exact hrecord k
  · intro hsuccess k
    have hkOne : 1 ≤ k.succ.val := by
      exact Nat.succ_pos k.val
    have hkHorizon : k.succ.val ≤ K := by
      exact Nat.succ_le_iff.mpr k.isLt
    exact (StoppedAttempt.mem_successEvent_iff_points_mem
      (restart.attempt i) ω).mp hsuccess k.succ.val hkOne hkHorizon

/-- Corollary 4.2: pulling the lifted record success set back through the
selector-plus-observable map gives the same terminal event. -/
theorem successRecordWithSelector_preimage
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun ω ↦
      (restart.outputIndex i ω,
        stoppedAttemptFiniteObservable (restart.attempt i) ω)) ⁻¹'
        successRecordWithSelector (Ξ := Ξ) (n := n) (m := m) K X =
      successEvent restart i := by
  simpa only [successRecordWithSelector, Function.comp_def, Set.preimage_preimage]
    using successRecord_preimage (restart := restart) i

/-- Corollary 4.2: the lifted record failure set is the measurable complement
of the finite success set. -/
def failureRecordWithSelector
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    Set (ℕ × stoppedAttemptFiniteObservableType Ξ n m K) :=
  (successRecordWithSelector (Ξ := Ξ) (n := n) (m := m) K X)ᶜ

/-- Corollary 4.2: the lifted record failure set is measurable. -/
theorem measurableSet_failureRecordWithSelector
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) :
    MeasurableSet
      (failureRecordWithSelector (Ξ := Ξ) (n := n) (m := m) K X) :=
  (measurableSet_successRecordWithSelector (Ξ := Ξ) (n := n) (m := m) K X hX).compl

/-- Corollary 4.2: pulling the lifted record failure set back to an attempt
gives the complement of its stopped success event. -/
theorem failureRecordWithSelector_preimage
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun ω ↦
      (restart.outputIndex i ω,
        stoppedAttemptFiniteObservable (restart.attempt i) ω)) ⁻¹'
        failureRecordWithSelector (Ξ := Ξ) (n := n) (m := m) K X =
      (successEvent restart i)ᶜ := by
  rw [failureRecordWithSelector]
  rw [Set.preimage_compl]
  rw [successRecordWithSelector_preimage restart i]

/-- Corollary 4.2: the number of oracle-bearing transitions in one stopped
attempt is the cardinality of its active in-horizon indices. -/
noncomputable def attemptIterations
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) : ℕ :=
  StoppedAttempt.executedIterations (restart.attempt i) ω

/-- Corollary 4.2: stopped attempt work never exceeds its finite horizon. -/
theorem attemptIterations_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) : attemptIterations restart i ω ≤ K := by
  exact StoppedAttempt.executedIterations_le (restart.attempt i) ω

/-- Corollary 4.2: a successful stopped attempt executes all `K` scheduled
transitions, including the transition that would discover a first exit. -/
theorem attemptIterations_eq_K_of_success
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω)
    (hω : ω ∈ successEvent (restart := restart) (confidence := confidence)
      (K := K) (X := X) i) : attemptIterations restart i ω = K := by
  apply StoppedAttempt.executedIterations_eq_of_mem_successEvent
  rw [← successEvent_eq_attempt_success restart i]
  exact hω

/-- Corollary 4.2: the Boolean completion indicator of one stopped attempt. -/
noncomputable def completionIndicator
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) : Bool :=
  @decide (ω ∈ successEvent (restart := restart) (confidence := confidence)
    (K := K) (X := X) (i := i)) (Classical.propDecidable _)

/-- Corollary 4.2: completion is equivalent to membership in the active-prefix
event. -/
theorem completionIndicator_eq_true
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) :
    completionIndicator restart i ω = true ↔
      ω ∈ successEvent (restart := restart) (confidence := confidence)
        (K := K) (X := X) (i := i) := by
  simp only [completionIndicator, decide_eq_true_eq]

/-- Corollary 4.2: the Boolean completion fiber of each stopped attempt is
measurable. -/
theorem measurableSet_completionIndicator_eq_true
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    MeasurableSet {ω | completionIndicator restart i ω = true} := by
  rw [show {ω | completionIndicator restart i ω = true} = successEvent restart i by
    ext ω
    exact (completionIndicator_eq_true restart i ω)]
  exact measurableSet_successEvent restart i

/-- Corollary 4.2: the first successful stopped attempt, or `⊤` when none
is successful. -/
noncomputable def firstAccepted
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) : Ω → ℕ∞ :=
  MeasureTheory.hittingAfter (fun i ω ↦ completionIndicator restart i ω)
    {true} 0

/-- Corollary 4.2: no stopped attempt succeeds exactly when the first accepted
index is infinite. -/
theorem firstAccepted_eq_top_iff
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) :
    firstAccepted restart ω = ⊤ ↔
      ∀ i, completionIndicator restart i ω ≠ true := by
  change (MeasureTheory.hittingAfter
      (fun i ω ↦ completionIndicator restart i ω) {true} 0 ω =
      (⊤ : WithTop ℕ) ↔ ∀ i, completionIndicator restart i ω ≠ true)
  rw [MeasureTheory.hittingAfter_eq_top_iff]
  simp only [Nat.zero_le, true_imp_iff, Set.mem_singleton_iff]

/-- Corollary 4.2: a finite first accepted index is a successful stopped
attempt. -/
theorem firstAccepted_completion
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) (htermination : firstAccepted restart ω ≠ ⊤) :
    completionIndicator restart
      ((firstAccepted restart ω).untop htermination) ω = true := by
  have hmem : completionIndicator restart
      (firstAccepted restart ω).untopA ω ∈ ({true} : Set Bool) := by
    simpa only [firstAccepted] using
      (MeasureTheory.hittingAfter_mem_set_of_ne_top
        (u := fun i ω ↦ completionIndicator restart i ω)
        (s := ({true} : Set Bool)) (n := 0) (ω := ω) htermination)
  have hindex : (firstAccepted restart ω).untopA =
      (firstAccepted restart ω).untop htermination := by
    exact WithTop.untopA_eq_untop htermination
  rw [hindex] at hmem
  simpa only [Set.mem_singleton_iff] using hmem

/-- Corollary 4.2: finite first acceptance is characterized by success at that
index and failure at every prior index. -/
theorem firstAccepted_eq_coe_iff
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) :
    firstAccepted restart ω = (i : ℕ∞) ↔
      completionIndicator restart i ω = true ∧
        ∀ j < i, completionIndicator restart j ω ≠ true := by
  constructor
  · intro hfirst
    have htermination : firstAccepted restart ω ≠ ⊤ := by
      rw [hfirst]
      exact ENat.coe_ne_top i
    constructor
    · have hsuccess := firstAccepted_completion restart ω htermination
      have hindex : (firstAccepted restart ω).untop htermination = i := by
        apply WithTop.coe_injective
        calc
          ((firstAccepted restart ω).untop htermination : ℕ∞) =
              firstAccepted restart ω := WithTop.coe_untop _ _
          _ = (i : ℕ∞) := hfirst
      rwa [hindex] at hsuccess
    · intro j hji
      have hfirstHitting :
          MeasureTheory.hittingAfter
              (fun i ω ↦ completionIndicator restart i ω) {true} 0 ω =
            (i : WithTop ℕ) := hfirst
      have hjlt : (j : WithTop ℕ) < MeasureTheory.hittingAfter
          (fun i ω ↦ completionIndicator restart i ω) ({true} : Set Bool)
            0 ω := by
        rw [hfirstHitting]
        exact WithTop.coe_lt_coe.mpr hji
      have hnotMem := MeasureTheory.notMem_of_lt_hittingAfter
        (u := fun i ω ↦ completionIndicator restart i ω)
        (s := ({true} : Set Bool)) (n := 0) (k := j) (ω := ω) hjlt
        (Nat.zero_le j)
      simpa only [Set.mem_singleton_iff] using hnotMem
  · rintro ⟨hiSuccess, hprior⟩
    have hiMem : completionIndicator restart i ω ∈ ({true} : Set Bool) := by
      simpa only [Set.mem_singleton_iff] using hiSuccess
    have hle := MeasureTheory.hittingAfter_le_of_mem
      (u := fun i ω ↦ completionIndicator restart i ω)
      (s := ({true} : Set Bool)) (n := 0) (ω := ω) (Nat.zero_le i) hiMem
    have hge : (i : ℕ∞) ≤ firstAccepted restart ω := by
      apply le_of_not_gt
      intro hlt
      have htermination : firstAccepted restart ω ≠ ⊤ :=
        ne_top_of_lt (hlt.trans (WithTop.coe_lt_top i))
      have hjlt : (firstAccepted restart ω).untop htermination < i := by
        exact (WithTop.untop_lt_iff htermination).mpr hlt
      apply hprior ((firstAccepted restart ω).untop htermination) hjlt
      exact firstAccepted_completion restart ω htermination
    exact le_antisymm hle hge

/-- Corollary 4.2: the one-based number of stopped attempts, infinite on
nontermination. -/
noncomputable def attemptCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ := firstAccepted restart ω + 1

/-- Corollary 4.2: attempt count is one plus first acceptance. -/
theorem attemptCount_eq
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : attemptCount restart ω = firstAccepted restart ω + 1 := by
  rfl

/-- Corollary 4.2: attempt count is infinite exactly on nontermination. -/
theorem attemptCount_eq_top_iff
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : attemptCount restart ω = ⊤ ↔ firstAccepted restart ω = ⊤ := by
  simp only [attemptCount, ENat.add_eq_top, ENat.one_ne_top, or_false]

/-- Corollary 4.2: the returned primal point from the first accepted stopped
attempt, with a harmless default on the null nontermination branch. -/
noncomputable def returnedPoint
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  let i := (firstAccepted restart ω).untopD 0
  StoppedAttempt.point (restart.attempt i)
    (restart.outputIndex i ω + 1) ω

/-- Corollary 4.2: the returned multiplier from the first accepted stopped
attempt, with the same default-index convention. -/
noncomputable def returnedMultiplier
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : EuclideanSpace ℝ (Fin m) :=
  let i := (firstAccepted restart ω).untopD 0
  StoppedAttempt.multiplier (restart.attempt i)
    (restart.outputIndex i ω + 1) ω

/-- Corollary 4.2: expose the returned point's selected stopped trajectory. -/
theorem returnedPoint_apply
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : returnedPoint restart ω =
      StoppedAttempt.point
        (restart.attempt ((firstAccepted restart ω).untopD 0))
        (restart.outputIndex ((firstAccepted restart ω).untopD 0) ω + 1) ω := by
  rfl

/-- Corollary 4.2: expose the returned multiplier's selected stopped trajectory. -/
theorem returnedMultiplier_apply
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : returnedMultiplier restart ω =
      StoppedAttempt.multiplier
        (restart.attempt ((firstAccepted restart ω).untopD 0))
        (restart.outputIndex ((firstAccepted restart ω).untopD 0) ω + 1) ω := by
  rfl

end StoppedSafeguardedRestart

end LALM.Correction

end
