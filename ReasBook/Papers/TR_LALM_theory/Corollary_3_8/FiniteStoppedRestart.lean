/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Probability.Process.HittingTime
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedOutput
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedOutput

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LALM.FiniteStopped

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀}
variable {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Corollary 3.8: the finite observable carried by one base stopped attempt. -/
abbrev stoppedAttemptFiniteObservableType
    (Ξ : Type u) (n m K : ℕ) :=
  (Fin K → ℕ → Ξ) ×
    (Fin (K + 1) → EuclideanSpace ℝ (Fin n)) ×
      (Fin (K + 1) → EuclideanSpace ℝ (Fin m)) ×
        (Fin K → EuclideanSpace ℝ (Fin n))

/-- Corollary 3.8: collect exactly the finite path and in-horizon sample rows
of one base stopped attempt. -/
noncomputable def stoppedAttemptFiniteObservable
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    stoppedAttemptFiniteObservableType Ξ n m K :=
  (fun k i ↦ attempt.sample k.1 i omega,
    fun k ↦ attempt.point k omega,
    fun k ↦ attempt.multiplier k omega,
    fun k ↦ attempt.baseStep k omega)

/-- Helper for Corollary 3.8: a finite record point coordinate is the
corresponding stopped point. -/
theorem stoppedAttemptFiniteObservable_point
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : Fin (K + 1)) (omega : Ω) :
    (stoppedAttemptFiniteObservable attempt omega).2.1 k =
      attempt.point k omega := by
  rfl

/-- Helper for Corollary 3.8: a finite record multiplier coordinate is the
corresponding stopped multiplier. -/
theorem stoppedAttemptFiniteObservable_multiplier
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : Fin (K + 1)) (omega : Ω) :
    (stoppedAttemptFiniteObservable attempt omega).2.2.1 k =
      attempt.multiplier k omega := by
  rfl

/-- Corollary 3.8: record-level success means that every positive endpoint
through the finite horizon lies in the localization set. -/
def successRecord
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    Set (stoppedAttemptFiniteObservableType Ξ n m K) :=
  {record | ∀ k : Fin K, record.2.1 k.succ ∈ X}

/-- Helper for Corollary 3.8: record-level success agrees with the terminal
active event of the stopped attempt. -/
theorem stoppedAttemptFiniteObservable_mem_successRecord_iff
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    stoppedAttemptFiniteObservable attempt omega ∈
        successRecord (Ξ := Ξ) (n := n) (m := m) K X ↔
      omega ∈ attempt.successEvent := by
  change (∀ k : Fin K, attempt.point k.succ omega ∈ X) ↔
    omega ∈ attempt.successEvent
  exact (attempt.mem_successEvent_iff_points_mem omega).symm

/-- Corollary 3.8: the finite record success set is measurable. -/
theorem measurableSet_successRecord
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) :
    MeasurableSet (successRecord (Ξ := Ξ) (n := n) (m := m) K X) := by
  change MeasurableSet
    {record : stoppedAttemptFiniteObservableType Ξ n m K |
      ∀ k : Fin K, record.2.1 k.succ ∈ X}
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun k ↦
    hX.preimage ((measurable_pi_apply k.succ).comp measurable_snd.fst)

/-- Corollary 3.8: the complete finite observable of a stopped attempt is
measurable. -/
theorem measurable_stoppedAttemptFiniteObservable
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) :
    Measurable (stoppedAttemptFiniteObservable attempt) := by
  have hsample : Measurable
      (fun (omega : Ω) (k : Fin K) (i : ℕ) ↦ attempt.sample k.1 i omega) := by
    apply measurable_pi_lambda
    intro k
    apply measurable_pi_lambda
    intro i
    exact attempt.measurable_sample k.1 i
  have hpoint : Measurable
      (fun (omega : Ω) (k : Fin (K + 1)) ↦ attempt.point k omega) := by
    apply measurable_pi_lambda
    intro k
    exact StoppedAttemptAnalysis.measurable_point attempt k
  have hmultiplier : Measurable
      (fun (omega : Ω) (k : Fin (K + 1)) ↦ attempt.multiplier k omega) := by
    apply measurable_pi_lambda
    intro k
    simpa only [LALM.FiniteStopped.StoppedAttempt.multiplier,
      Function.comp_def] using
      (measurable_fst.comp
        (measurable_snd.comp
          (measurable_snd.comp
            (measurable_snd.comp (attempt.measurable_state k)))))
  have hbaseStep : Measurable
      (fun (omega : Ω) (k : Fin K) ↦ attempt.baseStep k omega) := by
    apply measurable_pi_lambda
    intro k
    exact StoppedAttemptAnalysis.measurable_baseStep attempt k
  exact hsample.prodMk (hpoint.prodMk (hmultiplier.prodMk hbaseStep))

variable {hK : 2 ≤ K}

/-- Corollary 3.8: a countable safeguarded restart built from finite absorbing
base attempts and independent uniform output selectors. -/
structure StoppedSafeguardedRestart where
  /-- The finite stopped scheduled attempt at each restart index. -/
  attempt : ℕ → SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
    params confidence K X
  /-- The independent uniform output selector attached to each attempt. -/
  outputIndex : ℕ → Ω → ℕ
  /-- Every output selector has the uniform law on `1, ..., K - 1`. -/
  outputIndex_hasLaw : ∀ i,
    ProbabilityTheory.HasLaw (outputIndex i)
      (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure P
  /-- Each selector is independent of its finite stopped attempt. -/
  outputIndex_indep_attempt : ∀ i,
    ProbabilityTheory.IndepFun (outputIndex i)
      (fun omega ↦ stoppedAttemptFiniteObservable (attempt i) omega) P
  /-- The selector-attempt records are mutually independent across restarts. -/
  independent_attempt : ProbabilityTheory.iIndepFun
    (fun i omega ↦
      (outputIndex i omega, stoppedAttemptFiniteObservable (attempt i) omega)) P

namespace StoppedSafeguardedRestart

/-- Corollary 3.8: construct a finite stopped restart from explicit independent
attempts and selectors. -/
def ofAttempts
    (attempt : ℕ → SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (outputIndex : ℕ → Ω → ℕ)
    (outputIndex_hasLaw : ∀ i,
      ProbabilityTheory.HasLaw (outputIndex i)
        (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure P)
    (outputIndex_indep_attempt : ∀ i,
      ProbabilityTheory.IndepFun (outputIndex i)
        (fun omega ↦ stoppedAttemptFiniteObservable (attempt i) omega) P)
    (independent_attempt : ProbabilityTheory.iIndepFun
      (fun i omega ↦
        (outputIndex i omega, stoppedAttemptFiniteObservable (attempt i) omega)) P) :
    StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X) :=
  { attempt
    outputIndex
    outputIndex_hasLaw
    outputIndex_indep_attempt
    independent_attempt }

/-- Corollary 3.8: success of a restart attempt is its finite terminal active
event. -/
def successEvent
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : Set Ω :=
  (restart.attempt i).successEvent

/-- Helper for Corollary 3.8: the restart success event is definitionally the
attempt success event. -/
theorem successEvent_eq_attempt_success
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    successEvent restart i = (restart.attempt i).successEvent := by
  rfl

/-- Corollary 3.8: every finite restart success event is measurable. -/
theorem measurableSet_successEvent
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : MeasurableSet (successEvent restart i) :=
  (restart.attempt i).measurableSet_successEvent

/-- Corollary 3.8: every selector is almost surely supported on the prescribed
uniform output range. -/
theorem ae_outputIndex_mem_uniformRange
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    ∀ᵐ omega ∂P, restart.outputIndex i omega ∈ Finset.Icc 1 (K - 1) := by
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
  exact ((restart.outputIndex_hasLaw i).ae_iff (measurable_of_countable _)).mpr
    (by simpa only [p, s] using hpSupport)

/-- Corollary 3.8: lift finite record success to the selector-record product
used by the mutual-independence hypothesis. -/
def successRecordWithSelector
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    Set (ℕ × stoppedAttemptFiniteObservableType Ξ n m K) :=
  Prod.snd ⁻¹' successRecord (Ξ := Ξ) (n := n) (m := m) K X

/-- Corollary 3.8: the lifted finite success record is measurable. -/
theorem measurableSet_successRecordWithSelector
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) :
    MeasurableSet
      (successRecordWithSelector (Ξ := Ξ) (n := n) (m := m) K X) :=
  (measurableSet_successRecord (Ξ := Ξ) (n := n) (m := m) K X hX).preimage
    measurable_snd

/-- Corollary 3.8: pulling the lifted success record back through one restart
coordinate gives its finite success event. -/
theorem successRecordWithSelector_preimage
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun omega ↦
      (restart.outputIndex i omega,
        stoppedAttemptFiniteObservable (restart.attempt i) omega)) ⁻¹'
        successRecordWithSelector (Ξ := Ξ) (n := n) (m := m) K X =
      successEvent restart i := by
  ext omega
  exact stoppedAttemptFiniteObservable_mem_successRecord_iff
    (restart.attempt i) omega

/-- Corollary 3.8: the lifted failure record is the complement of finite
record success. -/
def failureRecordWithSelector
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    Set (ℕ × stoppedAttemptFiniteObservableType Ξ n m K) :=
  (successRecordWithSelector (Ξ := Ξ) (n := n) (m := m) K X)ᶜ

/-- Corollary 3.8: the lifted failure record is measurable. -/
theorem measurableSet_failureRecordWithSelector
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) :
    MeasurableSet
      (failureRecordWithSelector (Ξ := Ξ) (n := n) (m := m) K X) :=
  (measurableSet_successRecordWithSelector
    (Ξ := Ξ) (n := n) (m := m) K X hX).compl

/-- Corollary 3.8: pulling back the lifted failure record gives the complement
of the corresponding attempt success event. -/
theorem failureRecordWithSelector_preimage
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun omega ↦
      (restart.outputIndex i omega,
        stoppedAttemptFiniteObservable (restart.attempt i) omega)) ⁻¹'
        failureRecordWithSelector (Ξ := Ξ) (n := n) (m := m) K X =
      (successEvent restart i)ᶜ := by
  rw [failureRecordWithSelector, Set.preimage_compl,
    successRecordWithSelector_preimage restart i]

/-- Corollary 3.8: the number of actually executed transitions in one finite
stopped attempt. -/
noncomputable def attemptIterations
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) : ℕ :=
  (restart.attempt i).executedIterations omega

/-- Corollary 3.8: the work of one stopped attempt never exceeds the horizon. -/
theorem attemptIterations_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) : attemptIterations restart i omega ≤ K := by
  rw [attemptIterations,
    StoppedAttempt.executedIterations_eq_min_firstExitEndpoint]
  exact min_le_left _ _

/-- Corollary 3.8: a successful stopped attempt executes all `K`
transitions. -/
theorem attemptIterations_eq_K_of_success
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) (hsuccess : omega ∈ successEvent restart i) :
    attemptIterations restart i omega = K := by
  have hexit : StoppedAttempt.firstExitEndpoint (restart.attempt i) omega = K + 1 :=
    ((restart.attempt i).mem_successEvent_iff_firstExitEndpoint_eq_succ omega).mp
      hsuccess
  rw [attemptIterations,
    StoppedAttempt.executedIterations_eq_min_firstExitEndpoint, hexit]
  omega

/-- Corollary 3.8: the Boolean completion indicator of one stopped attempt. -/
noncomputable def completionIndicator
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) : Bool :=
  @decide (omega ∈ successEvent restart i) (Classical.propDecidable _)

/-- Corollary 3.8: completion is equivalent to finite success. -/
theorem completionIndicator_eq_true
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) :
    completionIndicator restart i omega = true ↔
      omega ∈ successEvent restart i := by
  simp only [completionIndicator, decide_eq_true_eq]

/-- Corollary 3.8: the first successful finite attempt, or `⊤` if no attempt
succeeds. -/
noncomputable def firstAccepted
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) : Ω → ℕ∞ :=
  MeasureTheory.hittingAfter (fun i omega ↦ completionIndicator restart i omega)
    {true} 0

/-- Corollary 3.8: first acceptance is infinite exactly when every finite
attempt fails. -/
theorem firstAccepted_eq_top_iff
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) :
    firstAccepted restart omega = ⊤ ↔
      ∀ i, completionIndicator restart i omega ≠ true := by
  change (MeasureTheory.hittingAfter
      (fun i omega ↦ completionIndicator restart i omega) {true} 0 omega =
      (⊤ : WithTop ℕ) ↔ ∀ i, completionIndicator restart i omega ≠ true)
  rw [MeasureTheory.hittingAfter_eq_top_iff]
  simp only [Nat.zero_le, true_imp_iff, Set.mem_singleton_iff]

/-- Corollary 3.8: a finite first accepted index is successful. -/
theorem firstAccepted_completion
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) (htermination : firstAccepted restart omega ≠ ⊤) :
    completionIndicator restart
      ((firstAccepted restart omega).untop htermination) omega = true := by
  have hmem : completionIndicator restart
      (firstAccepted restart omega).untopA omega ∈ ({true} : Set Bool) := by
    simpa only [firstAccepted] using
      (MeasureTheory.hittingAfter_mem_set_of_ne_top
        (u := fun i omega ↦ completionIndicator restart i omega)
        (s := ({true} : Set Bool)) (n := 0) (ω := omega) htermination)
  have hindex : (firstAccepted restart omega).untopA =
      (firstAccepted restart omega).untop htermination :=
    WithTop.untopA_eq_untop htermination
  rw [hindex] at hmem
  simpa only [Set.mem_singleton_iff] using hmem

/-- Corollary 3.8: finite first acceptance is characterized by success at that
index and failure at all previous indices. -/
theorem firstAccepted_eq_coe_iff
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) :
    firstAccepted restart omega = (i : ℕ∞) ↔
      completionIndicator restart i omega = true ∧
        ∀ j < i, completionIndicator restart j omega ≠ true := by
  constructor
  · intro hfirst
    have htermination : firstAccepted restart omega ≠ ⊤ := by
      rw [hfirst]
      exact ENat.coe_ne_top i
    constructor
    · have hsuccess := firstAccepted_completion restart omega htermination
      have hindex : (firstAccepted restart omega).untop htermination = i := by
        apply WithTop.coe_injective
        calc
          ((firstAccepted restart omega).untop htermination : ℕ∞) =
              firstAccepted restart omega := WithTop.coe_untop _ _
          _ = (i : ℕ∞) := hfirst
      rwa [hindex] at hsuccess
    · intro j hji
      have hjlt : (j : WithTop ℕ) < MeasureTheory.hittingAfter
          (fun i omega ↦ completionIndicator restart i omega)
          ({true} : Set Bool) 0 omega := by
        rw [show MeasureTheory.hittingAfter
            (fun i omega ↦ completionIndicator restart i omega)
              ({true} : Set Bool) 0 omega = (i : WithTop ℕ) from hfirst]
        exact WithTop.coe_lt_coe.mpr hji
      have hnotMem := MeasureTheory.notMem_of_lt_hittingAfter
        (u := fun i omega ↦ completionIndicator restart i omega)
        (s := ({true} : Set Bool)) (n := 0) (k := j) (ω := omega)
        hjlt (Nat.zero_le j)
      simpa only [Set.mem_singleton_iff] using hnotMem
  · rintro ⟨hiSuccess, hprior⟩
    have hiMem : completionIndicator restart i omega ∈ ({true} : Set Bool) := by
      simpa only [Set.mem_singleton_iff] using hiSuccess
    have hle := MeasureTheory.hittingAfter_le_of_mem
      (u := fun i omega ↦ completionIndicator restart i omega)
      (s := ({true} : Set Bool)) (n := 0) (ω := omega)
      (Nat.zero_le i) hiMem
    have hge : (i : ℕ∞) ≤ firstAccepted restart omega := by
      apply le_of_not_gt
      intro hlt
      have htermination : firstAccepted restart omega ≠ ⊤ :=
        ne_top_of_lt (hlt.trans (WithTop.coe_lt_top i))
      have hjlt : (firstAccepted restart omega).untop htermination < i :=
        (WithTop.untop_lt_iff htermination).mpr hlt
      apply hprior ((firstAccepted restart omega).untop htermination) hjlt
      exact firstAccepted_completion restart omega htermination
    exact le_antisymm hle hge

/-- Corollary 3.8: the one-based number of attempted finite runs, infinite on
nontermination. -/
noncomputable def attemptCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) : ℕ∞ :=
  firstAccepted restart omega + 1

/-- Corollary 3.8: attempt count is infinite exactly on nontermination. -/
theorem attemptCount_eq_top_iff
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) :
    attemptCount restart omega = ⊤ ↔ firstAccepted restart omega = ⊤ := by
  simp only [attemptCount, ENat.add_eq_top, ENat.one_ne_top, or_false]

/-- Corollary 3.8: the primal point returned by the first accepted finite
attempt, with index zero used on the nontermination branch. -/
noncomputable def returnedPoint
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) : EuclideanSpace ℝ (Fin n) :=
  let i := (firstAccepted restart omega).untopD 0
  StoppedAttemptAnalysis.canonicalPointNat (restart.attempt i)
    (restart.outputIndex i omega + 1) omega

/-- Corollary 3.8: the multiplier returned by the first accepted finite
attempt, using the same default index. -/
noncomputable def returnedMultiplier
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) : EuclideanSpace ℝ (Fin m) :=
  let i := (firstAccepted restart omega).untopD 0
  StoppedAttemptAnalysis.canonicalMultiplierNat (restart.attempt i)
    (restart.outputIndex i omega + 1) omega

/-- Corollary 3.8: expose the selected stopped point underlying the returned
point. -/
theorem returnedPoint_apply
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) :
    returnedPoint restart omega =
      StoppedAttemptAnalysis.canonicalPointNat
        (restart.attempt ((firstAccepted restart omega).untopD 0))
        (restart.outputIndex ((firstAccepted restart omega).untopD 0) omega + 1)
        omega := by
  rfl

/-- Corollary 3.8: expose the selected stopped multiplier underlying the
returned multiplier. -/
theorem returnedMultiplier_apply
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) :
    returnedMultiplier restart omega =
      StoppedAttemptAnalysis.canonicalMultiplierNat
        (restart.attempt ((firstAccepted restart omega).untopD 0))
        (restart.outputIndex ((firstAccepted restart omega).untopD 0) omega + 1)
        omega := by
  rfl

end StoppedSafeguardedRestart

end LALM.FiniteStopped

end
