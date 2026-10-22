/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.CertifiedStoppedRestart
public import TR_LALM_theory.Corollary_4_2.Stochastic

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LALM.Correction

universe u v

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
variable {confidence : ℝ} {K : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
variable {hK : 2 ≤ K}
variable {Q B b : ℕ+}

open StoppedAttemptAnalysis
open StoppedSafeguardedRestart

/-- Corollary 4.2: the squared residual selected from one stopped restart
attempt. -/
noncomputable def selectedStoppedResidual
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal
    (KKT.residual f c
      (StoppedAttempt.point (restart.attempt i)
        (restart.outputIndex i ω + 1) ω)
      (StoppedAttempt.multiplier (restart.attempt i)
        (restart.outputIndex i ω + 1) ω) ^ 2)

/-- Corollary 4.2: the success/residual observable of one stopped attempt. -/
noncomputable def stoppedSuccessResidualObservable
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) : ℝ≥0∞ × ℝ≥0∞ :=
  ((successEvent restart i).indicator (fun _ ↦ 1) ω,
    (successEvent restart i).indicator (selectedStoppedResidual restart i) ω)

/-- Helper for Corollary 4.2: the success weight and restricted residual as a
function of one finite stopped output record. -/
noncomputable def stoppedOutputRecordSummary
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (output : stoppedAttemptOutputRecordType Ξ n m K) : ℝ≥0∞ × ℝ≥0∞ :=
  ((successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X).indicator
      (fun _ ↦ 1) output,
    outputResidualIntegrand (h := h) K X output)

/-- Helper for Corollary 4.2: the successful finite output-record set is
measurable. -/
theorem measurableSet_successfulOutputRecord
    (hX : MeasurableSet X) :
    MeasurableSet
      (successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X) := by
  exact StoppedAttemptAnalysis.measurableSet_successfulOutputRecord K X hX

/-- Helper for Corollary 4.2: a supported record selector reads the same primal
coordinate as the padded stopped path. -/
theorem stoppedOutputRecord_point_eq
    (attempt : StoppedAttempt h oracle ℙ x₀ multiplier₀ params Q B b
      confidence K X)
    (k : ℕ) (hk : k < K + 1) (ω : Ω) :
    (stoppedAttemptFiniteObservable attempt ω).2.1
        (Fin.ofNat (K + 1) k) =
      StoppedAttempt.point attempt k ω := by
  exact stoppedAttemptFiniteObservable_point attempt k hk ω

/-- Helper for Corollary 4.2: a supported record selector reads the same
multiplier coordinate as the padded stopped path. -/
theorem stoppedOutputRecord_multiplier_eq
    (attempt : StoppedAttempt h oracle ℙ x₀ multiplier₀ params Q B b
      confidence K X)
    (k : ℕ) (hk : k < K + 1) (ω : Ω) :
    (stoppedAttemptFiniteObservable attempt ω).2.2.1
        (Fin.ofNat (K + 1) k) =
      StoppedAttempt.multiplier attempt k ω := by
  exact stoppedAttemptFiniteObservable_multiplier attempt k hk ω

/-- Helper for Corollary 4.2: the actual selector paired with its finite stopped
attempt observable. -/
noncomputable def stoppedOutputJoint
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) : stoppedAttemptOutputRecordType Ξ n m K :=
  (restart.outputIndex i ω,
    stoppedAttemptFiniteObservable (restart.attempt i) ω)

/-- Helper for Corollary 4.2: finite-record success is exactly stopped-attempt
success on an actual attempt observable. -/
theorem finiteObservable_mem_successRecord_iff
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) :
    stoppedAttemptFiniteObservable (restart.attempt i) ω ∈
        successRecord (Ξ := Ξ) (n := n) (m := m) K X ↔
      ω ∈ successEvent restart i := by
  change ω ∈ (fun ω ↦ stoppedAttemptFiniteObservable (restart.attempt i) ω) ⁻¹'
      successRecord (Ξ := Ξ) (n := n) (m := m) K X ↔
    ω ∈ successEvent restart i
  rw [successRecord_preimage restart i]

/-- Helper for Corollary 4.2: the actual selector/record pair has the reference
product law used by the finite attempt certificate. -/
theorem hasLaw_stoppedOutputJoint
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : ProbabilityTheory.HasLaw (stoppedOutputJoint restart i)
      (stoppedAttemptOutputMeasure (restart.attempt i) hK) ℙ := by
  let observable := fun ω ↦
    stoppedAttemptFiniteObservable (restart.attempt i) ω
  have hobservable : Measurable observable :=
    measurable_stoppedAttemptFiniteObservable (restart.attempt i)
  have hobservableLaw : ProbabilityTheory.HasLaw observable
      (ℙ.map observable) ℙ :=
    ⟨hobservable.aemeasurable, rfl⟩
  have hjointLaw := (restart.outputIndex_indep_attempt i).hasLaw_prod
    (restart.outputIndex_hasLaw i) hobservableLaw
  rw [StoppedAttemptAnalysis.stoppedAttemptOutputMeasure_def]
  change ProbabilityTheory.HasLaw
    (fun ω ↦ (restart.outputIndex i ω, observable ω)) _ ℙ
  exact hjointLaw

/-- Helper for Corollary 4.2: evaluating the record residual on an actual
selector/attempt pair gives the success-restricted raw residual almost surely. -/
theorem outputResidualIntegrand_actual
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun ω ↦ outputResidualIntegrand (h := h) K X
        (stoppedOutputJoint restart i ω)) =ᵐ[ℙ]
      fun ω ↦ (successEvent restart i).indicator
        (selectedStoppedResidual restart i) ω := by
  filter_upwards [ae_outputIndex_mem_uniformRange restart i] with ω hindex
  have hindexLt : restart.outputIndex i ω + 1 < K + 1 := by
    have hbounds := Finset.mem_Icc.mp hindex
    omega
  by_cases hsuccess : ω ∈ successEvent restart i
  · have hrecord : stoppedOutputJoint restart i ω ∈
        successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X := by
      apply (StoppedAttemptAnalysis.mem_successfulOutputRecord_iff K X _).mpr
      exact ⟨hindex,
        (finiteObservable_mem_successRecord_iff restart i ω).mpr hsuccess⟩
    have hattemptSuccess :
        ω ∈ StoppedAttempt.successEvent (restart.attempt i) := by
      rw [← successEvent_eq_attempt_success restart i]
      exact hsuccess
    have hselectedOne : 1 ≤ restart.outputIndex i ω + 1 := by omega
    have hselectedK : restart.outputIndex i ω + 1 ≤ K := by
      have hbounds := Finset.mem_Icc.mp hindex
      omega
    have hselectedX : StoppedAttempt.point (restart.attempt i)
        (restart.outputIndex i ω + 1) ω ∈ X :=
      (StoppedAttempt.mem_successEvent_iff_points_mem
        (restart.attempt i) ω).mp hattemptSuccess _ hselectedOne hselectedK
    have hXregion : X ⊆ h.region := fun x hx ↦
      (restart.attempt i).region_condition.thickening_subset
        (Metric.self_subset_cthickening X hx)
    have hselectedRegion :
        StoppedAttempt.point (restart.attempt i)
            (restart.outputIndex i ω + 1) ω ∈ h.region := by
      apply hXregion
      exact hselectedX
    have hextension := KKT.residualExtension_eq h
      (z := (StoppedAttempt.point (restart.attempt i)
          (restart.outputIndex i ω + 1) ω,
        StoppedAttempt.multiplier (restart.attempt i)
          (restart.outputIndex i ω + 1) ω)) hselectedRegion
    rw [StoppedAttemptAnalysis.outputResidualIntegrand_def,
      Set.indicator_of_mem hrecord, Set.indicator_of_mem hsuccess]
    simp only [stoppedOutputJoint]
    rw [stoppedOutputRecord_point_eq (restart.attempt i)
        (restart.outputIndex i ω + 1) hindexLt ω,
      stoppedOutputRecord_multiplier_eq (restart.attempt i)
        (restart.outputIndex i ω + 1) hindexLt ω,
      hextension]
    rfl
  · have hrecord : stoppedOutputJoint restart i ω ∉
        successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X := by
      intro hrecord
      have hrecordSuccess :=
        (StoppedAttemptAnalysis.mem_successfulOutputRecord_iff K X _).mp hrecord
      exact hsuccess
        ((finiteObservable_mem_successRecord_iff restart i ω).mp hrecordSuccess.2)
    rw [StoppedAttemptAnalysis.outputResidualIntegrand_def,
      Set.indicator_of_notMem hrecord, Set.indicator_of_notMem hsuccess]

/-- Helper for Corollary 4.2: the record success weight agrees almost surely
with the actual stopped success indicator. -/
theorem stoppedOutputRecordSuccessWeight_actual
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun ω ↦
      (successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) (stoppedOutputJoint restart i ω)) =ᵐ[ℙ]
      fun ω ↦ (successEvent restart i).indicator (fun _ ↦ 1) ω := by
  filter_upwards [ae_outputIndex_mem_uniformRange restart i] with ω hindex
  by_cases hsuccess : ω ∈ successEvent restart i
  · have hrecord : stoppedOutputJoint restart i ω ∈
        successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X := by
      apply (StoppedAttemptAnalysis.mem_successfulOutputRecord_iff K X _).mpr
      exact ⟨hindex,
        (finiteObservable_mem_successRecord_iff restart i ω).mpr hsuccess⟩
    rw [Set.indicator_of_mem hrecord, Set.indicator_of_mem hsuccess]
  · have hrecord : stoppedOutputJoint restart i ω ∉
        successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X := by
      intro hrecord
      have hrecordSuccess :=
        (StoppedAttemptAnalysis.mem_successfulOutputRecord_iff K X _).mp hrecord
      exact hsuccess
        ((finiteObservable_mem_successRecord_iff restart i ω).mp hrecordSuccess.2)
    rw [Set.indicator_of_notMem hrecord, Set.indicator_of_notMem hsuccess]

/-- Helper for Corollary 4.2: the record summary agrees almost surely with the
actual stopped success/residual observable. -/
theorem stoppedOutputRecordSummary_actual
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun ω ↦ stoppedOutputRecordSummary (h := h) K X
      (stoppedOutputJoint restart i ω)) =ᵐ[ℙ]
        stoppedSuccessResidualObservable restart i := by
  filter_upwards [stoppedOutputRecordSuccessWeight_actual restart i,
    outputResidualIntegrand_actual restart i] with ω hsuccess hresidual
  exact Prod.ext hsuccess hresidual

/-- Helper for Corollary 4.2: evaluate the finite stopped primal record at its
uniform output index. -/
def stoppedOutputRecordPoint
    (output : stoppedAttemptOutputRecordType Ξ n m K) :
    EuclideanSpace ℝ (Fin n) :=
  output.2.2.1 (Fin.ofNat (K + 1) (output.1 + 1))

/-- Helper for Corollary 4.2: evaluate the finite stopped multiplier record at
its uniform output index. -/
def stoppedOutputRecordMultiplier
    (output : stoppedAttemptOutputRecordType Ξ n m K) :
    EuclideanSpace ℝ (Fin m) :=
  output.2.2.2.1 (Fin.ofNat (K + 1) (output.1 + 1))

/-- Helper for Corollary 4.2: the selected primal point from one stopped
attempt. -/
noncomputable def selectedStoppedPoint
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  StoppedAttempt.point (restart.attempt i)
    (restart.outputIndex i ω + 1) ω

/-- Helper for Corollary 4.2: the selected multiplier from one stopped attempt. -/
noncomputable def selectedStoppedMultiplier
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin m) :=
  StoppedAttempt.multiplier (restart.attempt i)
    (restart.outputIndex i ω + 1) ω

/-- Helper for Corollary 4.2: the finite record primal evaluator is measurable. -/
theorem measurable_stoppedOutputRecordPoint :
    Measurable (stoppedOutputRecordPoint (Ξ := Ξ) (n := n) (m := m) (K := K)) := by
  let pointProjection :
      stoppedAttemptFiniteObservableType Ξ n m K →
        (Fin (K + 1) → EuclideanSpace ℝ (Fin n)) :=
    fun output ↦ output.2.1
  have hpointProjection : Measurable pointProjection := by
    have hrest : Measurable
        (fun output : stoppedAttemptFiniteObservableType Ξ n m K ↦ output.2) :=
      measurable_snd
    exact measurable_fst.comp hrest
  let g : ℕ → stoppedAttemptFiniteObservableType Ξ n m K →
      EuclideanSpace ℝ (Fin n) :=
    fun k output ↦ pointProjection output (Fin.ofNat (K + 1) (k + 1))
  have hg : ∀ k, Measurable (g k) := by
    intro k
    exact (measurable_pi_apply (Fin.ofNat (K + 1) (k + 1))).comp
      hpointProjection
  have hglobal : Measurable
      (fun output : ℕ × stoppedAttemptFiniteObservableType Ξ n m K ↦
        g output.1 output.2) :=
    measurable_from_prod_countable_right (fun k ↦ hg k)
  change Measurable
    (fun output : ℕ × stoppedAttemptFiniteObservableType Ξ n m K ↦
      output.2.2.1 (Fin.ofNat (K + 1) (output.1 + 1)))
  simpa only [g, pointProjection] using hglobal

/-- Helper for Corollary 4.2: the finite record multiplier evaluator is
measurable. -/
theorem measurable_stoppedOutputRecordMultiplier :
    Measurable
      (stoppedOutputRecordMultiplier (Ξ := Ξ) (n := n) (m := m) (K := K)) := by
  let multiplierProjection :
      stoppedAttemptFiniteObservableType Ξ n m K →
        (Fin (K + 1) → EuclideanSpace ℝ (Fin m)) :=
    fun output ↦ output.2.2.1
  have hmultiplierProjection : Measurable multiplierProjection := by
    have hrest : Measurable
        (fun output : stoppedAttemptFiniteObservableType Ξ n m K ↦ output.2) :=
      measurable_snd
    have hmultiplierRest : Measurable
        (fun output : stoppedAttemptFiniteObservableType Ξ n m K ↦ output.2.2) :=
      measurable_snd.comp hrest
    exact measurable_fst.comp hmultiplierRest
  let g : ℕ → stoppedAttemptFiniteObservableType Ξ n m K →
      EuclideanSpace ℝ (Fin m) :=
    fun k output ↦ multiplierProjection output (Fin.ofNat (K + 1) (k + 1))
  have hg : ∀ k, Measurable (g k) := by
    intro k
    exact (measurable_pi_apply (Fin.ofNat (K + 1) (k + 1))).comp
      hmultiplierProjection
  have hglobal : Measurable
      (fun output : ℕ × stoppedAttemptFiniteObservableType Ξ n m K ↦
        g output.1 output.2) :=
    measurable_from_prod_countable_right (fun k ↦ hg k)
  change Measurable
    (fun output : ℕ × stoppedAttemptFiniteObservableType Ξ n m K ↦
      output.2.2.2.1 (Fin.ofNat (K + 1) (output.1 + 1)))
  simpa only [g, multiplierProjection] using hglobal

/-- Helper for Corollary 4.2: the finite record primal evaluator agrees almost
everywhere with the actual selected stopped path. -/
theorem stoppedOutputRecordPoint_actual
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun ω ↦ stoppedOutputRecordPoint (stoppedOutputJoint restart i ω)) =ᵐ[ℙ]
      selectedStoppedPoint restart i := by
  filter_upwards [ae_outputIndex_mem_uniformRange restart i] with ω hindex
  have hbounds := Finset.mem_Icc.mp hindex
  have hk : restart.outputIndex i ω + 1 < K + 1 := by omega
  simpa only [stoppedOutputRecordPoint, stoppedOutputJoint,
    selectedStoppedPoint] using
    stoppedOutputRecord_point_eq (restart.attempt i)
      (restart.outputIndex i ω + 1) hk ω

/-- Helper for Corollary 4.2: the finite record multiplier evaluator agrees
almost everywhere with the actual selected stopped path. -/
theorem stoppedOutputRecordMultiplier_actual
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun ω ↦ stoppedOutputRecordMultiplier (stoppedOutputJoint restart i ω)) =ᵐ[ℙ]
      selectedStoppedMultiplier restart i := by
  filter_upwards [ae_outputIndex_mem_uniformRange restart i] with ω hindex
  have hbounds := Finset.mem_Icc.mp hindex
  have hk : restart.outputIndex i ω + 1 < K + 1 := by omega
  simpa only [stoppedOutputRecordMultiplier, stoppedOutputJoint,
    selectedStoppedMultiplier] using
    stoppedOutputRecord_multiplier_eq (restart.attempt i)
      (restart.outputIndex i ω + 1) hk ω

/-- Corollary 4.2: the selected primal point of a fixed stopped attempt is
almost everywhere measurable. -/
theorem selectedStoppedPoint_aemeasurable
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : AEMeasurable (selectedStoppedPoint restart i) ℙ := by
  have hjoint : AEMeasurable (stoppedOutputJoint restart i) ℙ :=
    (hasLaw_stoppedOutputJoint restart i).aemeasurable
  have hcomp : AEMeasurable
      (fun ω ↦ stoppedOutputRecordPoint (stoppedOutputJoint restart i ω)) ℙ :=
    measurable_stoppedOutputRecordPoint.comp_aemeasurable hjoint
  exact hcomp.congr (stoppedOutputRecordPoint_actual restart i)

/-- Corollary 4.2: the selected multiplier of a fixed stopped attempt is
almost everywhere measurable. -/
theorem selectedStoppedMultiplier_aemeasurable
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : AEMeasurable (selectedStoppedMultiplier restart i) ℙ := by
  have hjoint : AEMeasurable (stoppedOutputJoint restart i) ℙ :=
    (hasLaw_stoppedOutputJoint restart i).aemeasurable
  have hcomp : AEMeasurable
      (fun ω ↦ stoppedOutputRecordMultiplier (stoppedOutputJoint restart i ω)) ℙ :=
    measurable_stoppedOutputRecordMultiplier.comp_aemeasurable hjoint
  exact hcomp.congr (stoppedOutputRecordMultiplier_actual restart i)

/-- Corollary 4.2: the fixed-attempt selected residual integral is exactly the
certificate's reference product-law numerator. -/
theorem successRestrictedSelectedResidual_eq_certificateNumerator
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (∫⁻ ω in successEvent certified.restart i,
      selectedStoppedResidual certified.restart i ω ∂ℙ) =
      successRestrictedResidualNumerator (certified.restart.attempt i) hK := by
  have hsuccess : MeasurableSet (successEvent certified.restart i) :=
    StoppedSafeguardedRestart.measurableSet_successEvent certified.restart i
  have hjoint := hasLaw_stoppedOutputJoint certified.restart i
  calc
    (∫⁻ ω in successEvent certified.restart i,
        selectedStoppedResidual certified.restart i ω ∂ℙ) =
        ∫⁻ ω, (successEvent certified.restart i).indicator
          (selectedStoppedResidual certified.restart i) ω ∂ℙ :=
      (lintegral_indicator₀ hsuccess.nullMeasurableSet _).symm
    _ = ∫⁻ ω, outputResidualIntegrand (h := h) K X
        (stoppedOutputJoint certified.restart i ω) ∂ℙ := by
      exact lintegral_congr_ae
        (outputResidualIntegrand_actual certified.restart i).symm
    _ = ∫⁻ output, outputResidualIntegrand (h := h) K X output
        ∂stoppedAttemptOutputMeasure (certified.restart.attempt i) hK :=
      hjoint.lintegral_comp
        (measurable_outputResidualIntegrand K X
          (certified.restart.attempt_localization_measurableSet i)).aemeasurable
    _ = successRestrictedResidualNumerator (certified.restart.attempt i) hK := by
      rw [successRestrictedResidualNumerator_def]

/-- Helper for Corollary 4.2: the record success/residual summary is
almost-everywhere measurable under the certificate's reference law. -/
theorem stoppedOutputRecordSummary_aemeasurable
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    AEMeasurable (stoppedOutputRecordSummary (h := h) K X)
      (stoppedAttemptOutputMeasure (certified.restart.attempt i) hK) := by
  exact (measurable_const.indicator
      (measurableSet_successfulOutputRecord
        (certified.restart.attempt_localization_measurableSet i))).aemeasurable.prodMk
    (measurable_outputResidualIntegrand K X
      (certified.restart.attempt_localization_measurableSet i)).aemeasurable

/-- Helper for Corollary 4.2: the actual success/residual observables of a
certified stopped restart are almost-everywhere measurable. -/
theorem certified_stoppedSuccessResidual_aemeasurable
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    AEMeasurable (stoppedSuccessResidualObservable certified.restart i) ℙ := by
  have hjoint := hasLaw_stoppedOutputJoint certified.restart i
  have hrecord : AEMeasurable
      (stoppedOutputRecordSummary (h := h) K X)
      (ℙ.map (stoppedOutputJoint certified.restart i)) := by
    rw [hjoint.map_eq]
    exact stoppedOutputRecordSummary_aemeasurable certified i
  have hcomp : AEMeasurable
      (fun ω ↦ stoppedOutputRecordSummary (h := h) K X
        (stoppedOutputJoint certified.restart i ω)) ℙ :=
    hrecord.comp_aemeasurable hjoint.aemeasurable
  exact hcomp.congr (stoppedOutputRecordSummary_actual certified.restart i)

/-- Corollary 4.2: complete stopped attempts induce mutually independent
success/residual observables. -/
theorem certified_stoppedSuccessResidual_iIndep
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) :
    ProbabilityTheory.iIndepFun
      (fun i ↦ stoppedSuccessResidualObservable certified.restart i) ℙ := by
  let f : ℕ → Ω → stoppedAttemptOutputRecordType Ξ n m K :=
    fun i ↦ stoppedOutputJoint certified.restart i
  let g : ℕ → stoppedAttemptOutputRecordType Ξ n m K →
      ℝ≥0∞ × ℝ≥0∞ :=
    fun _i ↦ stoppedOutputRecordSummary (h := h) K X
  have hf : ∀ i, AEMeasurable (f i) ℙ := by
    intro i
    exact (hasLaw_stoppedOutputJoint certified.restart i).aemeasurable
  have hg : ∀ i, AEMeasurable (g i) (ℙ.map (f i)) := by
    intro i
    change AEMeasurable
      (stoppedOutputRecordSummary (h := h) K X)
      (ℙ.map (stoppedOutputJoint certified.restart i))
    rw [(hasLaw_stoppedOutputJoint certified.restart i).map_eq]
    exact stoppedOutputRecordSummary_aemeasurable certified i
  have hrecord := certified.restart.independent_attempt.comp₀ g hf hg
  have hactual : ∀ i, (g i ∘ f i) =ᵐ[ℙ]
      stoppedSuccessResidualObservable certified.restart i := by
    intro i
    exact stoppedOutputRecordSummary_actual certified.restart i
  have hrecord' := hrecord.congr hactual
  simpa only [Function.comp_apply, f, g] using hrecord'

/-- Corollary 4.2: the event that every stopped attempt before `i` fails. -/
def priorStoppedFailureEvent
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : Set Ω :=
  ⋂ j ∈ Finset.range i, (successEvent restart j)ᶜ

/-- Corollary 4.2: the indicator of prior stopped-attempt failure. -/
noncomputable def priorStoppedFailureWeight
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (priorStoppedFailureEvent restart i).indicator (fun _ ↦ 1) ω

/-- Corollary 4.2: the expected squared residual of the returned stopped pair. -/
noncomputable def stoppedResidualMeanSquare
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) : ℝ≥0∞ :=
  KKT.Stochastic.residualMeanSquare ℙ f c
    (StoppedSafeguardedRestart.returnedPoint restart)
    (StoppedSafeguardedRestart.returnedMultiplier restart)

/-- Corollary 4.2: the returned residual is the selected residual at the
defaulted first-accepted attempt. -/
theorem stoppedReturnedResidual_eq_selected
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) :
    ENNReal.ofReal
        (KKT.residual f c (StoppedSafeguardedRestart.returnedPoint restart ω)
          (StoppedSafeguardedRestart.returnedMultiplier restart ω) ^ 2) =
      selectedStoppedResidual restart
        ((StoppedSafeguardedRestart.firstAccepted restart ω).untopD 0) ω := by
  rw [StoppedSafeguardedRestart.returnedPoint_apply,
    StoppedSafeguardedRestart.returnedMultiplier_apply]
  rfl

/-- Corollary 4.2: a finite first-accepted index lies in its success event. -/
lemma stoppedUntopD_eq_untop (a : ℕ∞) (d : ℕ) (ha : a ≠ ⊤) :
    a.untopD d = a.untop ha := by
  cases a using ENat.recTopCoe with
  | top => exact False.elim (ha rfl)
  | coe k => rfl

/-- Corollary 4.2: a finite first-accepted index lies in its success event. -/
theorem stoppedSelected_mem_success
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) (htermination : firstAccepted restart ω ≠ ⊤) :
    ω ∈ successEvent restart ((firstAccepted restart ω).untopD 0) := by
  have hindex : (firstAccepted restart ω).untopD 0 =
      (firstAccepted restart ω).untop htermination := by
    exact stoppedUntopD_eq_untop _ 0 htermination
  rw [hindex]
  have hcompletion := firstAccepted_completion restart ω htermination
  rw [completionIndicator_eq_true] at hcompletion
  exact hcompletion

/-- Corollary 4.2: the first-accepted fiber is prior failure intersected with
the current stopped success event. -/
theorem stoppedFirstAcceptedFiber_eq
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    {ω | firstAccepted restart ω = (i : ℕ∞)} =
      priorStoppedFailureEvent restart i ∩ successEvent restart i := by
  ext ω
  rw [Set.mem_setOf_eq, firstAccepted_eq_coe_iff]
  simp only [priorStoppedFailureEvent, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_compl_iff, Finset.mem_range]
  constructor
  · rintro ⟨hsuccess, hprior⟩
    constructor
    · intro j hj hmem
      apply hprior j hj
      exact (completionIndicator_eq_true restart j ω).mpr hmem
    · exact (completionIndicator_eq_true restart i ω).mp hsuccess
  · rintro ⟨hprior, hsuccess⟩
    constructor
    · exact (completionIndicator_eq_true restart i ω).mpr hsuccess
    · intro j hj hcompletion
      exact hprior j hj ((completionIndicator_eq_true restart j ω).mp hcompletion)

/-- Corollary 4.2: prior stopped failures are measurable. -/
theorem measurableSet_priorStoppedFailureEvent
    (_hX : MeasurableSet X)
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : MeasurableSet (priorStoppedFailureEvent restart i) := by
  unfold priorStoppedFailureEvent
  apply (Finset.range i).measurableSet_biInter
  intro j hj
  exact (StoppedSafeguardedRestart.measurableSet_successEvent restart j).compl

/-- Corollary 4.2: every finite first-accepted fiber is measurable. -/
theorem measurableSet_stoppedFirstAcceptedFiber
    (hX : MeasurableSet X)
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : MeasurableSet {ω | firstAccepted restart ω = (i : ℕ∞)} := by
  rw [stoppedFirstAcceptedFiber_eq restart i]
  exact (measurableSet_priorStoppedFailureEvent hX restart i).inter
    (StoppedSafeguardedRestart.measurableSet_successEvent restart i)

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Corollary 4.2: almost-everywhere measurable functions on a
countable null-measurable conull partition glue to a global function. -/
private lemma aemeasurable_of_eq_on_countable_partition_stopped
    {E : Type*} [MeasurableSpace E]
    (sets : ℕ → Set Ω) (hsets : ∀ i, NullMeasurableSet (sets i) ℙ)
    (hcover : ∀ᵐ omega ∂ℙ, omega ∈ ⋃ i, sets i)
    (selected : ℕ → Ω → E) (returned : Ω → E)
    (hselected : ∀ i, AEMeasurable (selected i) ℙ)
    (heq : ∀ i omega, omega ∈ sets i → returned omega = selected i omega) :
    AEMeasurable returned ℙ := by
  have hrestricted : AEMeasurable returned (ℙ.restrict (⋃ i, sets i)) := by
    rw [aemeasurable_iUnion_iff]
    intro i
    have hselectedRestricted :
        AEMeasurable (selected i) (ℙ.restrict (sets i)) :=
      (hselected i).mono_measure Measure.restrict_le_self
    have heqAE : selected i =ᵐ[ℙ.restrict (sets i)] returned :=
      (ae_restrict_mem₀ (hsets i)).mono fun omega homega ↦
        (heq i omega homega).symm
    exact hselectedRestricted.congr heqAE
  have hmeasure : ℙ.restrict (⋃ i, sets i) = ℙ :=
    Measure.restrict_eq_self_of_ae_mem hcover
  rwa [hmeasure] at hrestricted

/-- Helper for Corollary 4.2: almost-sure termination makes the union of all
finite first-accepted fibers conull. -/
theorem stoppedFirstAcceptedFiberUnion_ae
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (htermination : ∀ᵐ omega ∂ℙ, firstAccepted restart omega ≠ ⊤) :
    ∀ᵐ omega ∂ℙ,
      omega ∈ ⋃ i : ℕ, {omega | firstAccepted restart omega = (i : ℕ∞)} := by
  filter_upwards [htermination] with omega hfinite
  cases hvalue : firstAccepted restart omega using ENat.recTopCoe with
  | top => exact False.elim (hfinite hvalue)
  | coe i => exact Set.mem_iUnion.mpr ⟨i, hvalue⟩

/-- Corollary 4.2: under almost-sure termination, the returned primal point is
almost everywhere measurable. -/
theorem returnedPoint_aemeasurable
    (hX : MeasurableSet X)
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (htermination : ∀ᵐ omega ∂ℙ, firstAccepted restart omega ≠ ⊤) :
    AEMeasurable (StoppedSafeguardedRestart.returnedPoint restart) ℙ := by
  let sets : ℕ → Set Ω := fun i ↦
    {omega | firstAccepted restart omega = (i : ℕ∞)}
  have hsets (i : ℕ) : NullMeasurableSet (sets i) ℙ :=
    (measurableSet_stoppedFirstAcceptedFiber hX restart i).nullMeasurableSet
  have hcover : ∀ᵐ omega ∂ℙ, omega ∈ ⋃ i, sets i := by
    simpa only [sets] using stoppedFirstAcceptedFiberUnion_ae restart htermination
  have heq (i : ℕ) (omega : Ω) (homega : omega ∈ sets i) :
      StoppedSafeguardedRestart.returnedPoint restart omega =
        selectedStoppedPoint restart i omega := by
    have hindex : (firstAccepted restart omega).untopD 0 = i := by
      rw [homega]
      rfl
    rw [StoppedSafeguardedRestart.returnedPoint_apply]
    unfold selectedStoppedPoint
    rw [hindex]
  exact aemeasurable_of_eq_on_countable_partition_stopped sets hsets hcover
    (selectedStoppedPoint restart) (StoppedSafeguardedRestart.returnedPoint restart)
    (fun i ↦ selectedStoppedPoint_aemeasurable restart i) heq

/-- Corollary 4.2: under almost-sure termination, the returned multiplier is
almost everywhere measurable. -/
theorem returnedMultiplier_aemeasurable
    (hX : MeasurableSet X)
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (htermination : ∀ᵐ omega ∂ℙ, firstAccepted restart omega ≠ ⊤) :
    AEMeasurable (StoppedSafeguardedRestart.returnedMultiplier restart) ℙ := by
  let sets : ℕ → Set Ω := fun i ↦
    {omega | firstAccepted restart omega = (i : ℕ∞)}
  have hsets (i : ℕ) : NullMeasurableSet (sets i) ℙ :=
    (measurableSet_stoppedFirstAcceptedFiber hX restart i).nullMeasurableSet
  have hcover : ∀ᵐ omega ∂ℙ, omega ∈ ⋃ i, sets i := by
    simpa only [sets] using stoppedFirstAcceptedFiberUnion_ae restart htermination
  have heq (i : ℕ) (omega : Ω) (homega : omega ∈ sets i) :
      StoppedSafeguardedRestart.returnedMultiplier restart omega =
        selectedStoppedMultiplier restart i omega := by
    have hindex : (firstAccepted restart omega).untopD 0 = i := by
      rw [homega]
      rfl
    rw [StoppedSafeguardedRestart.returnedMultiplier_apply]
    unfold selectedStoppedMultiplier
    rw [hindex]
  exact aemeasurable_of_eq_on_countable_partition_stopped sets hsets hcover
    (selectedStoppedMultiplier restart)
      (StoppedSafeguardedRestart.returnedMultiplier restart)
    (fun i ↦ selectedStoppedMultiplier_aemeasurable restart i) heq

/-- Corollary 4.2: multiplying prior failure by current success gives the
indicator of the corresponding first-accepted fiber. -/
theorem priorStoppedFailureWeight_mul_success
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) :
    priorStoppedFailureWeight restart i ω *
        (stoppedSuccessResidualObservable restart i ω).1 =
      {ω | firstAccepted restart ω = (i : ℕ∞)}.indicator
        (fun _ ↦ (1 : ℝ≥0∞)) ω := by
  change priorStoppedFailureWeight restart i ω *
      (successEvent restart i).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω = _
  by_cases hprior : ω ∈ priorStoppedFailureEvent restart i
  · by_cases hsuccess : ω ∈ successEvent restart i
    · have hfiber : ω ∈ {ω | firstAccepted restart ω = (i : ℕ∞)} := by
        rw [stoppedFirstAcceptedFiber_eq restart i]
        exact ⟨hprior, hsuccess⟩
      unfold priorStoppedFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_mem hsuccess,
        Set.indicator_of_mem hfiber, one_mul]
    · have hnotFiber : ω ∉ {ω | firstAccepted restart ω = (i : ℕ∞)} := by
        rw [stoppedFirstAcceptedFiber_eq restart i]
        exact fun hfiber ↦ hsuccess hfiber.2
      unfold priorStoppedFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_notMem hsuccess,
        Set.indicator_of_notMem hnotFiber, mul_zero]
  · have hnotFiber : ω ∉ {ω | firstAccepted restart ω = (i : ℕ∞)} := by
      rw [stoppedFirstAcceptedFiber_eq restart i]
      exact fun hfiber ↦ hprior hfiber.1
    unfold priorStoppedFailureWeight
    rw [Set.indicator_of_notMem hprior, Set.indicator_of_notMem hnotFiber,
      zero_mul]

/-- Corollary 4.2: on a first-accepted fiber, the returned residual is the
selected residual of that fixed stopped attempt. -/
theorem stoppedReturnedResidual_eq_selected_on_fiber
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω)
    (hfirst : firstAccepted restart ω = (i : ℕ∞)) :
    ENNReal.ofReal
        (KKT.residual f c (returnedPoint restart ω)
          (returnedMultiplier restart ω) ^ 2) =
      selectedStoppedResidual restart i ω := by
  have hindex : (firstAccepted restart ω).untopD 0 = i := by
    rw [hfirst]
    rfl
  calc
    ENNReal.ofReal
        (KKT.residual f c (returnedPoint restart ω)
          (returnedMultiplier restart ω) ^ 2) =
        selectedStoppedResidual restart
          ((firstAccepted restart ω).untopD 0) ω :=
      stoppedReturnedResidual_eq_selected restart ω
    _ = selectedStoppedResidual restart i ω := by rw [hindex]

/-- Corollary 4.2: multiplying prior failure by the current restricted
residual gives the returned residual restricted to that fiber. -/
theorem priorStoppedFailureWeight_mul_residual
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) :
    priorStoppedFailureWeight restart i ω *
        (stoppedSuccessResidualObservable restart i ω).2 =
      {ω | firstAccepted restart ω = (i : ℕ∞)}.indicator
        (fun ω ↦ ENNReal.ofReal
          (KKT.residual f c (returnedPoint restart ω)
            (returnedMultiplier restart ω) ^ 2)) ω := by
  change priorStoppedFailureWeight restart i ω *
      (successEvent restart i).indicator
        (selectedStoppedResidual restart i) ω = _
  by_cases hprior : ω ∈ priorStoppedFailureEvent restart i
  · by_cases hsuccess : ω ∈ successEvent restart i
    · have hfiber : ω ∈ {ω | firstAccepted restart ω = (i : ℕ∞)} := by
        rw [stoppedFirstAcceptedFiber_eq restart i]
        exact ⟨hprior, hsuccess⟩
      unfold priorStoppedFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_mem hsuccess,
        Set.indicator_of_mem hfiber, one_mul]
      exact (stoppedReturnedResidual_eq_selected_on_fiber restart i ω hfiber).symm
    · have hnotFiber : ω ∉ {ω | firstAccepted restart ω = (i : ℕ∞)} := by
        rw [stoppedFirstAcceptedFiber_eq restart i]
        exact fun hfiber ↦ hsuccess hfiber.2
      unfold priorStoppedFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_notMem hsuccess,
        Set.indicator_of_notMem hnotFiber, mul_zero]
  · have hnotFiber : ω ∉ {ω | firstAccepted restart ω = (i : ℕ∞)} := by
      rw [stoppedFirstAcceptedFiber_eq restart i]
      exact fun hfiber ↦ hprior hfiber.1
    unfold priorStoppedFailureWeight
    rw [Set.indicator_of_notMem hprior, Set.indicator_of_notMem hnotFiber,
      zero_mul]

/-- Helper for Corollary 4.2: the finite tuple all-zero weight used to summarize
the strict prefix of independent success/residual observables. -/
noncomputable def allFirstCoordinatesZeroWeight
    {ι : Type*} (z : ι → ℝ≥0∞ × ℝ≥0∞) : ℝ≥0∞ :=
  {z | ∀ j, (z j).1 = 0}.indicator (fun _ ↦ 1) z

/-- Helper for Corollary 4.2: the finite all-zero summary is measurable. -/
theorem measurable_allFirstCoordinatesZeroWeight
    {ι : Type*} [Finite ι] :
    Measurable (allFirstCoordinatesZeroWeight (ι := ι)) := by
  have hcoordinate (j : ι) : Measurable
      (fun z : ι → ℝ≥0∞ × ℝ≥0∞ ↦ (z j).1) :=
    measurable_fst.comp (measurable_pi_apply j)
  unfold allFirstCoordinatesZeroWeight
  apply measurable_const.indicator
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun j ↦
    (measurableSet_singleton (0 : ℝ≥0∞)).preimage (hcoordinate j)

/-- Helper for Corollary 4.2: the finite all-zero summary agrees pointwise with
the prior-failure indicator. -/
theorem allFirstCoordinatesZeroWeight_eq_prior
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) :
    allFirstCoordinatesZeroWeight
        (fun j : Finset.range i ↦ stoppedSuccessResidualObservable restart j ω) =
      priorStoppedFailureWeight restart i ω := by
  classical
  by_cases hprior : ω ∈ priorStoppedFailureEvent restart i
  · have hfail : ∀ j ∈ Finset.range i, ω ∉ successEvent restart j := by
      simpa only [priorStoppedFailureEvent, Set.mem_iInter, Set.mem_compl_iff]
        using hprior
    have hsummary :
        (fun j : Finset.range i ↦ stoppedSuccessResidualObservable restart j ω) ∈
          {z | ∀ j, (z j).1 = 0} := by
      intro j
      unfold stoppedSuccessResidualObservable
      change (successEvent restart j).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) ω = 0
      rw [Set.indicator_of_notMem (hfail j j.property)]
    unfold allFirstCoordinatesZeroWeight priorStoppedFailureWeight
    rw [Set.indicator_of_mem hsummary, Set.indicator_of_mem hprior]
  · have hsummary :
        (fun j : Finset.range i ↦ stoppedSuccessResidualObservable restart j ω) ∉
          {z | ∀ j, (z j).1 = 0} := by
      intro hall
      apply hprior
      simp only [priorStoppedFailureEvent, Set.mem_iInter, Set.mem_compl_iff]
      intro j hj hsuccess
      have hzero := hall ⟨j, hj⟩
      unfold stoppedSuccessResidualObservable at hzero
      change (successEvent restart j).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) ω = 0 at hzero
      rw [Set.indicator_of_mem hsuccess] at hzero
      exact one_ne_zero hzero
    unfold allFirstCoordinatesZeroWeight priorStoppedFailureWeight
    rw [Set.indicator_of_notMem hsummary, Set.indicator_of_notMem hprior]

/-- Helper for Corollary 4.2: prior failures are independent of the current
success/residual observable whenever the stopped attempt observables are
mutually independent. -/
theorem priorStoppedFailureWeight_indep
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (hsummaryMeas : ∀ i,
      AEMeasurable (stoppedSuccessResidualObservable restart i) ℙ)
    (hsummaryIndep : ProbabilityTheory.iIndepFun
      (fun i ↦ stoppedSuccessResidualObservable restart i) ℙ)
    (i : ℕ) : ProbabilityTheory.IndepFun
      (priorStoppedFailureWeight restart i)
      (stoppedSuccessResidualObservable restart i) ℙ := by
  classical
  have hdisjoint : Disjoint (Finset.range i) {i} := by simp
  have htuple := hsummaryIndep.indepFun_finset₀
    (Finset.range i) {i} hdisjoint hsummaryMeas
  have hprojected := htuple.comp
    measurable_allFirstCoordinatesZeroWeight
    (measurable_pi_apply ⟨i, Finset.mem_singleton_self i⟩)
  refine hprojected.congr ?_ ?_
  · exact Filter.Eventually.of_forall fun ω ↦
      allFirstCoordinatesZeroWeight_eq_prior restart i ω
  · exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Corollary 4.2: a fixed stopped-attempt success-restricted integral bound
transfers to its first-accepted fiber. -/
theorem stoppedFirstAcceptedFiberResidual_le
    (hX : MeasurableSet X)
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (bound : ℝ≥0∞)
    (hsummaryMeas : ∀ i,
      AEMeasurable (stoppedSuccessResidualObservable restart i) ℙ)
    (hsummaryIndep : ProbabilityTheory.iIndepFun
      (fun i ↦ stoppedSuccessResidualObservable restart i) ℙ)
    (hfixed : ∀ i,
      (∫⁻ ω in successEvent restart i,
        selectedStoppedResidual restart i ω ∂ℙ) ≤
        ℙ (successEvent restart i) * bound)
    (i : ℕ) :
    (∫⁻ ω in {ω | firstAccepted restart ω = (i : ℕ∞)},
      ENNReal.ofReal
        (KKT.residual f c (returnedPoint restart ω)
          (returnedMultiplier restart ω) ^ 2) ∂ℙ) ≤
      ℙ {ω | firstAccepted restart ω = (i : ℕ∞)} * bound := by
  have hpriorNull : MeasurableSet (priorStoppedFailureEvent restart i) :=
    measurableSet_priorStoppedFailureEvent hX restart i
  have hfiberNull : MeasurableSet
      {ω | firstAccepted restart ω = (i : ℕ∞)} :=
    measurableSet_stoppedFirstAcceptedFiber hX restart i
  have hsuccessNull : MeasurableSet (successEvent restart i) :=
    StoppedSafeguardedRestart.measurableSet_successEvent restart i
  have hpriorMeas : AEMeasurable (priorStoppedFailureWeight restart i) ℙ := by
    unfold priorStoppedFailureWeight
    exact aemeasurable_const.indicator₀ hpriorNull.nullMeasurableSet
  have hcurrentMeas := hsummaryMeas i
  have hindependent := priorStoppedFailureWeight_indep restart hsummaryMeas
    hsummaryIndep i
  have hfactorResidual :
      (∫⁻ ω, priorStoppedFailureWeight restart i ω *
          (stoppedSuccessResidualObservable restart i ω).2 ∂ℙ) =
        (∫⁻ ω, priorStoppedFailureWeight restart i ω ∂ℙ) *
          ∫⁻ ω, (stoppedSuccessResidualObservable restart i ω).2 ∂ℙ :=
    ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      hpriorMeas hcurrentMeas.snd
        (hindependent.comp measurable_id measurable_snd)
  have hfactorSuccess :
      (∫⁻ ω, priorStoppedFailureWeight restart i ω *
          (stoppedSuccessResidualObservable restart i ω).1 ∂ℙ) =
        (∫⁻ ω, priorStoppedFailureWeight restart i ω ∂ℙ) *
          ∫⁻ ω, (stoppedSuccessResidualObservable restart i ω).1 ∂ℙ :=
    ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      hpriorMeas hcurrentMeas.fst
        (hindependent.comp measurable_id measurable_fst)
  have hcurrentResidualIntegral :
      (∫⁻ ω, (stoppedSuccessResidualObservable restart i ω).2 ∂ℙ) =
        ∫⁻ ω in successEvent restart i,
          selectedStoppedResidual restart i ω ∂ℙ := by
    unfold stoppedSuccessResidualObservable
    exact lintegral_indicator₀ hsuccessNull.nullMeasurableSet _
  have hcurrentSuccessIntegral :
      (∫⁻ ω, (stoppedSuccessResidualObservable restart i ω).1 ∂ℙ) =
        ℙ (successEvent restart i) := by
    unfold stoppedSuccessResidualObservable
    exact lintegral_indicator_one₀ hsuccessNull.nullMeasurableSet
  have hmeasureFiber :
      ℙ {ω | firstAccepted restart ω = (i : ℕ∞)} =
        (∫⁻ ω, priorStoppedFailureWeight restart i ω ∂ℙ) *
          ℙ (successEvent restart i) := by
    calc
      ℙ {ω | firstAccepted restart ω = (i : ℕ∞)} =
          ∫⁻ ω, {ω | firstAccepted restart ω = (i : ℕ∞)}.indicator
            (fun _ ↦ (1 : ℝ≥0∞)) ω ∂ℙ :=
        (lintegral_indicator_one₀ hfiberNull.nullMeasurableSet).symm
      _ = ∫⁻ ω, priorStoppedFailureWeight restart i ω *
          (stoppedSuccessResidualObservable restart i ω).1 ∂ℙ := by
        apply lintegral_congr
        intro ω
        exact (priorStoppedFailureWeight_mul_success restart i ω).symm
      _ = (∫⁻ ω, priorStoppedFailureWeight restart i ω ∂ℙ) *
          ∫⁻ ω, (stoppedSuccessResidualObservable restart i ω).1 ∂ℙ :=
        hfactorSuccess
      _ = (∫⁻ ω, priorStoppedFailureWeight restart i ω ∂ℙ) *
          ℙ (successEvent restart i) := by
        rw [hcurrentSuccessIntegral]
  calc
    (∫⁻ ω in {ω | firstAccepted restart ω = (i : ℕ∞)},
      ENNReal.ofReal
        (KKT.residual f c (returnedPoint restart ω)
          (returnedMultiplier restart ω) ^ 2) ∂ℙ) =
        ∫⁻ ω, {ω | firstAccepted restart ω = (i : ℕ∞)}.indicator
          (fun ω ↦ ENNReal.ofReal
            (KKT.residual f c (returnedPoint restart ω)
              (returnedMultiplier restart ω) ^ 2)) ω ∂ℙ :=
      (lintegral_indicator₀ hfiberNull.nullMeasurableSet _).symm
    _ = ∫⁻ ω, priorStoppedFailureWeight restart i ω *
        (stoppedSuccessResidualObservable restart i ω).2 ∂ℙ := by
      apply lintegral_congr
      intro ω
      exact (priorStoppedFailureWeight_mul_residual restart i ω).symm
    _ = (∫⁻ ω, priorStoppedFailureWeight restart i ω ∂ℙ) *
        ∫⁻ ω, (stoppedSuccessResidualObservable restart i ω).2 ∂ℙ :=
      hfactorResidual
    _ = (∫⁻ ω, priorStoppedFailureWeight restart i ω ∂ℙ) *
        (∫⁻ ω in successEvent restart i,
          selectedStoppedResidual restart i ω ∂ℙ) := by
      rw [hcurrentResidualIntegral]
    _ ≤ (∫⁻ ω, priorStoppedFailureWeight restart i ω ∂ℙ) *
        (ℙ (successEvent restart i) * bound) :=
      mul_le_mul_right (hfixed i) _
    _ = ((∫⁻ ω, priorStoppedFailureWeight restart i ω ∂ℙ) *
        ℙ (successEvent restart i)) * bound :=
      (mul_assoc _ _ _).symm
    _ = ℙ {ω | firstAccepted restart ω = (i : ℕ∞)} * bound := by
      rw [← hmeasureFiber]

/-- Corollary 4.2: a uniform success-restricted integral bound passes through
the almost-surely terminating first-success mixture. -/
theorem stoppedResidualMeanSquare_le_of_successRestricted
    (hX : MeasurableSet X)
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (bound : ℝ≥0∞)
    (htermination : ∀ᵐ ω ∂ℙ, firstAccepted restart ω ≠ ⊤)
    (hsummaryMeas : ∀ i,
      AEMeasurable (stoppedSuccessResidualObservable restart i) ℙ)
    (hsummaryIndep : ProbabilityTheory.iIndepFun
      (fun i ↦ stoppedSuccessResidualObservable restart i) ℙ)
    (hfixed : ∀ i,
      (∫⁻ ω in successEvent restart i,
        selectedStoppedResidual restart i ω ∂ℙ) ≤
        ℙ (successEvent restart i) * bound) :
    stoppedResidualMeanSquare restart ≤ bound := by
  have hdisjoint : Pairwise fun i j : ℕ ↦
      Disjoint {ω | firstAccepted restart ω = (i : ℕ∞)}
        {ω | firstAccepted restart ω = (j : ℕ∞)} := by
    intro i j hij
    rw [Set.disjoint_left]
    intro ω hi hj
    apply hij
    apply ENat.coe_inj.mp
    exact hi.symm.trans hj
  have haedisjoint : Pairwise fun i j : ℕ ↦
      AEDisjoint ℙ {ω | firstAccepted restart ω = (i : ℕ∞)}
        {ω | firstAccepted restart ω = (j : ℕ∞)} :=
    hdisjoint.aedisjoint
  have hfiberMeas (i : ℕ) : MeasurableSet
      {ω | firstAccepted restart ω = (i : ℕ∞)} :=
    measurableSet_stoppedFirstAcceptedFiber hX restart i
  have hunionAE : ∀ᵐ ω ∂ℙ,
      ω ∈ ⋃ i : ℕ, {ω | firstAccepted restart ω = (i : ℕ∞)} := by
    filter_upwards [htermination] with ω hfinite
    obtain ⟨i, hi⟩ : ∃ i : ℕ, firstAccepted restart ω = (i : ℕ∞) := by
      cases hvalue : firstAccepted restart ω using ENat.recTopCoe with
      | top => exact False.elim (hfinite hvalue)
      | coe i => exact ⟨i, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hunionMeasure :
      ℙ (⋃ i : ℕ, {ω | firstAccepted restart ω = (i : ℕ∞)}) = 1 := by
    calc
      ℙ (⋃ i : ℕ, {ω | firstAccepted restart ω = (i : ℕ∞)}) =
          ℙ Set.univ := measure_congr (Filter.eventuallyEq_univ.mpr hunionAE)
      _ = 1 := measure_univ
  calc
    stoppedResidualMeanSquare restart =
        ∫⁻ ω, ENNReal.ofReal
          (KKT.residual f c (returnedPoint restart ω)
            (returnedMultiplier restart ω) ^ 2) ∂ℙ := by
      rw [stoppedResidualMeanSquare, KKT.Stochastic.residualMeanSquare_def]
    _ = ∫⁻ ω in ⋃ i : ℕ, {ω | firstAccepted restart ω = (i : ℕ∞)},
        ENNReal.ofReal
          (KKT.residual f c (returnedPoint restart ω)
            (returnedMultiplier restart ω) ^ 2) ∂ℙ := by
      rw [Measure.restrict_eq_self_of_ae_mem hunionAE]
    _ = ∑' i : ℕ,
        ∫⁻ ω in {ω | firstAccepted restart ω = (i : ℕ∞)},
          ENNReal.ofReal
            (KKT.residual f c (returnedPoint restart ω)
              (returnedMultiplier restart ω) ^ 2) ∂ℙ :=
      lintegral_iUnion₀ (fun i ↦ (hfiberMeas i).nullMeasurableSet)
        haedisjoint _
    _ ≤ ∑' i : ℕ,
        ℙ {ω | firstAccepted restart ω = (i : ℕ∞)} * bound :=
      ENNReal.tsum_le_tsum fun i ↦
        stoppedFirstAcceptedFiberResidual_le hX restart bound hsummaryMeas
          hsummaryIndep hfixed i
    _ = (∑' i : ℕ,
        ℙ {ω | firstAccepted restart ω = (i : ℕ∞)}) * bound :=
      ENNReal.tsum_mul_right
    _ = ℙ (⋃ i : ℕ,
        {ω | firstAccepted restart ω = (i : ℕ∞)}) * bound := by
      rw [measure_iUnion₀ haedisjoint
        (fun i ↦ (hfiberMeas i).nullMeasurableSet)]
    _ = 1 * bound := by rw [hunionMeasure]
    _ = bound := one_mul bound

namespace CertifiedStoppedSafeguardedRestart

/-- Corollary 4.2: almost-sure termination makes both components of the
returned stopped pair almost everywhere measurable. -/
theorem returnedPair_aemeasurable
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) :
    AEMeasurable (StoppedSafeguardedRestart.returnedPoint certified.restart) ℙ ∧
      AEMeasurable
        (StoppedSafeguardedRestart.returnedMultiplier certified.restart) ℙ := by
  have htermination := certified.terminatesAE confidence_pos confidence_lt_one hX
  exact ⟨returnedPoint_aemeasurable hX certified.restart htermination,
    returnedMultiplier_aemeasurable hX certified.restart htermination⟩

/-- Corollary 4.2: a certified stopped restart transfers a uniform finite
success-restricted integral bound to the residual of its first accepted pair. -/
theorem returnedResidualMeanSquare_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (bound : ℝ≥0∞)
    (hbound : ∀ i, (certified.certificate i).residualPerSuccessBound ≤ bound)
    (hX : MeasurableSet X) :
    KKT.Stochastic.residualMeanSquare ℙ f c
      (StoppedSafeguardedRestart.returnedPoint certified.restart)
      (StoppedSafeguardedRestart.returnedMultiplier certified.restart) ≤ bound := by
  have htermination := certified.terminatesAE confidence_pos confidence_lt_one hX
  have hsummaryMeas : ∀ i,
      AEMeasurable (stoppedSuccessResidualObservable certified.restart i) ℙ :=
    fun i ↦ certified_stoppedSuccessResidual_aemeasurable certified i
  have hsummaryIndep := certified_stoppedSuccessResidual_iIndep certified
  have hfixed : ∀ i,
      (∫⁻ ω in successEvent certified.restart i,
        selectedStoppedResidual certified.restart i ω ∂ℙ) ≤
      ℙ (successEvent certified.restart i) * bound := by
    intro i
    calc
      (∫⁻ ω in successEvent certified.restart i,
          selectedStoppedResidual certified.restart i ω ∂ℙ) =
          successRestrictedResidualNumerator
            (certified.restart.attempt i) hK :=
        successRestrictedSelectedResidual_eq_certificateNumerator certified i
      _ ≤ ℙ (StoppedAttemptAnalysis.successEvent
          (certified.restart.attempt i)) *
          (certified.certificate i).residualPerSuccessBound :=
        (certified.certificate i).successRestrictedResidual_le
      _ = ℙ (successEvent certified.restart i) *
          (certified.certificate i).residualPerSuccessBound := by
        rw [successEvent_eq_attempt_success certified.restart i,
          ← StoppedAttemptAnalysis.successEvent_eq_stoppedAttempt]
      _ ≤ ℙ (successEvent certified.restart i) * bound :=
        mul_le_mul_right (hbound i) _
  simpa only [stoppedResidualMeanSquare] using
    stoppedResidualMeanSquare_le_of_successRestricted hX certified.restart bound
      htermination hsummaryMeas hsummaryIndep hfixed

/-- Corollary 4.2: the source residual constant gives the advertised
`C_st / ((1 - confidence) * (K - 1))` target once each finite certificate
supplies that uniform aggregate success-restricted bound. -/
theorem returnedResidualMeanSquare_le_tex
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X)
    (hbound : ∀ i,
      (certified.certificate i).residualPerSuccessBound ≤
        ENNReal.ofReal
          (stochasticComplexityConstant h oracle params /
            ((1 - confidence) * ((K : ℝ) - 1)))) :
    KKT.Stochastic.residualMeanSquare ℙ f c
      (StoppedSafeguardedRestart.returnedPoint certified.restart)
      (StoppedSafeguardedRestart.returnedMultiplier certified.restart) ≤
        ENNReal.ofReal
          (stochasticComplexityConstant h oracle params /
            ((1 - confidence) * ((K : ℝ) - 1))) := by
  exact returnedResidualMeanSquare_le certified confidence_pos confidence_lt_one
    _ hbound hX

/-- Corollary 4.2: under the source iteration threshold, a certified stopped
restart returns a stochastic `ε`-KKT pair. -/
theorem isApproximatePair_of_iterationBound
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X)
    (ε : ℝ≥0) (ε_pos : 0 < ε)
    (hbound : ∀ i,
      (certified.certificate i).residualPerSuccessBound ≤
        ENNReal.ofReal
          (stochasticComplexityConstant h oracle params /
            ((1 - confidence) * ((K : ℝ) - 1))))
    (h_iterations : stochasticComplexityConstant h oracle params *
        (ε : ℝ)⁻¹ ^ 2 ≤
      (1 - confidence) * ((K : ℝ) - 1)) :
    KKT.Stochastic.IsApproximatePair ℙ f c ε
      (StoppedSafeguardedRestart.returnedPoint certified.restart)
      (StoppedSafeguardedRestart.returnedMultiplier certified.restart) := by
  have hmeas := returnedPair_aemeasurable certified confidence_pos
    confidence_lt_one hX
  have hepsilon : 0 < (ε : ℝ) := by
    exact_mod_cast ε_pos
  have hepsilonNe : (ε : ℝ) ≠ 0 := hepsilon.ne'
  have hKnat : 1 < K := by omega
  have hKreal : (1 : ℝ) < (K : ℝ) := by
    exact_mod_cast hKnat
  have hdenominator :
      0 < (1 - confidence) * ((K : ℝ) - 1) :=
    mul_pos (sub_pos.mpr confidence_lt_one) (sub_pos.mpr hKreal)
  have hrealRate :
      stochasticComplexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1)) ≤
        (ε : ℝ) ^ 2 := by
    apply (div_le_iff₀ hdenominator).2
    calc
      stochasticComplexityConstant h oracle params =
          (stochasticComplexityConstant h oracle params *
            (ε : ℝ)⁻¹ ^ 2) * (ε : ℝ) ^ 2 := by
        field_simp [hepsilonNe]
      _ ≤ ((1 - confidence) * ((K : ℝ) - 1)) * (ε : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h_iterations (sq_nonneg (ε : ℝ))
      _ = (ε : ℝ) ^ 2 *
          ((1 - confidence) * ((K : ℝ) - 1)) := by ring
  have hresidual :
      KKT.Stochastic.residualMeanSquare ℙ f c
          (StoppedSafeguardedRestart.returnedPoint certified.restart)
          (StoppedSafeguardedRestart.returnedMultiplier certified.restart) ≤
        (ε : ℝ≥0∞) ^ 2 := by
    calc
      KKT.Stochastic.residualMeanSquare ℙ f c
          (StoppedSafeguardedRestart.returnedPoint certified.restart)
          (StoppedSafeguardedRestart.returnedMultiplier certified.restart) ≤
          ENNReal.ofReal
            (stochasticComplexityConstant h oracle params /
              ((1 - confidence) * ((K : ℝ) - 1))) :=
        returnedResidualMeanSquare_le_tex certified confidence_pos
          confidence_lt_one hX hbound
      _ ≤ ENNReal.ofReal ((ε : ℝ) ^ 2) :=
        ENNReal.ofReal_le_ofReal hrealRate
      _ = (ε : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_pow (NNReal.coe_nonneg ε),
          ENNReal.ofReal_coe_nnreal]
  exact KKT.Stochastic.IsApproximatePair.of_residualMeanSquare_le
    hmeas.1 hmeas.2 hresidual

end CertifiedStoppedSafeguardedRestart

end LALM.Correction

end
