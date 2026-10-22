/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCertifiedRestart
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedCertifiedRestart

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

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
variable {X : Set (EuclideanSpace ℝ (Fin n))} {hK : 2 ≤ K}

open StoppedAttemptAnalysis
open StoppedSafeguardedRestart

/-- Helper for Corollary 3.8: the finite output record pairs a natural-valued
uniform selector with the observable finite stopped attempt. -/
abbrev finiteStoppedOutputRecordType
    (Ξ : Type u) (n m K : ℕ) :=
  ℕ × stoppedAttemptFiniteObservableType Ξ n m K

/-- Helper for Corollary 3.8: successful output records have a supported
selector and a successful finite stopped path. -/
def successfulFiniteStoppedOutputRecord
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    Set (finiteStoppedOutputRecordType Ξ n m K) :=
  {record | record.1 ∈ Finset.Icc 1 (K - 1) ∧
    record.2 ∈ successRecord (Ξ := Ξ) (n := n) (m := m) K X}

/-- Helper for Corollary 3.8: the successful finite output-record set is
measurable. -/
theorem measurableSet_successfulFiniteStoppedOutputRecord
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) :
    MeasurableSet
      (successfulFiniteStoppedOutputRecord
        (Ξ := Ξ) (n := n) (m := m) K X) := by
  unfold successfulFiniteStoppedOutputRecord
  have hleft : MeasurableSet
      {record : finiteStoppedOutputRecordType Ξ n m K |
        record.1 ∈ (Finset.Icc 1 (K - 1) : Finset ℕ)} :=
    (Finset.Icc 1 (K - 1)).measurableSet.preimage
      (measurable_fst : Measurable
        (fun record : finiteStoppedOutputRecordType Ξ n m K ↦ record.1))
  have hright : MeasurableSet
      {record : finiteStoppedOutputRecordType Ξ n m K |
        record.2 ∈ successRecord (Ξ := Ξ) (n := n) (m := m) K X} :=
    (measurableSet_successRecord
      (Ξ := Ξ) (n := n) (m := m) K X hX).preimage
      (measurable_snd : Measurable
        (fun record : finiteStoppedOutputRecordType Ξ n m K ↦ record.2))
  exact hleft.inter hright

/-- Helper for Corollary 3.8: the reference law of one finite output record is
the uniform selector law times the pushed-forward stopped-attempt law. -/
noncomputable def finiteStoppedOutputRecordMeasure
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K) : Measure (finiteStoppedOutputRecordType Ξ n m K) :=
  (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure.prod
    (P.map (stoppedAttemptFiniteObservable attempt))

/-- Helper for Corollary 3.8: evaluate the primal coordinate selected by a
finite output record. -/
def finiteStoppedOutputRecordPoint
    (record : finiteStoppedOutputRecordType Ξ n m K) :
    EuclideanSpace ℝ (Fin n) :=
  record.2.2.1 (Fin.ofNat (K + 1) (record.1 + 1))

/-- Helper for Corollary 3.8: evaluate the multiplier coordinate selected by a
finite output record. -/
def finiteStoppedOutputRecordMultiplier
    (record : finiteStoppedOutputRecordType Ξ n m K) :
    EuclideanSpace ℝ (Fin m) :=
  record.2.2.2.1 (Fin.ofNat (K + 1) (record.1 + 1))

/-- Helper for Corollary 3.8: the record residual is restricted to successful
records and uses the globally measurable regularity-region extension. -/
noncomputable def finiteStoppedOutputResidualIntegrand
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (record : finiteStoppedOutputRecordType Ξ n m K) : ℝ≥0∞ :=
  (successfulFiniteStoppedOutputRecord
      (Ξ := Ξ) (n := n) (m := m) K X).indicator
    (fun record ↦ ENNReal.ofReal
      (KKT.residualExtension h
        (finiteStoppedOutputRecordPoint record,
          finiteStoppedOutputRecordMultiplier record) ^ 2)) record

/-- Helper for Corollary 3.8: the finite output-record primal evaluator is
measurable. -/
theorem measurable_finiteStoppedOutputRecordPoint :
    Measurable
      (finiteStoppedOutputRecordPoint (Ξ := Ξ) (n := n) (m := m) (K := K)) := by
  let pointProjection : stoppedAttemptFiniteObservableType Ξ n m K →
      Fin (K + 1) → EuclideanSpace ℝ (Fin n) :=
    fun record ↦ record.2.1
  have hpointProjection : Measurable pointProjection :=
    measurable_fst.comp measurable_snd
  let pointAt : ℕ → stoppedAttemptFiniteObservableType Ξ n m K →
      EuclideanSpace ℝ (Fin n) :=
    fun k record ↦ pointProjection record (Fin.ofNat (K + 1) (k + 1))
  have hpointAt (k : ℕ) : Measurable (pointAt k) :=
    (measurable_pi_apply (Fin.ofNat (K + 1) (k + 1))).comp hpointProjection
  change Measurable (fun record :
    ℕ × stoppedAttemptFiniteObservableType Ξ n m K ↦
      record.2.2.1 (Fin.ofNat (K + 1) (record.1 + 1)))
  simpa only [pointAt, pointProjection] using
    measurable_from_prod_countable_right hpointAt

/-- Helper for Corollary 3.8: the finite output-record multiplier evaluator is
measurable. -/
theorem measurable_finiteStoppedOutputRecordMultiplier :
    Measurable (finiteStoppedOutputRecordMultiplier
      (Ξ := Ξ) (n := n) (m := m) (K := K)) := by
  let multiplierProjection : stoppedAttemptFiniteObservableType Ξ n m K →
      Fin (K + 1) → EuclideanSpace ℝ (Fin m) :=
    fun record ↦ record.2.2.1
  have hmultiplierProjection : Measurable multiplierProjection :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  let multiplierAt : ℕ → stoppedAttemptFiniteObservableType Ξ n m K →
      EuclideanSpace ℝ (Fin m) :=
    fun k record ↦
      multiplierProjection record (Fin.ofNat (K + 1) (k + 1))
  have hmultiplierAt (k : ℕ) : Measurable (multiplierAt k) :=
    (measurable_pi_apply (Fin.ofNat (K + 1) (k + 1))).comp
      hmultiplierProjection
  change Measurable (fun record :
    ℕ × stoppedAttemptFiniteObservableType Ξ n m K ↦
      record.2.2.2.1 (Fin.ofNat (K + 1) (record.1 + 1)))
  simpa only [multiplierAt, multiplierProjection] using
    measurable_from_prod_countable_right hmultiplierAt

/-- Helper for Corollary 3.8: the finite successful-record residual integrand
is measurable. -/
theorem measurable_finiteStoppedOutputResidualIntegrand
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) :
    Measurable (finiteStoppedOutputResidualIntegrand
      (Ξ := Ξ) (m := m) (h := h) K X) := by
  have hpoint : Measurable
      (finiteStoppedOutputRecordPoint (Ξ := Ξ) (n := n) (m := m) (K := K)) :=
    measurable_finiteStoppedOutputRecordPoint
  have hmultiplier : Measurable
      (finiteStoppedOutputRecordMultiplier
        (Ξ := Ξ) (n := n) (m := m) (K := K)) :=
    measurable_finiteStoppedOutputRecordMultiplier
  have hresidual := (KKT.measurable_residualExtension h).comp
    (hpoint.prodMk hmultiplier)
  unfold finiteStoppedOutputResidualIntegrand
  exact (hresidual.pow_const 2).ennreal_ofReal.indicator
    (measurableSet_successfulFiniteStoppedOutputRecord K X hX)

/-- Helper for Corollary 3.8: mapping the right coordinate of a product
measure commutes with a measurable nonnegative integral. -/
theorem lintegral_prod_map_right
    {E : Type*} [MeasurableSpace E]
    (mu : Measure ℕ) (g : Ω → E) (hg : Measurable g)
    (F : ℕ × E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂mu.prod (P.map g)) =
      ∫⁻ z, F (z.1, g z.2) ∂mu.prod P := by
  have hsection (k : ℕ) :
      AEMeasurable (fun y : E ↦ F (k, y)) (P.map g) :=
    (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hcomposedSection (k : ℕ) :
      Measurable (fun omega ↦ F (k, g omega)) :=
    hF.comp (measurable_const.prodMk hg)
  have hcomposed : Measurable (fun z : ℕ × Ω ↦ F (z.1, g z.2)) :=
    measurable_from_prod_countable_right hcomposedSection
  calc
    (∫⁻ z, F z ∂mu.prod (P.map g)) =
        ∫⁻ k, ∫⁻ y, F (k, y) ∂P.map g ∂mu :=
      lintegral_prod F hF.aemeasurable
    _ = ∫⁻ k, ∫⁻ omega, F (k, g omega) ∂P ∂mu := by
      apply lintegral_congr
      intro k
      exact lintegral_map' (hsection k) hg.aemeasurable
    _ = ∫⁻ z, F (z.1, g z.2) ∂mu.prod P :=
      (lintegral_prod _ hcomposed.aemeasurable).symm

/-- Helper for Corollary 3.8: a supported finite record coordinate agrees
with the canonical natural-index primal adapter. -/
theorem finiteStoppedOutputRecord_point_eq
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (k : ℕ) (hk : k ≤ K) (omega : Ω) :
    (stoppedAttemptFiniteObservable attempt omega).2.1
        (Fin.ofNat (K + 1) k) =
      canonicalPointNat attempt k omega := by
  have hfin : (Fin.ofNat (K + 1) k) =
      (⟨k, Nat.lt_succ_iff.mpr hk⟩ : Fin (K + 1)) := by
    apply Fin.ext
    simp only [Fin.ofNat_eq_cast, Fin.val_natCast]
    exact Nat.mod_eq_of_lt (Nat.lt_succ_iff.mpr hk)
  rw [stoppedAttemptFiniteObservable_point, hfin]
  exact (canonicalPointNat_eq_point attempt k hk omega).symm

/-- Helper for Corollary 3.8: a supported finite record coordinate agrees
with the canonical natural-index multiplier adapter. -/
theorem finiteStoppedOutputRecord_multiplier_eq
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (k : ℕ) (hk : k ≤ K) (omega : Ω) :
    (stoppedAttemptFiniteObservable attempt omega).2.2.1
        (Fin.ofNat (K + 1) k) =
      canonicalMultiplierNat attempt k omega := by
  have hfin : (Fin.ofNat (K + 1) k) =
      (⟨k, Nat.lt_succ_iff.mpr hk⟩ : Fin (K + 1)) := by
    apply Fin.ext
    simp only [Fin.ofNat_eq_cast, Fin.val_natCast]
    exact Nat.mod_eq_of_lt (Nat.lt_succ_iff.mpr hk)
  rw [stoppedAttemptFiniteObservable_multiplier, hfin]
  exact (canonicalMultiplierNat_eq_multiplier attempt k hk omega).symm

/-- Helper for Corollary 3.8: after pushing the stopped-attempt coordinate
back to the original probability space, the record integrand is the canonical
success-restricted uniform-output residual. -/
theorem finiteStoppedOutputResidualIntegrand_eq
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K) :
    (fun output : ℕ × Ω ↦ finiteStoppedOutputResidualIntegrand
      (h := h) K X
      (output.1, stoppedAttemptFiniteObservable attempt output.2)) =ᵐ[
        LALM.StochasticRun.UniformOutput.measure K hK P]
      fun output ↦
        (Set.univ ×ˢ attempt.successEvent).indicator
          (fun output ↦ ENNReal.ofReal
            (KKT.residual f c
              (canonicalPointNat attempt (output.1 + 1) output.2)
              (canonicalMultiplierNat attempt (output.1 + 1) output.2) ^ 2))
          output := by
  let p := LALM.StochasticRun.UniformOutput.indexLaw K hK
  have hpSupport : ∀ᵐ k ∂p.toMeasure, k ∈ Finset.Icc 1 (K - 1) := by
    rw [ae_iff_of_countable]
    intro k hkMeasure
    by_contra hk
    have hpZero : p k = 0 := by
      simp only [p, LALM.StochasticRun.UniformOutput.indexLaw,
        PMF.uniformOfFinset_apply, if_neg hk]
    have hsingleton : p.toMeasure {k} = p k :=
      PMF.toMeasure_apply_singleton p k (MeasurableSet.singleton k)
    exact hkMeasure (hsingleton.trans hpZero)
  have hpSupportLifted : ∀ᵐ output ∂p.toMeasure.prod P,
      output.1 ∈ Finset.Icc 1 (K - 1) :=
    (Measure.quasiMeasurePreserving_fst (μ := p.toMeasure) (ν := P)).ae
      hpSupport
  change _ =ᵐ[p.toMeasure.prod P] _
  filter_upwards [hpSupportLifted] with output hindex
  let i := output.1
  let omega := output.2
  let record : finiteStoppedOutputRecordType Ξ n m K :=
    (i, stoppedAttemptFiniteObservable attempt omega)
  change finiteStoppedOutputResidualIntegrand (h := h) K X record = _
  have hiBounds : i ∈ Finset.Icc 1 (K - 1) := hindex
  have hi := Finset.mem_Icc.mp hiBounds
  have hiSuccLe : i + 1 ≤ K := by omega
  have hsuccessRecord :
      record ∈ successfulFiniteStoppedOutputRecord
          (Ξ := Ξ) (n := n) (m := m) K X ↔
        omega ∈ attempt.successEvent := by
    change (i ∈ Finset.Icc 1 (K - 1) ∧
      stoppedAttemptFiniteObservable attempt omega ∈
        successRecord (Ξ := Ξ) (n := n) (m := m) K X) ↔ _
    rw [stoppedAttemptFiniteObservable_mem_successRecord_iff]
    exact and_iff_right hiBounds
  by_cases hsuccess : omega ∈ attempt.successEvent
  · have hrecord : record ∈ successfulFiniteStoppedOutputRecord
        (Ξ := Ξ) (n := n) (m := m) K X :=
      hsuccessRecord.mpr hsuccess
    have hpointX : canonicalPointNat attempt (i + 1) omega ∈ X := by
      rw [canonicalPointNat_eq_point attempt (i + 1) hiSuccLe omega]
      let k : Fin K := ⟨i, by omega⟩
      have hmem := (attempt.mem_successEvent_iff_points_mem omega).mp hsuccess k
      have hendpoint :
          (⟨i + 1, Nat.lt_succ_iff.mpr hiSuccLe⟩ : Fin (K + 1)) =
            k.succ := by
        apply Fin.ext
        rfl
      rwa [hendpoint]
    have hpointRegion :
        canonicalPointNat attempt (i + 1) omega ∈ h.region :=
      attempt.region_condition.thickening_subset
        (Metric.self_subset_cthickening X hpointX)
    have hextension := KKT.residualExtension_eq h
      (z := (canonicalPointNat attempt (i + 1) omega,
        canonicalMultiplierNat attempt (i + 1) omega)) hpointRegion
    have hproduct : output ∈ Set.univ ×ˢ attempt.successEvent :=
      ⟨Set.mem_univ _, hsuccess⟩
    unfold finiteStoppedOutputResidualIntegrand
    rw [Set.indicator_of_mem hrecord, Set.indicator_of_mem hproduct]
    change ENNReal.ofReal
        (KKT.residualExtension h
          ((stoppedAttemptFiniteObservable attempt omega).2.1
              (Fin.ofNat (K + 1) (i + 1)),
            (stoppedAttemptFiniteObservable attempt omega).2.2.1
              (Fin.ofNat (K + 1) (i + 1))) ^ 2) = _
    rw [finiteStoppedOutputRecord_point_eq attempt (i + 1) hiSuccLe omega,
      finiteStoppedOutputRecord_multiplier_eq attempt (i + 1) hiSuccLe omega,
      hextension]
  · have hrecord : record ∉ successfulFiniteStoppedOutputRecord
        (Ξ := Ξ) (n := n) (m := m) K X :=
      fun hrecord ↦ hsuccess (hsuccessRecord.mp hrecord)
    have hproduct : output ∉ Set.univ ×ˢ attempt.successEvent :=
      fun houtput ↦ hsuccess houtput.2
    unfold finiteStoppedOutputResidualIntegrand
    rw [Set.indicator_of_notMem hrecord, Set.indicator_of_notMem hproduct]

/-- Corollary 3.8: the finite record-law residual integral is exactly the
canonical independent-uniform success-restricted numerator. -/
theorem finiteStoppedOutputRecordIntegral_eq_canonicalNumerator
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K) :
    (∫⁻ record, finiteStoppedOutputResidualIntegrand (h := h) K X record
        ∂finiteStoppedOutputRecordMeasure attempt hK) =
      canonicalUniformSuccessResidualNumerator attempt hK := by
  let observable := stoppedAttemptFiniteObservable attempt
  let muIndex :=
    (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure
  have hobservable : Measurable observable :=
    measurable_stoppedAttemptFiniteObservable attempt
  have hX : MeasurableSet X := attempt.measurableSet_localization
  have hintegrand : Measurable
      (finiteStoppedOutputResidualIntegrand (Ξ := Ξ) (m := m) (h := h) K X) :=
    measurable_finiteStoppedOutputResidualIntegrand
      (Ξ := Ξ) (m := m) (h := h) K X hX
  have hsuccess : NullMeasurableSet
      (Set.univ ×ˢ attempt.successEvent) (muIndex.prod P) :=
    MeasurableSet.univ.nullMeasurableSet.prod
      attempt.measurableSet_successEvent.nullMeasurableSet
  calc
    (∫⁻ record, finiteStoppedOutputResidualIntegrand (h := h) K X record
        ∂finiteStoppedOutputRecordMeasure attempt hK) =
        ∫⁻ output, finiteStoppedOutputResidualIntegrand (h := h) K X
          (output.1, observable output.2) ∂muIndex.prod P := by
      exact lintegral_prod_map_right (P := P) muIndex observable hobservable
        (finiteStoppedOutputResidualIntegrand (h := h) K X) hintegrand
    _ = ∫⁻ output,
        (Set.univ ×ˢ attempt.successEvent).indicator
          (fun output ↦ ENNReal.ofReal
            (KKT.residual f c
              (canonicalPointNat attempt (output.1 + 1) output.2)
              (canonicalMultiplierNat attempt (output.1 + 1) output.2) ^ 2))
          output ∂muIndex.prod P := by
      exact lintegral_congr_ae
        (finiteStoppedOutputResidualIntegrand_eq attempt hK)
    _ = ∫⁻ output in Set.univ ×ˢ attempt.successEvent,
        ENNReal.ofReal
          (KKT.residual f c
            (canonicalPointNat attempt (output.1 + 1) output.2)
            (canonicalMultiplierNat attempt (output.1 + 1) output.2) ^ 2)
          ∂muIndex.prod P := by
      exact lintegral_indicator₀ hsuccess _
    _ = canonicalUniformSuccessResidualNumerator attempt hK := by
      rfl

/-- Corollary 3.8: the actual selector paired with its finite stopped-attempt
observable. -/
noncomputable def finiteStoppedOutputJoint
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) : finiteStoppedOutputRecordType Ξ n m K :=
  (restart.outputIndex i omega,
    stoppedAttemptFiniteObservable (restart.attempt i) omega)

/-- Helper for Corollary 3.8: the actual selector-record pair has the finite
reference product law. -/
theorem hasLaw_finiteStoppedOutputJoint
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : ProbabilityTheory.HasLaw (finiteStoppedOutputJoint restart i)
      (finiteStoppedOutputRecordMeasure (restart.attempt i) hK) P := by
  let observable := fun omega ↦
    stoppedAttemptFiniteObservable (restart.attempt i) omega
  have hobservable : Measurable observable :=
    measurable_stoppedAttemptFiniteObservable (restart.attempt i)
  have hobservableLaw : ProbabilityTheory.HasLaw observable
      (P.map observable) P :=
    ⟨hobservable.aemeasurable, rfl⟩
  have hjointLaw := (restart.outputIndex_indep_attempt i).hasLaw_prod
    (restart.outputIndex_hasLaw i) hobservableLaw
  change ProbabilityTheory.HasLaw
    (fun omega ↦ (restart.outputIndex i omega, observable omega)) _ P
  exact hjointLaw

/- The selected point and multiplier are exposed separately from the residual
integrand so the final approximate-pair theorem can use their measurable
interfaces. -/

/-- Corollary 3.8: the primal point selected from one finite stopped attempt. -/
noncomputable def selectedFiniteStoppedPoint
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) : EuclideanSpace ℝ (Fin n) :=
  canonicalPointNat (restart.attempt i)
    (restart.outputIndex i omega + 1) omega

/-- Corollary 3.8: the multiplier selected from one finite stopped attempt. -/
noncomputable def selectedFiniteStoppedMultiplier
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) : EuclideanSpace ℝ (Fin m) :=
  canonicalMultiplierNat (restart.attempt i)
    (restart.outputIndex i omega + 1) omega

/-- Helper for Corollary 3.8: the record primal evaluator agrees almost surely
with the selected finite stopped primal point. -/
theorem finiteStoppedOutputRecordPoint_actual
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun omega ↦ finiteStoppedOutputRecordPoint
      (finiteStoppedOutputJoint restart i omega)) =ᵐ[P]
      selectedFiniteStoppedPoint restart i := by
  filter_upwards [ae_outputIndex_mem_uniformRange restart i] with omega hindex
  have hbounds := Finset.mem_Icc.mp hindex
  have hselectedLe : restart.outputIndex i omega + 1 ≤ K := by omega
  change (stoppedAttemptFiniteObservable (restart.attempt i) omega).2.1
      (Fin.ofNat (K + 1) (restart.outputIndex i omega + 1)) =
    canonicalPointNat (restart.attempt i)
      (restart.outputIndex i omega + 1) omega
  exact finiteStoppedOutputRecord_point_eq (restart.attempt i)
    (restart.outputIndex i omega + 1) hselectedLe omega

/-- Helper for Corollary 3.8: the record multiplier evaluator agrees almost
surely with the selected finite stopped multiplier. -/
theorem finiteStoppedOutputRecordMultiplier_actual
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun omega ↦ finiteStoppedOutputRecordMultiplier
      (finiteStoppedOutputJoint restart i omega)) =ᵐ[P]
      selectedFiniteStoppedMultiplier restart i := by
  filter_upwards [ae_outputIndex_mem_uniformRange restart i] with omega hindex
  have hbounds := Finset.mem_Icc.mp hindex
  have hselectedLe : restart.outputIndex i omega + 1 ≤ K := by omega
  change (stoppedAttemptFiniteObservable (restart.attempt i) omega).2.2.1
      (Fin.ofNat (K + 1) (restart.outputIndex i omega + 1)) =
    canonicalMultiplierNat (restart.attempt i)
      (restart.outputIndex i omega + 1) omega
  exact finiteStoppedOutputRecord_multiplier_eq (restart.attempt i)
    (restart.outputIndex i omega + 1) hselectedLe omega

/-- Corollary 3.8: the selected finite stopped primal point is almost
everywhere measurable. -/
theorem selectedFiniteStoppedPoint_aemeasurable
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : AEMeasurable (selectedFiniteStoppedPoint restart i) P := by
  have hjoint := hasLaw_finiteStoppedOutputJoint restart i
  have hcomp : AEMeasurable
      (fun omega ↦ finiteStoppedOutputRecordPoint
        (finiteStoppedOutputJoint restart i omega)) P :=
    measurable_finiteStoppedOutputRecordPoint.comp_aemeasurable
      hjoint.aemeasurable
  exact hcomp.congr (finiteStoppedOutputRecordPoint_actual restart i)

/-- Corollary 3.8: the selected finite stopped multiplier is almost
everywhere measurable. -/
theorem selectedFiniteStoppedMultiplier_aemeasurable
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : AEMeasurable (selectedFiniteStoppedMultiplier restart i) P := by
  have hjoint := hasLaw_finiteStoppedOutputJoint restart i
  have hcomp : AEMeasurable
      (fun omega ↦ finiteStoppedOutputRecordMultiplier
        (finiteStoppedOutputJoint restart i omega)) P :=
    measurable_finiteStoppedOutputRecordMultiplier.comp_aemeasurable
      hjoint.aemeasurable
  exact hcomp.congr (finiteStoppedOutputRecordMultiplier_actual restart i)

/-- Corollary 3.8: the squared residual selected from one finite stopped
restart attempt. -/
noncomputable def selectedFiniteStoppedResidual
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal
    (KKT.residual f c
      (canonicalPointNat (restart.attempt i)
        (restart.outputIndex i omega + 1) omega)
      (canonicalMultiplierNat (restart.attempt i)
        (restart.outputIndex i omega + 1) omega) ^ 2)

/-- Helper for Corollary 3.8: evaluating the finite record integrand on an
actual selector-attempt pair gives the success-restricted selected residual
almost surely. -/
theorem finiteStoppedOutputResidualIntegrand_actual
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun omega ↦ finiteStoppedOutputResidualIntegrand (h := h) K X
        (finiteStoppedOutputJoint restart i omega)) =ᵐ[P]
      fun omega ↦ (successEvent restart i).indicator
        (selectedFiniteStoppedResidual restart i) omega := by
  filter_upwards [ae_outputIndex_mem_uniformRange restart i] with omega hindex
  have hbounds := Finset.mem_Icc.mp hindex
  have hselectedLe : restart.outputIndex i omega + 1 ≤ K := by omega
  have hrecordSuccess : finiteStoppedOutputJoint restart i omega ∈
        successfulFiniteStoppedOutputRecord
          (Ξ := Ξ) (n := n) (m := m) K X ↔
      omega ∈ successEvent restart i := by
    change (restart.outputIndex i omega ∈ Finset.Icc 1 (K - 1) ∧
      stoppedAttemptFiniteObservable (restart.attempt i) omega ∈
        successRecord (Ξ := Ξ) (n := n) (m := m) K X) ↔ _
    rw [stoppedAttemptFiniteObservable_mem_successRecord_iff]
    exact and_iff_right hindex
  by_cases hsuccess : omega ∈ successEvent restart i
  · have hrecord := hrecordSuccess.mpr hsuccess
    have hpointX : canonicalPointNat (restart.attempt i)
        (restart.outputIndex i omega + 1) omega ∈ X := by
      rw [canonicalPointNat_eq_point (restart.attempt i)
        (restart.outputIndex i omega + 1) hselectedLe omega]
      let k : Fin K := ⟨restart.outputIndex i omega, by omega⟩
      have hmem := ((restart.attempt i).mem_successEvent_iff_points_mem omega).mp
        hsuccess k
      have hendpoint :
          (⟨restart.outputIndex i omega + 1,
            Nat.lt_succ_iff.mpr hselectedLe⟩ : Fin (K + 1)) = k.succ := by
        apply Fin.ext
        rfl
      rwa [hendpoint]
    have hpointRegion : canonicalPointNat (restart.attempt i)
        (restart.outputIndex i omega + 1) omega ∈ h.region :=
      (restart.attempt i).region_condition.thickening_subset
        (Metric.self_subset_cthickening X hpointX)
    have hextension := KKT.residualExtension_eq h
      (z := (canonicalPointNat (restart.attempt i)
          (restart.outputIndex i omega + 1) omega,
        canonicalMultiplierNat (restart.attempt i)
          (restart.outputIndex i omega + 1) omega)) hpointRegion
    unfold finiteStoppedOutputResidualIntegrand
    rw [Set.indicator_of_mem hrecord, Set.indicator_of_mem hsuccess]
    change ENNReal.ofReal
        (KKT.residualExtension h
          ((stoppedAttemptFiniteObservable (restart.attempt i) omega).2.1
              (Fin.ofNat (K + 1) (restart.outputIndex i omega + 1)),
            (stoppedAttemptFiniteObservable (restart.attempt i) omega).2.2.1
              (Fin.ofNat (K + 1) (restart.outputIndex i omega + 1))) ^ 2) = _
    rw [finiteStoppedOutputRecord_point_eq (restart.attempt i)
        (restart.outputIndex i omega + 1) hselectedLe omega,
      finiteStoppedOutputRecord_multiplier_eq (restart.attempt i)
        (restart.outputIndex i omega + 1) hselectedLe omega,
      hextension]
    rfl
  · have hrecord : finiteStoppedOutputJoint restart i omega ∉
        successfulFiniteStoppedOutputRecord
          (Ξ := Ξ) (n := n) (m := m) K X :=
      fun hrecord ↦ hsuccess (hrecordSuccess.mp hrecord)
    unfold finiteStoppedOutputResidualIntegrand
    rw [Set.indicator_of_notMem hrecord, Set.indicator_of_notMem hsuccess]

/-- Corollary 3.8: the actual success-restricted selected residual integral is
exactly the canonical product-law numerator. -/
theorem successRestrictedSelectedFiniteStoppedResidual_eq_canonicalNumerator
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (∫⁻ omega in successEvent restart i,
      selectedFiniteStoppedResidual restart i omega ∂P) =
      canonicalUniformSuccessResidualNumerator (restart.attempt i) hK := by
  have hsuccess : MeasurableSet (successEvent restart i) :=
    measurableSet_successEvent restart i
  have hjoint := hasLaw_finiteStoppedOutputJoint restart i
  have hintegrand := measurable_finiteStoppedOutputResidualIntegrand
    (Ξ := Ξ) (m := m) (h := h) K X
    (restart.attempt i).measurableSet_localization
  calc
    (∫⁻ omega in successEvent restart i,
        selectedFiniteStoppedResidual restart i omega ∂P) =
        ∫⁻ omega, (successEvent restart i).indicator
          (selectedFiniteStoppedResidual restart i) omega ∂P :=
      (lintegral_indicator₀ hsuccess.nullMeasurableSet _).symm
    _ = ∫⁻ omega, finiteStoppedOutputResidualIntegrand (h := h) K X
        (finiteStoppedOutputJoint restart i omega) ∂P := by
      exact lintegral_congr_ae
        (finiteStoppedOutputResidualIntegrand_actual restart i).symm
    _ = ∫⁻ record, finiteStoppedOutputResidualIntegrand (h := h) K X record
        ∂finiteStoppedOutputRecordMeasure (restart.attempt i) hK :=
      hjoint.lintegral_comp hintegrand.aemeasurable
    _ = canonicalUniformSuccessResidualNumerator (restart.attempt i) hK :=
      finiteStoppedOutputRecordIntegral_eq_canonicalNumerator
        (restart.attempt i) hK

/-- Corollary 3.8: the success weight and restricted selected residual of one
finite stopped restart attempt. -/
noncomputable def finiteStoppedSuccessResidualObservable
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) : ℝ≥0∞ × ℝ≥0∞ :=
  ((successEvent restart i).indicator (fun _ ↦ 1) omega,
    (successEvent restart i).indicator
      (selectedFiniteStoppedResidual restart i) omega)

/-- Helper for Corollary 3.8: summarize success and residual as a measurable
function of one finite output record. -/
noncomputable def finiteStoppedOutputRecordSummary
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (record : finiteStoppedOutputRecordType Ξ n m K) : ℝ≥0∞ × ℝ≥0∞ :=
  ((successfulFiniteStoppedOutputRecord
      (Ξ := Ξ) (n := n) (m := m) K X).indicator (fun _ ↦ 1) record,
    finiteStoppedOutputResidualIntegrand (h := h) K X record)

/-- Helper for Corollary 3.8: the record summary agrees almost surely with the
actual success/residual observable. -/
theorem finiteStoppedOutputRecordSummary_actual
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    (fun omega ↦ finiteStoppedOutputRecordSummary (h := h) K X
      (finiteStoppedOutputJoint restart i omega)) =ᵐ[P]
        finiteStoppedSuccessResidualObservable restart i := by
  filter_upwards [ae_outputIndex_mem_uniformRange restart i,
    finiteStoppedOutputResidualIntegrand_actual restart i] with
      omega hindex hresidual
  have hrecordSuccess : finiteStoppedOutputJoint restart i omega ∈
        successfulFiniteStoppedOutputRecord
          (Ξ := Ξ) (n := n) (m := m) K X ↔
      omega ∈ successEvent restart i := by
    change (restart.outputIndex i omega ∈ Finset.Icc 1 (K - 1) ∧
      stoppedAttemptFiniteObservable (restart.attempt i) omega ∈
        successRecord (Ξ := Ξ) (n := n) (m := m) K X) ↔ _
    rw [stoppedAttemptFiniteObservable_mem_successRecord_iff]
    exact and_iff_right hindex
  unfold finiteStoppedOutputRecordSummary finiteStoppedSuccessResidualObservable
  apply Prod.ext
  · by_cases hsuccess : omega ∈ successEvent restart i
    · rw [Set.indicator_of_mem (hrecordSuccess.mpr hsuccess),
        Set.indicator_of_mem hsuccess]
    · rw [Set.indicator_of_notMem
          (fun hrecord ↦ hsuccess (hrecordSuccess.mp hrecord)),
        Set.indicator_of_notMem hsuccess]
  · exact hresidual

/-- Helper for Corollary 3.8: the finite record summary is measurable. -/
theorem measurable_finiteStoppedOutputRecordSummary
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) :
    Measurable (finiteStoppedOutputRecordSummary
      (Ξ := Ξ) (m := m) (h := h) K X) :=
  (measurable_const.indicator
      (measurableSet_successfulFiniteStoppedOutputRecord K X hX)).prodMk
    (measurable_finiteStoppedOutputResidualIntegrand K X hX)

/-- Corollary 3.8: each actual finite stopped success/residual observable is
almost everywhere measurable. -/
theorem finiteStoppedSuccessResidualObservable_aemeasurable
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    AEMeasurable (finiteStoppedSuccessResidualObservable restart i) P := by
  have hjoint := hasLaw_finiteStoppedOutputJoint restart i
  have hsummary := measurable_finiteStoppedOutputRecordSummary
    (Ξ := Ξ) (m := m) (h := h) K X
    (restart.attempt i).measurableSet_localization
  have hcomp : AEMeasurable
      (fun omega ↦ finiteStoppedOutputRecordSummary (h := h) K X
        (finiteStoppedOutputJoint restart i omega)) P :=
    hsummary.comp_aemeasurable hjoint.aemeasurable
  exact hcomp.congr (finiteStoppedOutputRecordSummary_actual restart i)

/-- Corollary 3.8: mutually independent finite attempt records induce
mutually independent success/residual observables. -/
theorem finiteStoppedSuccessResidualObservable_iIndep
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) :
    ProbabilityTheory.iIndepFun
      (fun i ↦ finiteStoppedSuccessResidualObservable restart i) P := by
  let joint : ℕ → Ω → finiteStoppedOutputRecordType Ξ n m K :=
    fun i ↦ finiteStoppedOutputJoint restart i
  let summary : ℕ → finiteStoppedOutputRecordType Ξ n m K →
      ℝ≥0∞ × ℝ≥0∞ :=
    fun _i ↦ finiteStoppedOutputRecordSummary (h := h) K X
  have hjoint : ∀ i, AEMeasurable (joint i) P := by
    intro i
    exact (hasLaw_finiteStoppedOutputJoint restart i).aemeasurable
  have hsummary : ∀ i, AEMeasurable (summary i) (P.map (joint i)) := by
    intro i
    exact (measurable_finiteStoppedOutputRecordSummary
      (Ξ := Ξ) (m := m) (h := h) K X
      (restart.attempt i).measurableSet_localization).aemeasurable
  have hrecord := restart.independent_attempt.comp₀ summary hjoint hsummary
  have hactual : ∀ i, (summary i ∘ joint i) =ᵐ[P]
      finiteStoppedSuccessResidualObservable restart i := by
    intro i
    exact finiteStoppedOutputRecordSummary_actual restart i
  exact hrecord.congr hactual

end LALM.FiniteStopped

end
