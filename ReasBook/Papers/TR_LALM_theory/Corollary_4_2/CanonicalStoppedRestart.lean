/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Probability.Independence.InfinitePi
public import TR_LALM_theory.Corollary_4_2.CanonicalStoppedAttempt
public import TR_LALM_theory.Corollary_4_2.StoppedRestart
import all TR_LALM_theory.Corollary_4_2.CanonicalStoppedAttempt
import all TR_LALM_theory.Corollary_4_2.StoppedRestart
import all TR_LALM_theory.Corollary_4_2.StoppedScheduledAttempt

public section

open MeasureTheory

namespace LALM.Correction

open StochasticRun.Localization

universe u v w

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Ω' : Type w} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}

/-- Helper for Corollary 4.2: independence of two random variables is
preserved by pullback along a measure-preserving map. -/
private lemma indepFun_comp_measurePreserving
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {φ : Ω' → Ω} {U : Ω → A} {V : Ω → B}
    (hφ : MeasurePreserving φ P' P)
    (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    (hUV : ProbabilityTheory.IndepFun U V P) :
    ProbabilityTheory.IndepFun (fun ω ↦ U (φ ω)) (fun ω ↦ V (φ ω)) P' := by
  let μU : Measure A := P.map U
  let μV : Measure B := P.map V
  have hLawU : ProbabilityTheory.HasLaw U μU P := by
    exact ⟨hU, rfl⟩
  have hLawV : ProbabilityTheory.HasLaw V μV P := by
    exact ⟨hV, rfl⟩
  have hLawφ : ProbabilityTheory.HasLaw φ P P' := hφ.hasLaw
  have hLawPullU : ProbabilityTheory.HasLaw (fun ω ↦ U (φ ω)) μU P' := by
    simpa only [Function.comp_def] using hLawU.comp hLawφ
  have hLawPullV : ProbabilityTheory.HasLaw (fun ω ↦ V (φ ω)) μV P' := by
    simpa only [Function.comp_def] using hLawV.comp hLawφ
  have hLawJoint : ProbabilityTheory.HasLaw (fun ω ↦ (U ω, V ω))
      (μU.prod μV) P := hUV.hasLaw_prod hLawU hLawV
  have hLawPullJoint : ProbabilityTheory.HasLaw
      (fun ω ↦ (U (φ ω), V (φ ω))) (μU.prod μV) P' := by
    simpa only [Function.comp_def] using hLawJoint.comp hLawφ
  exact (ProbabilityTheory.indepFun_iff_hasLaw_prodMk_prod
    hLawPullU hLawPullV).mpr hLawPullJoint

omit [IsProbabilityMeasure P] in
/-- Helper for Corollary 4.2: mutual independence of an indexed family is
preserved by pullback along a measure-preserving map. -/
private lemma iIndepFun_comp_measurePreserving
    {ι : Type*} {A : ι → Type*} [mA : ∀ i, MeasurableSpace (A i)]
    {φ : Ω' → Ω} {U : (i : ι) → Ω → A i}
    (hφ : MeasurePreserving φ P' P)
    (hU : AEMeasurable (fun ω i ↦ U i ω) P)
    (hIndep : ProbabilityTheory.iIndepFun U P) :
    ProbabilityTheory.iIndepFun (fun i ω ↦ U i (φ ω)) P' := by
  let μ : (i : ι) → Measure (A i) := fun i ↦ P.map (U i)
  have hLaw (i : ι) : ProbabilityTheory.HasLaw (U i) (μ i) P := by
    exact ⟨hU.eval i, rfl⟩
  have hLawφ : ProbabilityTheory.HasLaw φ P P' := hφ.hasLaw
  have hLawPull (i : ι) :
      ProbabilityTheory.HasLaw (fun ω ↦ U i (φ ω)) (μ i) P' := by
    simpa only [Function.comp_def] using (hLaw i).comp hLawφ
  have hJointLaw : ProbabilityTheory.HasLaw (fun ω i ↦ U i ω)
      (Measure.infinitePi μ) P :=
    hIndep.hasLaw_infinitePi hLaw hU
  have hPullJointLaw : ProbabilityTheory.HasLaw
      (fun ω i ↦ U i (φ ω)) (Measure.infinitePi μ) P' := by
    simpa only [Function.comp_def] using hJointLaw.comp hLawφ
  have hPullMeasurable : AEMeasurable (fun ω i ↦ U i (φ ω)) P' :=
    hU.comp_quasiMeasurePreserving hφ.quasiMeasurePreserving
  exact (ProbabilityTheory.iIndepFun_iff_hasLaw_Pi_infinitePi
    hLawPull hPullMeasurable).mpr hPullJointLaw

namespace StoppedAttempt

variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Corollary 4.2: pull back every latent oracle sample of a stopped
attempt along a map of probability spaces. -/
def pullSample
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (k i : ℕ) (ω : Ω') : Ξ :=
  attempt.sample k i (φ ω)

/-- Helper for Corollary 4.2: pull back every finite stopped state along a map
of probability spaces. -/
def pullState
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (k : Fin (K + 1)) (ω : Ω') :
    LocalizedPreBatchState h params X :=
  attempt.state k (φ ω)

omit [IsProbabilityMeasure P'] in
/-- Helper for Corollary 4.2: each pulled oracle coordinate is measurable. -/
private lemma measurable_pullSample
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) (k i : ℕ) :
    Measurable (pullSample attempt φ k i) := by
  exact (attempt.measurable_sample k i).comp hφ.measurable

omit [IsProbabilityMeasure P'] in
/-- Helper for Corollary 4.2: each pulled oracle coordinate retains the oracle
law. -/
private lemma pullSample_hasLaw
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) (k i : ℕ) :
    ProbabilityTheory.HasLaw (pullSample attempt φ k i) ν P' := by
  change ProbabilityTheory.HasLaw
    (fun ω ↦ attempt.sample k i (φ ω)) ν P'
  simpa only [Function.comp_def] using (attempt.hasLaw_sample k i).comp hφ.hasLaw

/-- Helper for Corollary 4.2: the pulled latent sample array remains mutually
independent. -/
private lemma pullSample_iIndepFun
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) :
    ProbabilityTheory.iIndepFun
      (fun ki : ℕ × ℕ ↦ pullSample attempt φ ki.1 ki.2) P' := by
  have hMeasurable : AEMeasurable
      (fun (ω : Ω) (ki : ℕ × ℕ) ↦ attempt.sample ki.1 ki.2 ω) P := by
    apply aemeasurable_pi_lambda
    intro ki
    exact (attempt.measurable_sample ki.1 ki.2).aemeasurable
  have hPull := iIndepFun_comp_measurePreserving
    hφ hMeasurable attempt.independent_sample
  change ProbabilityTheory.iIndepFun
    (fun (ki : ℕ × ℕ) (ω : Ω') ↦ attempt.sample ki.1 ki.2 (φ ω)) P'
  exact hPull

omit [IsProbabilityMeasure P'] in
/-- Helper for Corollary 4.2: each pulled stopped state is measurable. -/
private lemma measurable_pullState
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) (k : Fin (K + 1)) :
    Measurable (pullState attempt φ k) := by
  exact (attempt.measurable_state k).comp hφ.measurable

/-- Helper for Corollary 4.2: a pulled stopped state remains independent of its
fresh pulled sample row. -/
private lemma pullState_indep_pullSample
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) (k : Fin K) :
    ProbabilityTheory.IndepFun (pullState attempt φ k.castSucc)
      (fun ω i ↦ pullSample attempt φ k i ω) P' := by
  have hState : AEMeasurable (attempt.state k.castSucc) P :=
    (attempt.measurable_state k.castSucc).aemeasurable
  have hBatch : AEMeasurable (fun (ω : Ω) (i : ℕ) ↦ attempt.sample k i ω) P := by
    apply aemeasurable_pi_lambda
    intro i
    exact (attempt.measurable_sample k i).aemeasurable
  have hPull := indepFun_comp_measurePreserving hφ hState hBatch
    (attempt.independent_state_sample k)
  change ProbabilityTheory.IndepFun
    (fun ω ↦ attempt.state k.castSucc (φ ω))
    (fun ω i ↦ attempt.sample k i (φ ω)) P'
  exact hPull

omit [MeasurableSpace Ω'] in
/-- Helper for Corollary 4.2: the pulled finite state starts from the same
active initialized package. -/
private lemma pullState_zero
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (ω : Ω') :
    pullState attempt φ ⟨0, Nat.zero_lt_succ K⟩ ω =
      Sum.inr (initialActivePreBatchState attempt.initial_mem
        attempt.region_condition) := by
  exact attempt.state_zero (φ ω)

omit [MeasurableSpace Ω'] in
/-- Helper for Corollary 4.2: every pulled finite successor uses the same
absorbing localized transition as its source attempt. -/
private lemma pullState_succ
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (k : Fin K) (ω : Ω') :
    pullState attempt φ k.succ ω =
      canonicalLocalizedTransition h oracle params Q B b X
        attempt.region_condition k
        (pullState attempt φ k.castSucc ω,
          fun i ↦ pullSample attempt φ k i ω) := by
  exact attempt.state_succ k (φ ω)

/-- Corollary 4.2: a stopped attempt can be transported to any probability
space mapping measure-preservingly to its original space. -/
noncomputable def pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) :
    StoppedAttempt h oracle P' x₀ multiplier₀ params Q B b confidence K X :=
  { measurableSet_localization := attempt.measurableSet_localization
    initial_mem := attempt.initial_mem
    region_condition := attempt.region_condition
    sample := pullSample attempt φ
    measurable_sample := measurable_pullSample attempt φ hφ
    hasLaw_sample := pullSample_hasLaw attempt φ hφ
    independent_sample := pullSample_iIndepFun attempt φ hφ
    state := pullState attempt φ
    measurable_state := measurable_pullState attempt φ hφ
    independent_state_sample := pullState_indep_pullSample attempt φ hφ
    state_zero := pullState_zero attempt φ
    state_succ := pullState_succ attempt φ }

/-- Helper for Corollary 4.2: the sample projection of a pulled stopped attempt
is composition with the probability-space map. -/
@[simp] theorem pullback_sample_apply
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P)
    (k i : ℕ) (ω : Ω') :
    (pullback attempt φ hφ).sample k i ω = attempt.sample k i (φ ω) :=
  by
    unfold pullback pullSample
    rfl

/-- Helper for Corollary 4.2: the state projection of a pulled stopped attempt
is composition with the probability-space map. -/
@[simp] theorem pullback_state_apply
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P)
    (k : Fin (K + 1)) (ω : Ω') :
    (pullback attempt φ hφ).state k ω = attempt.state k (φ ω) :=
  by
    unfold pullback pullState
    rfl

/-- Helper for Corollary 4.2: the batch of a pulled stopped attempt is the
source batch evaluated after the probability-space map. -/
@[simp] theorem batch_pullback_aux
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P)
    (k : ℕ) (ω : Ω') :
    (pullback attempt φ hφ).batch k ω = attempt.batch k (φ ω) :=
  by
    funext i
    unfold StoppedAttempt.batch
    exact pullback_sample_apply attempt φ hφ k i ω

/-- Helper for Corollary 4.2: the padded primal path of a pulled stopped
attempt is the pullback of the source primal path. -/
@[simp] theorem point_pullback_aux
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P)
    (k : ℕ) (ω : Ω') :
    point (pullback attempt φ hφ) k ω = point attempt k (φ ω) := by
  induction k with
  | zero =>
      unfold StoppedAttempt.point
      rfl
  | succ k ih =>
      by_cases hk : k < K
      · unfold StoppedAttempt.point
        simp only [dif_pos hk, pullback_state_apply, batch_pullback_aux, ih]
      · unfold StoppedAttempt.point
        simp only [dif_neg hk, ih]

/-- Helper for Corollary 4.2: the padded multiplier path of a pulled stopped
attempt is the pullback of the source multiplier path. -/
@[simp] theorem multiplier_pullback_aux
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P)
    (k : ℕ) (ω : Ω') :
    multiplier (pullback attempt φ hφ) k ω =
      multiplier attempt k (φ ω) := by
  induction k with
  | zero =>
      unfold StoppedAttempt.multiplier
      rfl
  | succ k ih =>
      by_cases hk : k < K
      · unfold StoppedAttempt.multiplier
        simp only [dif_pos hk, pullback_state_apply, batch_pullback_aux, ih]
      · unfold StoppedAttempt.multiplier
        simp only [dif_neg hk, ih]

/-- Helper for Corollary 4.2: the padded base step of a pulled stopped attempt
is the pullback of the source base step. -/
@[simp] theorem baseStep_pullback_aux
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P)
    (k : ℕ) (ω : Ω') :
    baseStep (pullback attempt φ hφ) k ω = baseStep attempt k (φ ω) := by
  unfold StoppedAttempt.baseStep
  by_cases hk : k < K
  · simp only [dif_pos hk, pullback_state_apply, batch_pullback_aux]
  · simp only [dif_neg hk]

/-- Helper for Corollary 4.2: the complete finite observable of a pulled
stopped attempt is the pullback of the source finite observable. -/
private theorem finiteObservable_pullback_aux
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) (ω : Ω') :
    stoppedAttemptFiniteObservable (pullback attempt φ hφ) ω =
      stoppedAttemptFiniteObservable attempt (φ ω) := by
  unfold LALM.Correction.stoppedAttemptFiniteObservable
  simp only [pullback_sample_apply, point_pullback_aux, multiplier_pullback_aux,
    baseStep_pullback_aux]

/-- Corollary 4.2: transporting a stopped attempt along a measure-preserving
map transports its complete finite observable by ordinary composition. -/
@[simp] theorem finiteObservable_pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) (ω : Ω') :
    stoppedAttemptFiniteObservable (pullback attempt φ hφ) ω =
      stoppedAttemptFiniteObservable attempt (φ ω) := by
  exact finiteObservable_pullback_aux attempt φ hφ ω

/-- Helper for Corollary 4.2: the terminal active success event commutes with
    a measure-preserving pullback. -/
theorem successEvent_pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) :
    StoppedAttempt.successEvent (pullback attempt φ hφ) =
      φ ⁻¹' StoppedAttempt.successEvent attempt := by
  ext ω
  change activeAt (pullback attempt φ hφ) K ω ↔ activeAt attempt K (φ ω)
  unfold activeAt activeIndicator
  simp only [dif_pos (Nat.le_refl K), pullback_state_apply]

end StoppedAttempt

/-- Helper for Corollary 4.2: one canonical stopped-restart block consists of
a uniform selector and one complete canonical oracle-noise array. -/
abbrev CanonicalStoppedRestartBlock (Ξ : Type u) :=
  ℕ × CanonicalSampleSpace Ξ

/-- Helper for Corollary 4.2: a canonical stopped-restart block has the product
law of its uniform selector and oracle-noise array. -/
noncomputable def canonicalStoppedRestartBlockMeasure
    (ν : Measure Ξ) (K : ℕ) (hK : 2 ≤ K) :
    Measure (CanonicalStoppedRestartBlock Ξ) :=
  (StochasticRun.UniformOutput.indexLaw K hK).toMeasure.prod
    (canonicalProductMeasure ν)

/-- Helper for Corollary 4.2: the canonical stopped-restart block law is a
probability measure. -/
instance canonicalStoppedRestartBlockMeasure.instIsProbabilityMeasure
    (K : ℕ) (hK : 2 ≤ K) :
    IsProbabilityMeasure (canonicalStoppedRestartBlockMeasure ν K hK) := by
  unfold canonicalStoppedRestartBlockMeasure
  infer_instance

/-- Helper for Corollary 4.2: the canonical stopped-restart sample space has
one selector-and-noise block for every restart index. -/
abbrev CanonicalStoppedRestartSampleSpace (Ξ : Type u) :=
  ℕ → CanonicalStoppedRestartBlock Ξ

/-- Corollary 4.2: the canonical stopped-restart law is the countable product
of the common selector-and-noise block law. -/
noncomputable def canonicalStoppedRestartMeasure
    (ν : Measure Ξ) (K : ℕ) (hK : 2 ≤ K) :
    Measure (CanonicalStoppedRestartSampleSpace Ξ) :=
  Measure.infinitePi
    (fun _ : ℕ ↦ canonicalStoppedRestartBlockMeasure ν K hK)

/-- Helper for Corollary 4.2: the canonical countable stopped-restart law is a
probability measure. -/
instance canonicalStoppedRestartMeasure.instIsProbabilityMeasure
    (K : ℕ) (hK : 2 ≤ K) :
    IsProbabilityMeasure (canonicalStoppedRestartMeasure ν K hK) := by
  unfold canonicalStoppedRestartMeasure
  infer_instance

namespace CanonicalStoppedRestart

variable {confidence : ℝ} {K : ℕ} {hK : 2 ≤ K}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Corollary 4.2: expose the selector-and-noise block assigned to
restart index `i`. -/
def block (i : ℕ) (ω : CanonicalStoppedRestartSampleSpace Ξ) :
    CanonicalStoppedRestartBlock Ξ :=
  ω i

/-- Helper for Corollary 4.2: expose the uniform output selector assigned to
restart index `i`. -/
def outputIndex (i : ℕ) (ω : CanonicalStoppedRestartSampleSpace Ξ) : ℕ :=
  (ω i).1

/-- Helper for Corollary 4.2: expose the canonical oracle-noise array assigned
to restart index `i`. -/
def noise (i : ℕ) (ω : CanonicalStoppedRestartSampleSpace Ξ) :
    CanonicalSampleSpace Ξ :=
  (ω i).2

/-- Helper for Corollary 4.2: evaluation at one restart coordinate preserves
the common selector-and-noise block law. -/
theorem measurePreserving_block (i : ℕ) :
    MeasurePreserving (block (Ξ := Ξ) i)
      (canonicalStoppedRestartMeasure ν K hK)
      (canonicalStoppedRestartBlockMeasure ν K hK) := by
  exact measurePreserving_eval_infinitePi
    (fun _ : ℕ ↦ canonicalStoppedRestartBlockMeasure ν K hK) i

/-- Corollary 4.2: every canonical stopped-restart selector has the prescribed
uniform output-index law. -/
theorem outputIndex_hasLaw (i : ℕ) :
    ProbabilityTheory.HasLaw (outputIndex (Ξ := Ξ) i)
      (StochasticRun.UniformOutput.indexLaw K hK).toMeasure
      (canonicalStoppedRestartMeasure ν K hK) := by
  have hfst : MeasurePreserving Prod.fst
      (canonicalStoppedRestartBlockMeasure ν K hK)
      (StochasticRun.UniformOutput.indexLaw K hK).toMeasure := by
    exact measurePreserving_fst
  have hcomp := hfst.comp (measurePreserving_block (Ξ := Ξ) (ν := ν) i)
  unfold outputIndex
  simpa only [block, Function.comp_def] using hcomp.hasLaw

/-- Helper for Corollary 4.2: the noise projection at one restart coordinate
preserves the canonical oracle product law. -/
theorem measurePreserving_noise (i : ℕ) :
    MeasurePreserving (noise (Ξ := Ξ) i)
      (canonicalStoppedRestartMeasure ν K hK) (canonicalProductMeasure ν) := by
  have hsnd : MeasurePreserving Prod.snd
      (canonicalStoppedRestartBlockMeasure ν K hK)
      (canonicalProductMeasure ν) := by
    exact measurePreserving_snd
  have hcomp := hsnd.comp (measurePreserving_block (Ξ := Ξ) (ν := ν) i)
  unfold noise
  simpa only [block, Function.comp_def] using hcomp

/-- Helper for Corollary 4.2: lift one canonical stopped scheduled attempt to
restart coordinate `i` by feeding it only that coordinate's noise array. -/
noncomputable def attempt
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (i : ℕ) :
    SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalStoppedRestartMeasure ν K hK) x₀ multiplier₀ params
      confidence K X :=
  StoppedAttempt.pullback base (noise (Ξ := Ξ) i)
    (measurePreserving_noise (Ξ := Ξ) (ν := ν) i)

/-- Helper for Corollary 4.2: expose the pullback representation of a canonical
stopped attempt for certificate transport. -/
theorem attempt_eq_pullback
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (i : ℕ) :
    attempt (hK := hK) base i =
      StoppedAttempt.pullback base (noise (Ξ := Ξ) i)
        (measurePreserving_noise (Ξ := Ξ) (ν := ν) (K := K) (hK := hK) i) := by
  rfl

/-- Helper for Corollary 4.2: the complete observable of a lifted canonical
attempt is the source observable evaluated on its coordinate noise. -/
@[simp] theorem finiteObservable_attempt
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (i : ℕ) (ω : CanonicalStoppedRestartSampleSpace Ξ) :
    stoppedAttemptFiniteObservable (attempt (hK := hK) base i) ω =
      stoppedAttemptFiniteObservable base (noise (Ξ := Ξ) i ω) := by
  unfold attempt
  exact StoppedAttempt.finiteObservable_pullback base
    (noise (Ξ := Ξ) i)
    (measurePreserving_noise (Ξ := Ξ) (ν := ν) i) ω

/-- Helper for Corollary 4.2: one block observable records its selector and
the complete finite stopped-attempt observable generated by its noise. -/
noncomputable def blockObservable
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (z : CanonicalStoppedRestartBlock Ξ) :
    ℕ × stoppedAttemptFiniteObservableType Ξ n m K :=
  (z.1, stoppedAttemptFiniteObservable base z.2)

/-- Helper for Corollary 4.2: the joint selector-and-attempt observable of one
canonical block is measurable. -/
theorem measurable_blockObservable
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X) :
    Measurable (blockObservable base) := by
  exact measurable_fst.prodMk
    ((measurable_stoppedAttemptFiniteObservable base).comp measurable_snd)

/-- Corollary 4.2: the common law of the joint selector-and-finite-attempt
observable is the pushforward of one canonical block law. -/
noncomputable def jointObservableMeasure
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X) :
    Measure (ℕ × stoppedAttemptFiniteObservableType Ξ n m K) :=
  (canonicalStoppedRestartBlockMeasure ν K hK).map (blockObservable base)

/-- Helper for Corollary 4.2: a single block observable has the canonical
joint observable law. -/
theorem blockObservable_hasLaw
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X) :
    ProbabilityTheory.HasLaw (blockObservable base)
      (jointObservableMeasure (hK := hK) base)
      (canonicalStoppedRestartBlockMeasure ν K hK) := by
  refine ⟨(measurable_blockObservable base).aemeasurable, ?_⟩
  rfl

/-- Helper for Corollary 4.2: within one canonical block, the uniform selector
is independent of the complete finite stopped-attempt observable. -/
theorem block_outputIndex_indep_finiteObservable
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X) :
    ProbabilityTheory.IndepFun
      (fun z : CanonicalStoppedRestartBlock Ξ ↦ z.1)
      (fun z ↦ stoppedAttemptFiniteObservable base z.2)
      (canonicalStoppedRestartBlockMeasure ν K hK) := by
  exact ProbabilityTheory.indepFun_prod measurable_id
    (measurable_stoppedAttemptFiniteObservable base)

/-- Corollary 4.2: at every restart coordinate, the uniform selector is
independent of its complete finite stopped-attempt observable. -/
theorem outputIndex_indep_attempt
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (i : ℕ) :
    ProbabilityTheory.IndepFun (outputIndex (Ξ := Ξ) i)
      (fun ω ↦ stoppedAttemptFiniteObservable (attempt (hK := hK) base i) ω)
      (canonicalStoppedRestartMeasure ν K hK) := by
  have hSelector : AEMeasurable
      (fun z : CanonicalStoppedRestartBlock Ξ ↦ z.1)
      (canonicalStoppedRestartBlockMeasure ν K hK) :=
    measurable_fst.aemeasurable
  have hObservable : AEMeasurable
      (fun z : CanonicalStoppedRestartBlock Ξ ↦
        stoppedAttemptFiniteObservable base z.2)
      (canonicalStoppedRestartBlockMeasure ν K hK) :=
    ((measurable_stoppedAttemptFiniteObservable base).comp
      measurable_snd).aemeasurable
  have hPull := indepFun_comp_measurePreserving
    (measurePreserving_block (Ξ := Ξ) (ν := ν) i)
    hSelector hObservable
    (block_outputIndex_indep_finiteObservable (hK := hK) base)
  unfold outputIndex
  simpa only [block, noise, finiteObservable_attempt] using hPull

/-- Corollary 4.2: the complete selector-and-finite-attempt observables are
mutually independent over all countably many restart coordinates. -/
theorem independent_attempt
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X) :
    ProbabilityTheory.iIndepFun
      (fun i ω ↦ (outputIndex (Ξ := Ξ) i ω,
        stoppedAttemptFiniteObservable (attempt (hK := hK) base i) ω))
      (canonicalStoppedRestartMeasure ν K hK) := by
  have hBlock : ProbabilityTheory.iIndepFun
      (fun i (ω : CanonicalStoppedRestartSampleSpace Ξ) ↦ ω i)
      (canonicalStoppedRestartMeasure ν K hK) := by
    exact ProbabilityTheory.iIndepFun_infinitePi
      (P := fun _ : ℕ ↦ canonicalStoppedRestartBlockMeasure ν K hK)
      (X := fun _ z ↦ z) (fun _ ↦ measurable_id)
  have hComposed := hBlock.comp (fun _ ↦ blockObservable base)
    (fun _ ↦ measurable_blockObservable base)
  simpa only [Function.comp_def, blockObservable, outputIndex, noise,
    finiteObservable_attempt] using hComposed

/-- Corollary 4.2: every joint selector-and-attempt observable has one common
law, so the canonical independent attempt family is identically distributed. -/
theorem jointObservable_hasLaw
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (i : ℕ) :
    ProbabilityTheory.HasLaw
      (fun ω ↦ (outputIndex (Ξ := Ξ) i ω,
        stoppedAttemptFiniteObservable (attempt (hK := hK) base i) ω))
      (jointObservableMeasure (hK := hK) base)
      (canonicalStoppedRestartMeasure ν K hK) := by
  have hBlockLaw : ProbabilityTheory.HasLaw (block (Ξ := Ξ) i)
      (canonicalStoppedRestartBlockMeasure ν K hK)
      (canonicalStoppedRestartMeasure ν K hK) :=
    (measurePreserving_block (Ξ := Ξ) (ν := ν) (K := K) (hK := hK) i).hasLaw
  have hLaw := (blockObservable_hasLaw (hK := hK) base).comp hBlockLaw
  simpa only [Function.comp_def, blockObservable, outputIndex, block, noise,
    finiteObservable_attempt] using hLaw

/-- Corollary 4.2: any canonical stopped scheduled attempt on one oracle-noise
array induces an infinite iid safeguarded restart on the countable product
space. -/
theorem safeguardedRestart_nonempty_of_stoppedAttempt
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X) :
    Nonempty (StoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := canonicalStoppedRestartMeasure ν K hK) (x₀ := x₀)
      (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) := by
  exact ⟨StoppedSafeguardedRestart.ofAttempts
    (attempt (hK := hK) base)
    (outputIndex (Ξ := Ξ))
    (outputIndex_hasLaw (Ξ := Ξ) (ν := ν))
    (outputIndex_indep_attempt (hK := hK) base)
    (independent_attempt (hK := hK) base)⟩

end CanonicalStoppedRestart

/-- Corollary 4.2: under the finite local region hypotheses, the explicit
countable product probability space supports an infinite iid stopped
safeguarded restart with independent uniform selectors. -/
theorem canonicalStoppedSafeguardedRestart_nonempty
    (confidence : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X) :
    Nonempty (StoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := canonicalStoppedRestartMeasure ν K hK) (x₀ := x₀)
      (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) := by
  exact CanonicalStoppedRestart.safeguardedRestart_nonempty_of_stoppedAttempt
    (Classical.choice (canonicalStoppedScheduledAttempt_nonempty
      confidence K X hX initial_mem h_region))

/-- Corollary 4.2: choose the canonical infinite iid stopped safeguarded
restart carried by the explicit countable selector-and-noise product space. -/
noncomputable def canonicalStoppedSafeguardedRestart
    (confidence : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X) :
    StoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := canonicalStoppedRestartMeasure ν K hK) (x₀ := x₀)
      (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X) :=
  Classical.choice (canonicalStoppedSafeguardedRestart_nonempty
    confidence K hK X hX initial_mem h_region)

end LALM.Correction

end
