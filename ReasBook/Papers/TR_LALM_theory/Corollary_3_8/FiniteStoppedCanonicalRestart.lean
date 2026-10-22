/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Probability.Independence.InfinitePi
public import TR_LALM_theory.Corollary_3_8.CanonicalStoppedAttempt
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestart
import all TR_LALM_theory.Corollary_3_8.CanonicalStoppedAttempt
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedRestart

public section

open MeasureTheory

namespace LALM.FiniteStopped

open LALM.StochasticRun.Localization

universe u v w

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Ω' : Type w} [MeasurableSpace Ω'] {P' : Measure Ω'}
  [IsProbabilityMeasure P']
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀}

/-- Helper for Corollary 3.8: independence is preserved by a
measure-preserving pullback. -/
theorem indepFun_comp_measurePreserving
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {phi : Ω' → Ω} {U : Ω → A} {V : Ω → B}
    (hphi : MeasurePreserving phi P' P)
    (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    (hUV : ProbabilityTheory.IndepFun U V P) :
    ProbabilityTheory.IndepFun (fun omega ↦ U (phi omega))
      (fun omega ↦ V (phi omega)) P' := by
  let muU : Measure A := P.map U
  let muV : Measure B := P.map V
  have hLawU : ProbabilityTheory.HasLaw U muU P := ⟨hU, rfl⟩
  have hLawV : ProbabilityTheory.HasLaw V muV P := ⟨hV, rfl⟩
  have hLawPhi : ProbabilityTheory.HasLaw phi P P' := hphi.hasLaw
  have hLawPullU : ProbabilityTheory.HasLaw
      (fun omega ↦ U (phi omega)) muU P' := by
    simpa only [Function.comp_def] using hLawU.comp hLawPhi
  have hLawPullV : ProbabilityTheory.HasLaw
      (fun omega ↦ V (phi omega)) muV P' := by
    simpa only [Function.comp_def] using hLawV.comp hLawPhi
  have hLawJoint : ProbabilityTheory.HasLaw (fun omega ↦ (U omega, V omega))
      (muU.prod muV) P := hUV.hasLaw_prod hLawU hLawV
  have hLawPullJoint : ProbabilityTheory.HasLaw
      (fun omega ↦ (U (phi omega), V (phi omega))) (muU.prod muV) P' := by
    simpa only [Function.comp_def] using hLawJoint.comp hLawPhi
  exact (ProbabilityTheory.indepFun_iff_hasLaw_prodMk_prod
    hLawPullU hLawPullV).mpr hLawPullJoint

omit [IsProbabilityMeasure P] in
/-- Helper for Corollary 3.8: mutual independence is preserved by a
measure-preserving pullback. -/
theorem iIndepFun_comp_measurePreserving
    {ι : Type*} {A : ι → Type*} [mA : ∀ i, MeasurableSpace (A i)]
    {phi : Ω' → Ω} {U : (i : ι) → Ω → A i}
    (hphi : MeasurePreserving phi P' P)
    (hU : AEMeasurable (fun omega i ↦ U i omega) P)
    (hIndep : ProbabilityTheory.iIndepFun U P) :
    ProbabilityTheory.iIndepFun (fun i omega ↦ U i (phi omega)) P' := by
  let mu : (i : ι) → Measure (A i) := fun i ↦ P.map (U i)
  have hLaw (i : ι) : ProbabilityTheory.HasLaw (U i) (mu i) P :=
    ⟨hU.eval i, rfl⟩
  have hLawPhi : ProbabilityTheory.HasLaw phi P P' := hphi.hasLaw
  have hLawPull (i : ι) :
      ProbabilityTheory.HasLaw (fun omega ↦ U i (phi omega)) (mu i) P' := by
    simpa only [Function.comp_def] using (hLaw i).comp hLawPhi
  have hJointLaw : ProbabilityTheory.HasLaw (fun omega i ↦ U i omega)
      (Measure.infinitePi mu) P :=
    hIndep.hasLaw_infinitePi hLaw hU
  have hPullJointLaw : ProbabilityTheory.HasLaw
      (fun omega i ↦ U i (phi omega)) (Measure.infinitePi mu) P' := by
    simpa only [Function.comp_def] using hJointLaw.comp hLawPhi
  have hPullMeasurable : AEMeasurable (fun omega i ↦ U i (phi omega)) P' :=
    hU.comp_quasiMeasurePreserving hphi.quasiMeasurePreserving
  exact (ProbabilityTheory.iIndepFun_iff_hasLaw_Pi_infinitePi
    hLawPull hPullMeasurable).mpr hPullJointLaw

namespace StoppedAttempt

variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Corollary 3.8: pull back every latent sample coordinate of a
finite stopped attempt. -/
def pullSample
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (phi : Ω' → Ω) (k i : ℕ) (omega : Ω') : Ξ :=
  attempt.sample k i (phi omega)

/-- Helper for Corollary 3.8: pull back every state of a finite stopped
attempt. -/
def pullState
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (phi : Ω' → Ω) (k : Fin (K + 1)) (omega : Ω') : PreBatchState n m :=
  attempt.state k (phi omega)

omit [IsProbabilityMeasure P'] in
/-- Helper for Corollary 3.8: pulled sample coordinates are measurable. -/
theorem measurable_pullSample
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (phi : Ω' → Ω) (hphi : MeasurePreserving phi P' P) (k i : ℕ) :
    Measurable (pullSample attempt phi k i) :=
  (attempt.measurable_sample k i).comp hphi.measurable

omit [IsProbabilityMeasure P'] in
/-- Helper for Corollary 3.8: pulled sample coordinates retain the oracle law. -/
theorem pullSample_hasLaw
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (phi : Ω' → Ω) (hphi : MeasurePreserving phi P' P) (k i : ℕ) :
    ProbabilityTheory.HasLaw (pullSample attempt phi k i) ν P' := by
  change ProbabilityTheory.HasLaw
    (fun omega ↦ attempt.sample k i (phi omega)) ν P'
  simpa only [Function.comp_def] using
    (attempt.hasLaw_sample k i).comp hphi.hasLaw

/-- Helper for Corollary 3.8: the pulled sample array remains mutually
independent. -/
theorem pullSample_iIndepFun
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (phi : Ω' → Ω) (hphi : MeasurePreserving phi P' P) :
    ProbabilityTheory.iIndepFun
      (fun ki : ℕ × ℕ ↦ pullSample attempt phi ki.1 ki.2) P' := by
  have hMeasurable : AEMeasurable
      (fun (omega : Ω) (ki : ℕ × ℕ) ↦ attempt.sample ki.1 ki.2 omega) P := by
    apply aemeasurable_pi_lambda
    intro ki
    exact (attempt.measurable_sample ki.1 ki.2).aemeasurable
  have hPull := iIndepFun_comp_measurePreserving hphi hMeasurable
    attempt.independent_sample
  change ProbabilityTheory.iIndepFun
    (fun (ki : ℕ × ℕ) (omega : Ω') ↦
      attempt.sample ki.1 ki.2 (phi omega)) P'
  exact hPull

omit [IsProbabilityMeasure P'] in
/-- Helper for Corollary 3.8: pulled finite states are measurable. -/
theorem measurable_pullState
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (phi : Ω' → Ω) (hphi : MeasurePreserving phi P' P)
    (k : Fin (K + 1)) : Measurable (pullState attempt phi k) :=
  (attempt.measurable_state k).comp hphi.measurable

/-- Helper for Corollary 3.8: a pulled pre-batch state remains independent of
its fresh pulled sample row. -/
theorem pullState_indep_pullSample
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (phi : Ω' → Ω) (hphi : MeasurePreserving phi P' P) (k : Fin K) :
    ProbabilityTheory.IndepFun (pullState attempt phi k.castSucc)
      (fun omega i ↦ pullSample attempt phi k i omega) P' := by
  have hState : AEMeasurable (attempt.state k.castSucc) P :=
    (attempt.measurable_state k.castSucc).aemeasurable
  have hBatch : AEMeasurable
      (fun (omega : Ω) (i : ℕ) ↦ attempt.sample k i omega) P := by
    apply aemeasurable_pi_lambda
    intro i
    exact (attempt.measurable_sample k i).aemeasurable
  have hPull := indepFun_comp_measurePreserving hphi hState hBatch
    (attempt.independent_state_sample k)
  change ProbabilityTheory.IndepFun
    (fun omega ↦ attempt.state k.castSucc (phi omega))
    (fun omega i ↦ attempt.sample k i (phi omega)) P'
  exact hPull

omit [MeasurableSpace Ω'] in
/-- Helper for Corollary 3.8: the pulled stopped state has the same initial
condition. -/
theorem pullState_zero
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (phi : Ω' → Ω) (omega : Ω') :
    pullState attempt phi ⟨0, Nat.zero_lt_succ K⟩ omega =
      initialState x₀ multiplier₀ :=
  attempt.state_zero (phi omega)

omit [MeasurableSpace Ω'] in
/-- Helper for Corollary 3.8: the pulled stopped state obeys the same finite
absorbing transition. -/
theorem pullState_succ
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (phi : Ω' → Ω) (k : Fin K) (omega : Ω') :
    pullState attempt phi k.succ omega =
      transition h oracle params Q B b X k.1
        (pullState attempt phi k.castSucc omega,
          fun i ↦ pullSample attempt phi k i omega) :=
  attempt.state_succ k (phi omega)

/-- Corollary 3.8: a finite stopped attempt transports along a
measure-preserving map. -/
noncomputable def pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (phi : Ω' → Ω) (hphi : MeasurePreserving phi P' P) :
    StoppedAttempt h oracle P' x₀ multiplier₀ params Q B b confidence K X :=
  { measurableSet_localization := attempt.measurableSet_localization
    initial_mem := attempt.initial_mem
    region_condition := attempt.region_condition
    sample := pullSample attempt phi
    measurable_sample := measurable_pullSample attempt phi hphi
    hasLaw_sample := pullSample_hasLaw attempt phi hphi
    independent_sample := pullSample_iIndepFun attempt phi hphi
    state := pullState attempt phi
    measurable_state := measurable_pullState attempt phi hphi
    independent_state_sample := pullState_indep_pullSample attempt phi hphi
    state_zero := pullState_zero attempt phi
    state_succ := pullState_succ attempt phi }

/-- Helper for Corollary 3.8: the finite observable of a pulled attempt is the
source observable evaluated after the probability-space map. -/
@[simp] theorem finiteObservable_pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (phi : Ω' → Ω) (hphi : MeasurePreserving phi P' P) (omega : Ω') :
    stoppedAttemptFiniteObservable (pullback attempt phi hphi) omega =
      stoppedAttemptFiniteObservable attempt (phi omega) := by
  rfl

end StoppedAttempt

/-- Helper for Corollary 3.8: one canonical finite restart block consists of a
uniform selector and one canonical oracle-noise array. -/
abbrev CanonicalStoppedRestartBlock (Ξ : Type u) :=
  ℕ × LALM.CanonicalSampleSpace Ξ

/-- Helper for Corollary 3.8: the common selector-and-noise block law. -/
noncomputable def canonicalStoppedRestartBlockMeasure
    (ν : Measure Ξ) (K : ℕ) (hK : 2 ≤ K) :
    Measure (CanonicalStoppedRestartBlock Ξ) :=
  (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure.prod
    (LALM.canonicalProductMeasure ν)

/-- Helper for Corollary 3.8: the common canonical restart block law is a
probability measure. -/
instance canonicalStoppedRestartBlockMeasure.instIsProbabilityMeasure
    (K : ℕ) (hK : 2 ≤ K) :
    IsProbabilityMeasure (canonicalStoppedRestartBlockMeasure ν K hK) := by
  unfold canonicalStoppedRestartBlockMeasure
  infer_instance

/-- Helper for Corollary 3.8: the canonical restart sample space contains one
selector-and-noise block for every attempt. -/
abbrev CanonicalStoppedRestartSampleSpace (Ξ : Type u) :=
  ℕ → CanonicalStoppedRestartBlock Ξ

/-- Corollary 3.8: the canonical finite stopped restart law is the countable
product of the selector-and-noise block law. -/
noncomputable def canonicalStoppedRestartMeasure
    (ν : Measure Ξ) (K : ℕ) (hK : 2 ≤ K) :
    Measure (CanonicalStoppedRestartSampleSpace Ξ) :=
  Measure.infinitePi
    (fun _ : ℕ ↦ canonicalStoppedRestartBlockMeasure ν K hK)

/-- Helper for Corollary 3.8: the canonical countable restart law is a
probability measure. -/
instance canonicalStoppedRestartMeasure.instIsProbabilityMeasure
    (K : ℕ) (hK : 2 ≤ K) :
    IsProbabilityMeasure (canonicalStoppedRestartMeasure ν K hK) := by
  unfold canonicalStoppedRestartMeasure
  infer_instance

namespace CanonicalStoppedRestart

variable {confidence : ℝ} {K : ℕ} {hK : 2 ≤ K}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Corollary 3.8: expose one selector-and-noise restart block. -/
def block (i : ℕ) (omega : CanonicalStoppedRestartSampleSpace Ξ) :
    CanonicalStoppedRestartBlock Ξ :=
  omega i

/-- Helper for Corollary 3.8: expose the selector in one restart block. -/
def outputIndex (i : ℕ) (omega : CanonicalStoppedRestartSampleSpace Ξ) : ℕ :=
  (omega i).1

/-- Helper for Corollary 3.8: expose the oracle-noise array in one restart
block. -/
def noise (i : ℕ) (omega : CanonicalStoppedRestartSampleSpace Ξ) :
    LALM.CanonicalSampleSpace Ξ :=
  (omega i).2

/-- Helper for Corollary 3.8: evaluation at a restart coordinate preserves
the common block law. -/
theorem measurePreserving_block (i : ℕ) :
    MeasurePreserving (block (Ξ := Ξ) i)
      (canonicalStoppedRestartMeasure ν K hK)
      (canonicalStoppedRestartBlockMeasure ν K hK) :=
  measurePreserving_eval_infinitePi
    (fun _ : ℕ ↦ canonicalStoppedRestartBlockMeasure ν K hK) i

/-- Corollary 3.8: every canonical selector has the prescribed uniform law. -/
theorem outputIndex_hasLaw (i : ℕ) :
    ProbabilityTheory.HasLaw (outputIndex (Ξ := Ξ) i)
      (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure
      (canonicalStoppedRestartMeasure ν K hK) := by
  have hfst : MeasurePreserving Prod.fst
      (canonicalStoppedRestartBlockMeasure ν K hK)
      (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure :=
    measurePreserving_fst
  have hcomp := hfst.comp (measurePreserving_block (Ξ := Ξ) (ν := ν) i)
  unfold outputIndex
  simpa only [block, Function.comp_def] using hcomp.hasLaw

/-- Helper for Corollary 3.8: every block noise projection preserves the
canonical oracle product law. -/
theorem measurePreserving_noise (i : ℕ) :
    MeasurePreserving (noise (Ξ := Ξ) i)
      (canonicalStoppedRestartMeasure ν K hK)
      (LALM.canonicalProductMeasure ν) := by
  have hsnd : MeasurePreserving Prod.snd
      (canonicalStoppedRestartBlockMeasure ν K hK)
      (LALM.canonicalProductMeasure ν) :=
    measurePreserving_snd
  have hcomp := hsnd.comp (measurePreserving_block (Ξ := Ξ) (ν := ν) i)
  unfold noise
  simpa only [block, Function.comp_def] using hcomp

/-- Helper for Corollary 3.8: pull a canonical finite stopped attempt back to
one restart coordinate. -/
noncomputable def attempt
    (base : SPIDER.StoppedScheduledAttempt h oracle
      (LALM.canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (i : ℕ) :
    SPIDER.StoppedScheduledAttempt h oracle
      (canonicalStoppedRestartMeasure ν K hK) x₀ multiplier₀ params
      confidence K X :=
  StoppedAttempt.pullback base (noise (Ξ := Ξ) i)
    (measurePreserving_noise (Ξ := Ξ) (ν := ν) i)

/-- Helper for Corollary 3.8: the finite observable of a coordinate attempt
depends only on that coordinate's noise array. -/
@[simp] theorem finiteObservable_attempt
    (base : SPIDER.StoppedScheduledAttempt h oracle
      (LALM.canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (i : ℕ) (omega : CanonicalStoppedRestartSampleSpace Ξ) :
    stoppedAttemptFiniteObservable (attempt (hK := hK) base i) omega =
      stoppedAttemptFiniteObservable base (noise (Ξ := Ξ) i omega) := by
  unfold attempt
  exact StoppedAttempt.finiteObservable_pullback base
    (noise (Ξ := Ξ) i)
    (measurePreserving_noise (Ξ := Ξ) (ν := ν) i) omega

/-- Helper for Corollary 3.8: one block observable records its selector and
finite stopped-attempt record. -/
noncomputable def blockObservable
    (base : SPIDER.StoppedScheduledAttempt h oracle
      (LALM.canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (z : CanonicalStoppedRestartBlock Ξ) :
    ℕ × stoppedAttemptFiniteObservableType Ξ n m K :=
  (z.1, stoppedAttemptFiniteObservable base z.2)

/-- Helper for Corollary 3.8: the joint block observable is measurable. -/
theorem measurable_blockObservable
    (base : SPIDER.StoppedScheduledAttempt h oracle
      (LALM.canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X) :
    Measurable (blockObservable base) :=
  measurable_fst.prodMk
    ((measurable_stoppedAttemptFiniteObservable base).comp measurable_snd)

/-- Corollary 3.8: the common joint law of a selector and its finite stopped
attempt is the pushforward of one canonical restart block. -/
noncomputable def jointObservableMeasure
    (base : SPIDER.StoppedScheduledAttempt h oracle
      (LALM.canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X) :
    Measure (ℕ × stoppedAttemptFiniteObservableType Ξ n m K) :=
  (canonicalStoppedRestartBlockMeasure ν K hK).map (blockObservable base)

/-- Helper for Corollary 3.8: one block observable has the common canonical
joint law. -/
theorem blockObservable_hasLaw
    (base : SPIDER.StoppedScheduledAttempt h oracle
      (LALM.canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X) :
    ProbabilityTheory.HasLaw (blockObservable base)
      (jointObservableMeasure (hK := hK) base)
      (canonicalStoppedRestartBlockMeasure ν K hK) := by
  exact ⟨(measurable_blockObservable base).aemeasurable, rfl⟩

/-- Helper for Corollary 3.8: within one block, the uniform selector is
independent of its finite stopped-attempt observable. -/
theorem block_outputIndex_indep_finiteObservable
    (base : SPIDER.StoppedScheduledAttempt h oracle
      (LALM.canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X) :
    ProbabilityTheory.IndepFun
      (fun z : CanonicalStoppedRestartBlock Ξ ↦ z.1)
      (fun z ↦ stoppedAttemptFiniteObservable base z.2)
      (canonicalStoppedRestartBlockMeasure ν K hK) :=
  ProbabilityTheory.indepFun_prod measurable_id
    (measurable_stoppedAttemptFiniteObservable base)

/-- Corollary 3.8: each canonical selector is independent of its coordinate
finite stopped attempt. -/
theorem outputIndex_indep_attempt
    (base : SPIDER.StoppedScheduledAttempt h oracle
      (LALM.canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (i : ℕ) :
    ProbabilityTheory.IndepFun (outputIndex (Ξ := Ξ) i)
      (fun omega ↦ stoppedAttemptFiniteObservable
        (attempt (hK := hK) base i) omega)
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

/-- Corollary 3.8: the selector-and-attempt records are mutually independent
over all countably many canonical restart coordinates. -/
theorem independent_attempt
    (base : SPIDER.StoppedScheduledAttempt h oracle
      (LALM.canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X) :
    ProbabilityTheory.iIndepFun
      (fun i omega ↦ (outputIndex (Ξ := Ξ) i omega,
        stoppedAttemptFiniteObservable (attempt (hK := hK) base i) omega))
      (canonicalStoppedRestartMeasure ν K hK) := by
  have hBlock : ProbabilityTheory.iIndepFun
      (fun i (omega : CanonicalStoppedRestartSampleSpace Ξ) ↦ omega i)
      (canonicalStoppedRestartMeasure ν K hK) :=
    ProbabilityTheory.iIndepFun_infinitePi
      (P := fun _ : ℕ ↦ canonicalStoppedRestartBlockMeasure ν K hK)
      (X := fun _ z ↦ z) (fun _ ↦ measurable_id)
  have hComposed := hBlock.comp (fun _ ↦ blockObservable base)
    (fun _ ↦ measurable_blockObservable base)
  simpa only [Function.comp_def, blockObservable, outputIndex, noise,
    finiteObservable_attempt] using hComposed

/-- Corollary 3.8: every canonical selector-and-attempt observable has the
same joint law, so the independent attempt family is identically distributed. -/
theorem jointObservable_hasLaw
    (base : SPIDER.StoppedScheduledAttempt h oracle
      (LALM.canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (i : ℕ) :
    ProbabilityTheory.HasLaw
      (fun omega ↦ (outputIndex (Ξ := Ξ) i omega,
        stoppedAttemptFiniteObservable (attempt (hK := hK) base i) omega))
      (jointObservableMeasure (hK := hK) base)
      (canonicalStoppedRestartMeasure ν K hK) := by
  have hBlockLaw : ProbabilityTheory.HasLaw (block (Ξ := Ξ) i)
      (canonicalStoppedRestartBlockMeasure ν K hK)
      (canonicalStoppedRestartMeasure ν K hK) :=
    (measurePreserving_block (Ξ := Ξ) (ν := ν) (K := K) (hK := hK) i).hasLaw
  have hLaw := (blockObservable_hasLaw (hK := hK) base).comp hBlockLaw
  simpa only [Function.comp_def, blockObservable, outputIndex, block, noise,
    finiteObservable_attempt] using hLaw

/-- Corollary 3.8: one canonical finite stopped attempt induces a countable
independent safeguarded restart. -/
theorem safeguardedRestart_nonempty_of_stoppedAttempt
    (base : SPIDER.StoppedScheduledAttempt h oracle
      (LALM.canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X) :
    Nonempty (StoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := canonicalStoppedRestartMeasure ν K hK) (x₀ := x₀)
      (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) := by
  exact ⟨StoppedSafeguardedRestart.ofAttempts
    (attempt (hK := hK) base)
    (outputIndex (Ξ := Ξ))
    (outputIndex_hasLaw (Ξ := Ξ) (ν := ν))
    (outputIndex_indep_attempt (hK := hK) base)
    (independent_attempt (hK := hK) base)⟩

end CanonicalStoppedRestart

/-- Corollary 3.8: the explicit countable product space supports an
independent finite stopped restart under the article's local hypotheses. -/
theorem canonicalFiniteStoppedSafeguardedRestart_nonempty
    (confidence : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X) :
    Nonempty (StoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := canonicalStoppedRestartMeasure ν K hK) (x₀ := x₀)
      (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) := by
  exact CanonicalStoppedRestart.safeguardedRestart_nonempty_of_stoppedAttempt
    (Classical.choice (LALM.canonicalStoppedScheduledAttempt_nonempty
      confidence K X hX initial_mem h_region))

/-- Corollary 3.8: choose the canonical independent finite stopped restart on
the explicit selector-and-noise product space. -/
noncomputable def canonicalFiniteStoppedSafeguardedRestart
    (confidence : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X) :
    StoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := canonicalStoppedRestartMeasure ν K hK) (x₀ := x₀)
      (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X) :=
  Classical.choice (canonicalFiniteStoppedSafeguardedRestart_nonempty
    confidence K hK X hX initial_mem h_region)

end LALM.FiniteStopped

end
