/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedTransition

public section

open MeasureTheory
open scoped BigOperators InnerProductSpace NNReal

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

open LALM.StochasticRun.Localization

/-- Theorem 3.7: a finite stopped base NR-LALM attempt carries only the
finite state prefix and a latent iid sample array.  Once its activity flag is
zero, the successor law is the identity, so no post-exit oracle call is part
of the construction. -/
structure StoppedAttempt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (confidence : ℝ) (K : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin n))) where
  /-- The finite localization predicate is measurable. -/
  measurableSet_localization : MeasurableSet X
  /-- The prescribed initial point belongs to the localization set. -/
  initial_mem : x₀ ∈ X
  /-- The localization set supplies the local regularity buffer. -/
  region_condition : RegionCondition h oracle params confidence X
  /-- The latent iid oracle sample array. -/
  sample : ℕ → ℕ → Ω → Ξ
  /-- Every latent sample coordinate is measurable. -/
  measurable_sample (k i : ℕ) : Measurable (sample k i)
  /-- Every latent sample coordinate has the oracle law. -/
  hasLaw_sample (k i : ℕ) : ProbabilityTheory.HasLaw (sample k i) ν P
  /-- All latent sample coordinates are mutually independent. -/
  independent_sample :
    ProbabilityTheory.iIndepFun (fun ki : ℕ × ℕ ↦ sample ki.1 ki.2) P
  /-- The stopped state before every batch through the finite horizon. -/
  state : Fin (K + 1) → Ω → PreBatchState n m
  /-- Every finite stopped state is measurable. -/
  measurable_state (k : Fin (K + 1)) : Measurable (state k)
  /-- The pre-batch state is independent of its fresh sample row. -/
  independent_state_sample (k : Fin K) :
    ProbabilityTheory.IndepFun (state k.castSucc)
      (fun omega i ↦ sample k i omega) P
  /-- The finite state starts from the active initialized package. -/
  state_zero (omega : Ω) :
    state ⟨0, Nat.zero_lt_succ K⟩ omega = initialState x₀ multiplier₀
  /-- Every in-horizon successor is the absorbing stopped transition. -/
  state_succ (k : Fin K) (omega : Ω) :
    state k.succ omega =
      transition h oracle params Q B b X k.1
        (state k.castSucc omega, fun i ↦ sample k i omega)

namespace StoppedAttempt

variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Theorem 3.7: the fresh row available at a finite attempt
iteration is the corresponding latent sample row. -/
def batch
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) : ℕ → Ξ :=
  fun i ↦ attempt.sample k i omega

/-- Helper for Theorem 3.7: every finite attempt batch is measurable. -/
theorem measurable_batch
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) : Measurable (attempt.batch k) := by
  apply measurable_pi_lambda
  intro i
  exact attempt.measurable_sample k i

/-- Helper for Theorem 3.7: the finite activity observable reads the stopped
state's activity coordinate. -/
def activeAt
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin (K + 1)) (omega : Ω) : Prop :=
  (attempt.state k omega).1 = 1

/-- Helper for Theorem 3.7: the finite primal observable is the current
coordinate of the stopped state. -/
def point
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin (K + 1)) (omega : Ω) : EuclideanSpace ℝ (Fin n) :=
  (attempt.state k omega).2.1

/-- Helper for Theorem 3.7: the finite multiplier observable is the current
dual coordinate of the stopped state. -/
def multiplier
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin (K + 1)) (omega : Ω) : EuclideanSpace ℝ (Fin m) :=
  (attempt.state k omega).2.2.2.1

/-- Helper for Theorem 3.7: one charged base step is the displacement
between two consecutive finite stopped states. -/
def baseStep
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω) : EuclideanSpace ℝ (Fin n) :=
  attempt.point k.succ omega - attempt.point k.castSucc omega

/-- Theorem 3.7: finite success means that the state remains active through
the charged horizon. -/
def successEvent
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    Set Ω :=
  {omega | attempt.activeAt (Fin.last K) omega}

/-- Helper for Theorem 3.7: each finite activity event is measurable. -/
theorem measurableSet_activeAt
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin (K + 1)) :
    MeasurableSet {omega | attempt.activeAt k omega} := by
  unfold activeAt
  exact (measurableSet_singleton (1 : ℝ)).preimage
    ((measurable_fst.comp (attempt.measurable_state k)))

/-- Helper for Theorem 3.7: the finite success event is measurable. -/
theorem measurableSet_successEvent
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    MeasurableSet (attempt.successEvent) := by
  unfold successEvent
  exact attempt.measurableSet_activeAt (Fin.last K)

/-- Helper for Theorem 3.7: the initial finite state is active. -/
theorem activeAt_zero
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) :
    attempt.activeAt ⟨0, Nat.zero_lt_succ K⟩ omega := by
  unfold activeAt
  rw [attempt.state_zero]

/-- Helper for Theorem 3.7: activity at a successor is equivalent to
activity before the transition and membership of the newly computed endpoint. -/
theorem activeAt_succ_iff
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω) :
    attempt.activeAt k.succ omega ↔
      attempt.activeAt k.castSucc omega ∧
        nextPointAt h oracle params Q B b k.1
          (attempt.state k.castSucc omega, attempt.batch k.1 omega) ∈ X := by
  have hstate := attempt.state_succ k omega
  let z : PreBatchState n m × (ℕ → Ξ) :=
    (attempt.state k.castSucc omega, attempt.batch k.1 omega)
  by_cases hprev : z.1.1 = 1
  · have htransition :
        attempt.state k.succ omega = activeTransition h oracle params Q B b X k.1 z := by
      rw [hstate]
      exact transition_of_active X k.1 z hprev
    have hpoint :
        nextPointAt h oracle params Q B b k.1 z =
          nextPointAt h oracle params Q B b k.1
            (attempt.state k.castSucc omega, attempt.batch k.1 omega) := by
      rfl
    change (attempt.state k.succ omega).1 = 1 ↔
      (attempt.state k.castSucc omega).1 = 1 ∧
        nextPointAt h oracle params Q B b k.1
          (attempt.state k.castSucc omega, attempt.batch k.1 omega) ∈ X
    rw [htransition]
    change (activeTransition h oracle params Q B b X k.1 z).1 = 1 ↔
      z.1.1 = 1 ∧ nextPointAt h oracle params Q B b k.1 z ∈ X
    have hiff := activeTransition_isActive_iff
      (h := h) (oracle := oracle) (params := params)
      (Q := Q) (B := B) (b := b) X k.1 z
    simpa [activeState, hprev] using hiff
  · have htransition : attempt.state k.succ omega = z.1 := by
      rw [hstate]
      exact transition_of_inactive X k.1 z hprev
    change (attempt.state k.succ omega).1 = 1 ↔
      (attempt.state k.castSucc omega).1 = 1 ∧
        nextPointAt h oracle params Q B b k.1
          (attempt.state k.castSucc omega, attempt.batch k.1 omega) ∈ X
    rw [htransition]
    change z.1.1 = 1 ↔ z.1.1 = 1 ∧
      nextPointAt h oracle params Q B b k.1 z ∈ X
    simp [hprev]

/-- Helper for Theorem 3.7: an inactive state freezes the next point and
multiplier, and therefore charges a zero base step. -/
theorem frozen_successor_of_inactive
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω) (hinactive : ¬ attempt.activeAt k.castSucc omega) :
    attempt.point k.succ omega = attempt.point k.castSucc omega ∧
      attempt.multiplier k.succ omega = attempt.multiplier k.castSucc omega ∧
      attempt.baseStep k omega = 0 := by
  have hstate := attempt.state_succ k omega
  let z : PreBatchState n m × (ℕ → Ξ) :=
    (attempt.state k.castSucc omega, attempt.batch k.1 omega)
  have hz : z.1.1 ≠ 1 := by
    simpa only [activeAt, z] using hinactive
  have htransition : attempt.state k.succ omega = z.1 := by
    rw [hstate]
    exact transition_of_inactive X k.1 z hz
  constructor
  · simp [point, htransition, z]
  constructor
  · simp [multiplier, htransition, z]
  · simp [baseStep, point, htransition, z]

/-- Helper for Theorem 3.7: an active transition's base step is the model
step used to produce its endpoint. -/
theorem baseStep_eq_activeModelStep
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω) (hactive : attempt.activeAt k.castSucc omega) :
    attempt.baseStep k omega =
      baseStepAt h oracle params Q B b k.1
        (attempt.state k.castSucc omega, attempt.batch k.1 omega) := by
  have hstate := attempt.state_succ k omega
  let z : PreBatchState n m × (ℕ → Ξ) :=
    (attempt.state k.castSucc omega, attempt.batch k.1 omega)
  have hz : z.1.1 = 1 := by
    simpa only [activeAt, z] using hactive
  have hbatch : (fun i ↦ attempt.sample k.1 i omega) = attempt.batch k.1 omega := by
    rfl
  rw [hbatch] at hstate
  unfold baseStep point
  rw [hstate, transition_of_active X k.1 z hz]
  exact activeTransition_point_displacement h oracle params Q B b X k.1 z

/-- Helper for Theorem 3.7: an active successor stores the endpoint computed
by the finite base transition. -/
theorem point_succ_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω) (hactive : attempt.activeAt k.castSucc omega) :
    attempt.point k.succ omega =
      nextPointAt h oracle params Q B b k.1
        (attempt.state k.castSucc omega, attempt.batch k.1 omega) := by
  have hstate := attempt.state_succ k omega
  let z : PreBatchState n m × (ℕ → Ξ) :=
    (attempt.state k.castSucc omega, attempt.batch k.1 omega)
  have hz : z.1.1 = 1 := by
    simpa only [activeAt, z] using hactive
  have hbatch : (fun i ↦ attempt.sample k.1 i omega) =
      attempt.batch k.1 omega := by
    rfl
  rw [hbatch] at hstate
  unfold point
  rw [hstate, transition_of_active X k.1 z hz]
  exact activeTransition_point h oracle params Q B b X k.1 z

/-- Helper for Theorem 3.7: an active successor stores the dual update
computed by the finite base transition. -/
theorem multiplier_succ_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω) (hactive : attempt.activeAt k.castSucc omega) :
    attempt.multiplier k.succ omega =
      nextMultiplierAt h oracle params Q B b k.1
        (attempt.state k.castSucc omega, attempt.batch k.1 omega) := by
  have hstate := attempt.state_succ k omega
  let z : PreBatchState n m × (ℕ → Ξ) :=
    (attempt.state k.castSucc omega, attempt.batch k.1 omega)
  have hz : z.1.1 = 1 := by
    simpa only [activeAt, z] using hactive
  have hbatch : (fun i ↦ attempt.sample k.1 i omega) =
      attempt.batch k.1 omega := by
    rfl
  rw [hbatch] at hstate
  unfold multiplier
  rw [hstate, transition_of_active X k.1 z hz]
  exact activeTransition_multiplier h oracle params Q B b X k.1 z

end StoppedAttempt

end LALM.FiniteStopped

namespace SPIDER

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Theorem 3.7: the prescribed refresh and batch schedule specializes the
finite stopped base attempt to the theorem's horizon `K`. -/
abbrev StoppedScheduledAttempt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (params : LALM.Parameters h x₀ multiplier₀)
    (confidence : ℝ) (K : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin n))) :=
  LALM.FiniteStopped.StoppedAttempt h oracle P x₀ multiplier₀ params
    (SPIDER.refreshPeriod K) (SPIDER.refreshBatchSize K)
    (SPIDER.innerBatchSize h oracle params K) confidence K X

end SPIDER

end
