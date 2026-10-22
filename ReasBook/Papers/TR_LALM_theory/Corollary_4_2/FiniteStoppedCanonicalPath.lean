/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.FiniteStoppedPathRealization
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedSemantics
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedLyapunovStep
import all TR_LALM_theory.Corollary_4_2.FiniteStoppedPathRealization
import all TR_LALM_theory.Corollary_4_2.FiniteStoppedSemantics
import all TR_LALM_theory.Corollary_4_2.FiniteStoppedLyapunovStep

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LALM.Correction

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
variable {params : Parameters h x₀ multiplier₀}

namespace StoppedAttemptAnalysis

open StochasticRun.Localization

variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}
variable {attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X}

/-- The exact active-prefix length in the finite corrected semantics. -/
noncomputable def canonicalPrefixLength
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) : ℕ :=
  min K (StoppedAttempt.firstExitEndpoint attempt omega)

/-- The finite corrected prefix is nonempty because the initialized state is
active at index zero. -/
theorem canonicalPrefixLength_pos
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (hK : 2 ≤ K) (omega : Ω) :
    1 ≤ canonicalPrefixLength attempt omega := by
  have hactive := StoppedAttempt.activeAt_zero attempt omega
  have hτ :=
    (StoppedAttempt.activeAt_iff_lt_firstExitEndpoint attempt omega 0).mp hactive
  have hτpos : 1 ≤ StoppedAttempt.firstExitEndpoint attempt omega := by
    omega
  dsimp [canonicalPrefixLength]
  omega

/-- The exact active-prefix length never exceeds the prescribed horizon. -/
theorem canonicalPrefixLength_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) :
    canonicalPrefixLength attempt omega ≤ K := by
  exact min_le_left _ _

/-- Activity on the natural indices is exactly the strict canonical prefix. -/
theorem activeAt_iff_lt_canonicalPrefixLength
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (k : ℕ) (hk : k < K) :
    StoppedAttempt.activeAt attempt k omega ↔
      k < canonicalPrefixLength attempt omega := by
  rw [StoppedAttempt.activeAt_iff_lt_firstExitEndpoint]
  have hτ := StoppedAttempt.firstExitEndpoint_le_succ attempt omega
  dsimp [canonicalPrefixLength]
  omega

/-- The preceding stopped base step used by the finite Lyapunov value, with a
zero convention at the initialization index. -/
noncomputable def canonicalPreviousStep
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) : EuclideanSpace ℝ (Fin n) :=
  if k = 0 then 0 else StoppedAttempt.baseStep attempt (k - 1) omega

/-- The finite Lyapunov value attached to the actual stopped state at index
`k`; this is the corrected augmented Lagrangian plus the preceding-step term. -/
noncomputable def canonicalFiniteLyapunov
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) : ℝ :=
  finiteActiveLyapunov h params
    (StoppedAttempt.point attempt k omega)
    (StoppedAttempt.multiplier attempt k omega)
    (canonicalPreviousStep attempt k omega)

/-! The stopped point and multiplier paths are padded through the absorbing
    branch. An active transition therefore still has the canonical successor
    values when that successor is the first point outside `X`. -/

/-- Helper for Corollary 4.2: an active stopped transition stores the
canonical corrected point at its successor, including a first-exit successor
represented by the inactive summand. -/
theorem point_succ_eq_canonicalActiveNextPoint_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) (hk : k < K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega = Sum.inr a) :
    StoppedAttempt.point attempt (k + 1) omega =
      canonicalActiveNextPointAt h oracle params Q B b k
        (a, attempt.batch k omega) := by
  rw [StoppedAttempt.point, dif_pos hk, ha]
  rfl

/-- Helper for Corollary 4.2: the stopped point follows the natural corrected
update `x_{k+1} = nextPoint c x_k p_k` on every active transition, including a
first-exit endpoint. -/
theorem point_succ_eq_nextPoint_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) (hk : k < K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega = Sum.inr a) :
    StoppedAttempt.point attempt (k + 1) omega =
      nextPoint c (StoppedAttempt.point attempt k omega)
        (StoppedAttempt.baseStep attempt k omega) := by
  have hpoint := point_succ_eq_canonicalActiveNextPoint_of_active attempt k omega hk a ha
  have hcurrent := StoppedAttempt.activeState_current_eq_point attempt k omega
    (Nat.le_of_lt hk) a ha
  have hstep := StoppedAttempt.activeState_baseStep_eq_baseStep attempt k omega hk a ha
  calc
    StoppedAttempt.point attempt (k + 1) omega =
        canonicalActiveNextPointAt h oracle params Q B b k
          (a, attempt.batch k omega) := hpoint
    _ = nextPoint c a.1.1
        (canonicalActiveBaseStepAt h oracle params Q B b k
          (a, attempt.batch k omega)) := by rfl
    _ = nextPoint c (StoppedAttempt.point attempt k omega)
        (StoppedAttempt.baseStep attempt k omega) := by rw [hcurrent, hstep]

/-- Helper for Corollary 4.2: an active stopped transition stores the
canonical corrected multiplier at its successor, including a first-exit
successor represented by the inactive summand. -/
theorem multiplier_succ_eq_canonicalActiveNextMultiplier_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) (hk : k < K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega = Sum.inr a) :
    StoppedAttempt.multiplier attempt (k + 1) omega =
      canonicalActiveNextMultiplierAt h oracle params Q B b k
        (a, attempt.batch k omega) := by
  rw [StoppedAttempt.multiplier, dif_pos hk, ha]
  rfl

/-- Helper for Corollary 4.2: the stopped multiplier obeys the natural
nonlinear-residual update on every active transition, even when its endpoint
is the first point outside `X`. -/
theorem multiplier_succ_eq_add_residual_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) (hk : k < K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega = Sum.inr a) :
    StoppedAttempt.multiplier attempt (k + 1) omega =
      StoppedAttempt.multiplier attempt k omega +
        (params.rho : ℝ) • c (StoppedAttempt.point attempt (k + 1) omega) := by
  have hmultiplier := StoppedAttempt.activeState_multiplier_eq_multiplier attempt k omega
    (Nat.le_of_lt hk) a ha
  have hpoint := point_succ_eq_canonicalActiveNextPoint_of_active attempt k omega hk a ha
  calc
    StoppedAttempt.multiplier attempt (k + 1) omega =
        canonicalActiveNextMultiplierAt h oracle params Q B b k
          (a, attempt.batch k omega) :=
      multiplier_succ_eq_canonicalActiveNextMultiplier_of_active attempt k omega hk a ha
    _ = a.1.2.2.1 + (params.rho : ℝ) • c
          (canonicalActiveNextPointAt h oracle params Q B b k
            (a, attempt.batch k omega)) := by
      rfl
    _ = StoppedAttempt.multiplier attempt k omega +
          (params.rho : ℝ) • c (StoppedAttempt.point attempt (k + 1) omega) := by
      rw [hmultiplier, hpoint]

/-- Helper for Corollary 4.2: the actual finite Lyapunov value at an active
successor is the canonical active successor Lyapunov value. This also applies
when the successor is the first point outside `X`. -/
theorem canonicalFiniteLyapunov_succ_eq_canonicalActiveNext
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) (hk : k < K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega = Sum.inr a) :
    canonicalFiniteLyapunov attempt (k + 1) omega =
      finiteActiveLyapunov h params
        (canonicalActiveNextPointAt h oracle params Q B b k
          (a, attempt.batch k omega))
        (canonicalActiveNextMultiplierAt h oracle params Q B b k
          (a, attempt.batch k omega))
        (canonicalActiveBaseStepAt h oracle params Q B b k
          (a, attempt.batch k omega)) := by
  unfold canonicalFiniteLyapunov canonicalPreviousStep
  simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
  rw [point_succ_eq_canonicalActiveNextPoint_of_active attempt k omega hk a ha,
    multiplier_succ_eq_canonicalActiveNextMultiplier_of_active attempt k omega hk
      a ha,
    StoppedAttempt.activeState_baseStep_eq_baseStep attempt k omega hk a ha]

/-! The next two adapters put the finite stopped observables into exactly the
    normal form consumed by the canonical one-step Lyapunov theorem. -/

/-- Helper for Corollary 4.2: an active stopped error square is the square of
the canonical clipped-estimator error attached to the same active state and
fresh batch. -/
theorem activeGradientErrorIntegrand_eq_canonicalActiveGradientError
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) (hk : k < K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega = Sum.inr a) :
    activeGradientErrorIntegrand attempt k omega =
      ‖canonicalActiveGradientErrorAt h oracle params Q B b k
          (a, attempt.batch k omega)‖ ^ 2 := by
  rw [activeGradientErrorIntegrand_eq_canonical attempt k omega hk a ha]
  rfl

/-- Helper for Corollary 4.2: an active stopped base-step square is the square
of the canonical active base step attached to that state and batch. -/
theorem activeBaseStepIntegrand_eq_canonicalActiveBaseStep
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) (hk : k < K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega = Sum.inr a) :
    activeBaseStepIntegrand attempt k omega =
      ‖canonicalActiveBaseStepAt h oracle params Q B b k
          (a, attempt.batch k omega)‖ ^ 2 := by
  exact activeBaseStepIntegrand_eq_canonical attempt k omega hk a ha

/-- Helper for Corollary 4.2: the canonical finite Lyapunov descent theorem
applies to every charged positive-index transition, including the transition
whose successor is the first point outside `X`. -/
theorem canonicalFiniteLyapunovDescent_of_prefix
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) {k : ℕ}
    (hk_pos : 1 ≤ k)
    (hk_prefix : k < canonicalPrefixLength attempt omega) :
    canonicalFiniteLyapunov attempt (k + 1) omega ≤
      canonicalFiniteLyapunov attempt k omega -
        (params.beta / 4) * activeBaseStepIntegrand attempt k omega +
      lyapunovErrorConstant h params *
        (activeGradientErrorIntegrand attempt k omega +
          activeGradientErrorIntegrand attempt (k - 1) omega) := by
  have hprefix_le := canonicalPrefixLength_le attempt omega
  have hkK : k < K := by omega
  have hprevK : k - 1 < K := by omega
  have hactiveCurrent : StoppedAttempt.activeAt attempt k omega := by
    exact (activeAt_iff_lt_canonicalPrefixLength attempt omega k hkK).mpr
      hk_prefix
  obtain ⟨aCurrent, hcurrentState⟩ :=
    (StoppedAttempt.activeAt_iff_state attempt k omega
      (Nat.le_of_lt hkK)).mp hactiveCurrent
  have hcurrentState' :
      attempt.state ⟨k, Nat.lt_succ_of_lt hkK⟩ omega = Sum.inr aCurrent :=
    hcurrentState
  let kPrev : Fin K := ⟨k - 1, hprevK⟩
  have hcurrentStateSucc : attempt.state kPrev.succ omega = Sum.inr aCurrent := by
    have hidx : kPrev.succ =
        (⟨k, Nat.lt_succ_of_lt hkK⟩ : Fin (K + 1)) := by
      apply Fin.ext
      dsimp [kPrev]
      omega
    rw [hidx]
    exact hcurrentState'
  obtain ⟨aPrevious, hpreviousState, _hpointMem, hdata⟩ :=
    StoppedAttempt.activeSuccessor_data attempt kPrev omega aCurrent
      hcurrentStateSucc
  have hpreviousState' :
      attempt.state ⟨k - 1, Nat.lt_succ_of_lt hprevK⟩ omega = Sum.inr aPrevious := by
    simpa only [kPrev, Fin.castSucc_mk] using hpreviousState
  have hcanonical :=
    canonicalActiveFiniteLyapunovDescent
      (h := h) (oracle := oracle) (params := params)
      (Q := Q) (B := B) (b := b) attempt.region_condition (k - 1)
      (aPrevious, attempt.batch (k - 1) omega)
      (aCurrent, attempt.batch k omega) hdata
  have hleft := canonicalFiniteLyapunov_succ_eq_canonicalActiveNext
    attempt k omega hkK aCurrent hcurrentState'
  have hright := canonicalFiniteLyapunov_succ_eq_canonicalActiveNext
    attempt (k - 1) omega hprevK aPrevious hpreviousState'
  have hstep := activeBaseStepIntegrand_eq_canonicalActiveBaseStep
    attempt k omega hkK aCurrent hcurrentState'
  have herror := activeGradientErrorIntegrand_eq_canonicalActiveGradientError
    attempt k omega hkK aCurrent hcurrentState'
  have hpreviousError := activeGradientErrorIntegrand_eq_canonicalActiveGradientError
    attempt (k - 1) omega hprevK aPrevious hpreviousState'
  have hindex : (k - 1) + 1 = k := by omega
  have hdata' :
      aCurrent.1 =
        canonicalActiveNextDataAt h oracle params Q B b (k - 1)
          (aPrevious, attempt.batch (k - 1) omega) := by
    simpa only [kPrev] using hdata
  have hcurrentPoint :
      aCurrent.1.1 =
        canonicalActiveNextPointAt h oracle params Q B b (k - 1)
          (aPrevious, attempt.batch (k - 1) omega) := by
    rw [← canonicalActiveNextDataAt_current (h := h) (oracle := oracle)
      (params := params) (Q := Q) (B := B) (b := b) aPrevious
      (attempt.batch (k - 1) omega) (k - 1), ← hdata']
  have hcurrentMultiplier :
      aCurrent.1.2.2.1 =
        canonicalActiveNextMultiplierAt h oracle params Q B b (k - 1)
          (aPrevious, attempt.batch (k - 1) omega) := by
    rw [← canonicalActiveNextDataAt_multiplier (h := h) (oracle := oracle)
      (params := params) (Q := Q) (B := B) (b := b) aPrevious
      (attempt.batch (k - 1) omega) (k - 1), ← hdata']
  have hcanonical' :
      finiteActiveLyapunov h params
          (canonicalActiveNextPointAt h oracle params Q B b k
            (aCurrent, attempt.batch k omega))
          (canonicalActiveNextMultiplierAt h oracle params Q B b k
            (aCurrent, attempt.batch k omega))
          (canonicalActiveBaseStepAt h oracle params Q B b k
            (aCurrent, attempt.batch k omega)) ≤
        finiteActiveLyapunov h params aCurrent.1.1 aCurrent.1.2.2.1
          (canonicalActiveBaseStepAt h oracle params Q B b (k - 1)
            (aPrevious, attempt.batch (k - 1) omega)) -
          (params.beta / 4) *
            ‖canonicalActiveBaseStepAt h oracle params Q B b k
              (aCurrent, attempt.batch k omega)‖ ^ 2 +
        lyapunovErrorConstant h params *
          (‖canonicalActiveGradientErrorAt h oracle params Q B b k
              (aCurrent, attempt.batch k omega)‖ ^ 2 +
            ‖canonicalActiveGradientErrorAt h oracle params Q B b (k - 1)
              (aPrevious, attempt.batch (k - 1) omega)‖ ^ 2) := by
    simpa only [kPrev, hindex] using hcanonical
  have hcurrentLyapunov :
      finiteActiveLyapunov h params aCurrent.1.1 aCurrent.1.2.2.1
          (canonicalActiveBaseStepAt h oracle params Q B b (k - 1)
            (aPrevious, attempt.batch (k - 1) omega)) =
        canonicalFiniteLyapunov attempt k omega := by
    have hright' :
        canonicalFiniteLyapunov attempt k omega =
          finiteActiveLyapunov h params
            (canonicalActiveNextPointAt h oracle params Q B b (k - 1)
              (aPrevious, attempt.batch (k - 1) omega))
            (canonicalActiveNextMultiplierAt h oracle params Q B b (k - 1)
              (aPrevious, attempt.batch (k - 1) omega))
            (canonicalActiveBaseStepAt h oracle params Q B b (k - 1)
              (aPrevious, attempt.batch (k - 1) omega)) := by
      simpa only [hindex] using hright
    rw [hcurrentPoint, hcurrentMultiplier, ← hright']
  calc
    canonicalFiniteLyapunov attempt (k + 1) omega =
        finiteActiveLyapunov h params
          (canonicalActiveNextPointAt h oracle params Q B b k
            (aCurrent, attempt.batch k omega))
          (canonicalActiveNextMultiplierAt h oracle params Q B b k
            (aCurrent, attempt.batch k omega))
          (canonicalActiveBaseStepAt h oracle params Q B b k
            (aCurrent, attempt.batch k omega)) := hleft
    _ ≤ finiteActiveLyapunov h params aCurrent.1.1 aCurrent.1.2.2.1
          (canonicalActiveBaseStepAt h oracle params Q B b (k - 1)
            (aPrevious, attempt.batch (k - 1) omega)) -
          (params.beta / 4) *
            ‖canonicalActiveBaseStepAt h oracle params Q B b k
              (aCurrent, attempt.batch k omega)‖ ^ 2 +
        lyapunovErrorConstant h params *
          (‖canonicalActiveGradientErrorAt h oracle params Q B b k
              (aCurrent, attempt.batch k omega)‖ ^ 2 +
            ‖canonicalActiveGradientErrorAt h oracle params Q B b (k - 1)
              (aPrevious, attempt.batch (k - 1) omega)‖ ^ 2) := hcanonical'
    _ = canonicalFiniteLyapunov attempt k omega -
          (params.beta / 4) * activeBaseStepIntegrand attempt k omega +
        lyapunovErrorConstant h params *
          (activeGradientErrorIntegrand attempt k omega +
            activeGradientErrorIntegrand attempt (k - 1) omega) := by
      rw [hcurrentLyapunov, ← hstep, ← herror, ← hpreviousError]

/-- Helper for Corollary 4.2: on a failed finite attempt, the first-exit
transition has an active predecessor and its actual endpoint Lyapunov value is
the canonical active successor value. The endpoint may be inactive because it
is outside `X`; this is precisely the terminal transition used by the
telescope. -/
theorem firstExitEndpoint_canonicalTransition_bridge
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (hfailure : omega ∉ StoppedAttempt.successEvent attempt) :
    ∃ (k : ℕ) (hk : k < K) (a : ActivePreBatchState h params X),
      StoppedAttempt.firstExitEndpoint attempt omega = k + 1 ∧
      attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega =
        Sum.inr a ∧
      StoppedAttempt.point attempt (k + 1) omega ∉ X ∧
      canonicalFiniteLyapunov attempt (k + 1) omega =
        finiteActiveLyapunov h params
          (canonicalActiveNextPointAt h oracle params Q B b k
            (a, attempt.batch k omega))
          (canonicalActiveNextMultiplierAt h oracle params Q B b k
            (a, attempt.batch k omega))
          (canonicalActiveBaseStepAt h oracle params Q B b k
            (a, attempt.batch k omega)) := by
  obtain ⟨k, hk, hendpoint, hkActive, hpointOutside, _hinactive⟩ :=
    (StoppedAttempt.not_mem_successEvent_iff_exists_firstExit attempt omega).mp
      hfailure
  obtain ⟨a, ha⟩ :=
    (StoppedAttempt.activeAt_iff_state attempt k omega (Nat.le_of_lt hk)).mp hkActive
  refine ⟨k, hk, a, hendpoint, ?_, hpointOutside, ?_⟩
  · exact ha
  · exact canonicalFiniteLyapunov_succ_eq_canonicalActiveNext attempt k omega hk a ha

/-- Helper for Corollary 4.2: the first-exit bridge also accepts the analysis
success event used by the finite energy and certificate interfaces. -/
theorem firstExitEndpoint_canonicalTransition_bridge_of_analysis_failure
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (hfailure : omega ∉ successEvent attempt) :
    ∃ (k : ℕ) (hk : k < K) (a : ActivePreBatchState h params X),
      StoppedAttempt.firstExitEndpoint attempt omega = k + 1 ∧
      attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega = Sum.inr a ∧
      StoppedAttempt.point attempt (k + 1) omega ∉ X ∧
      canonicalFiniteLyapunov attempt (k + 1) omega =
        finiteActiveLyapunov h params
          (canonicalActiveNextPointAt h oracle params Q B b k
            (a, attempt.batch k omega))
          (canonicalActiveNextMultiplierAt h oracle params Q B b k
            (a, attempt.batch k omega))
          (canonicalActiveBaseStepAt h oracle params Q B b k
            (a, attempt.batch k omega)) := by
  apply firstExitEndpoint_canonicalTransition_bridge attempt omega
  intro hstopped
  apply hfailure
  rw [successEvent_eq_stoppedAttempt]
  exact hstopped

/-- A canonical finite-path witness records the stopped Lyapunov descent and
its initial/terminal rank bounds. The prefix, energies, and Lyapunov sequence
are fixed by the stopped state, and the constructor below discharges the
descent field from `canonicalFiniteLyapunovDescent_of_prefix`. -/
structure CanonicalFiniteStoppedPathWitness
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    where
  /-- The finite one-step corrected Lyapunov descent on the active prefix. -/
  lyapunov_descent :
    ∀ (omega : Ω) {k : ℕ},
      1 ≤ k → k < canonicalPrefixLength attempt omega →
      canonicalFiniteLyapunov attempt (k + 1) omega ≤
        canonicalFiniteLyapunov attempt k omega -
          (params.beta / 4) *
            activeBaseStepIntegrand attempt k omega +
          lyapunovErrorConstant h params *
            (activeGradientErrorIntegrand attempt k omega +
              activeGradientErrorIntegrand attempt (k - 1) omega)
  /-- The initialized finite Lyapunov value is below the source allowance. -/
  lyapunov_one_le_initial :
    ∀ omega, canonicalFiniteLyapunov attempt 1 omega ≤
      initialPotentialBound h params
  /-- The terminal finite Lyapunov value has the uniform lower bound. -/
  lyapunov_lower_le_terminal :
    ∀ omega, lyapunovLowerBound h params ≤
      canonicalFiniteLyapunov attempt (canonicalPrefixLength attempt omega) omega

/-- Helper for Corollary 4.2: the finite active-prefix descent theorem fills
the descent field, so initial and terminal Lyapunov bounds alone determine a
canonical stopped-path witness. -/
theorem canonicalFiniteStoppedPathWitness_of_rankBounds
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (lyapunov_one_le_initial :
      ∀ omega, canonicalFiniteLyapunov attempt 1 omega ≤
        initialPotentialBound h params)
    (lyapunov_lower_le_terminal :
      ∀ omega, lyapunovLowerBound h params ≤
        canonicalFiniteLyapunov attempt (canonicalPrefixLength attempt omega) omega) :
    CanonicalFiniteStoppedPathWitness attempt :=
  { lyapunov_descent := canonicalFiniteLyapunovDescent_of_prefix attempt
    lyapunov_one_le_initial := lyapunov_one_le_initial
    lyapunov_lower_le_terminal := lyapunov_lower_le_terminal }

/-- The canonical initial-step square is bounded by the localization radius. -/
theorem canonical_initial_step_bound
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (hK : 1 ≤ K) (omega : Ω) :
    activeBaseStepIntegrand attempt 0 omega ≤ (params.delta : ℝ) ^ 2 := by
  rw [activeBaseStepIntegrand, dif_pos (by omega : 0 < K)]
  have hstep := norm_stoppedBaseStep_le attempt 0 omega
  exact (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg params.delta)).2 hstep

/-- The corrected initial-step allowance is nonnegative whenever the stopped
attempt has its stated initial localization witness. -/
theorem initialStepBound_nonneg_of_attempt
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    0 ≤ initialStepBound h params := by
  have hx₀ : x₀ ∈ h.region :=
    attempt.region_condition.thickening_subset
      (Metric.self_subset_cthickening X attempt.initial_mem)
  have hobjective : h.objectiveLower ≤ f x₀ :=
    h.objectiveLower_le x₀ hx₀
  have hmultiplierConstant :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hdisplacement : 0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def, stepConstant_def]
    positivity
  have hgradientTerm :
      0 ≤ (h.gradientBound : ℝ) * displacementFactor h params.delta *
        params.delta := by
    positivity
  have hmultiplierTerm :
      0 ≤ 4 * (params.multiplierBound : ℝ) ^ 2 / params.rho := by
    positivity
  have hcorrectionTerm :
      0 ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * (params.delta : ℝ) ^ 2 :=
    mul_nonneg (div_nonneg hmultiplierConstant (by positivity)) (sq_nonneg _)
  have hlowerCorrection :
      0 ≤ (params.multiplierBound : ℝ) ^ 2 / (2 * params.rho) := by
    positivity
  have hgap :
      0 ≤ initialPotentialBound h params - lyapunovLowerBound h params := by
    rw [initialPotentialBound_def, lyapunovLowerBound_def]
    linarith
  rw [initialStepBound_def]
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  positivity

/-- A canonical witness produces the earlier telescope interface with the
actual stopped prefix and state projections.  The absorbing zero obligations
are derived from the first-exit semantics, not supplied as extra fields. -/
noncomputable def finiteStoppedPathWitness_of_canonical
    (witness : CanonicalFiniteStoppedPathWitness attempt)
    (hK : 2 ≤ K) :
    FiniteStoppedPathWitness attempt := by
  let prefixLength : Ω → ℕ := canonicalPrefixLength attempt
  have hprefix_pos : ∀ omega, 1 ≤ prefixLength omega := by
    intro omega
    exact canonicalPrefixLength_pos attempt hK omega
  have hprefix_le : ∀ omega, prefixLength omega ≤ K := by
    intro omega
    exact canonicalPrefixLength_le attempt omega
  let data : ∀ omega,
      FinitePrefixLyapunovData (h := h) (params := params) (prefixLength omega) :=
    fun omega ↦ {
      lyapunov := fun k ↦ canonicalFiniteLyapunov attempt k omega
      stepEnergy := fun k ↦ activeBaseStepIntegrand attempt k omega
      errorEnergy := fun k ↦ activeGradientErrorIntegrand attempt k omega
      lyapunov_one_le_initial := by
        simpa only [prefixLength] using witness.lyapunov_one_le_initial omega
      lyapunov_lower_le_terminal := by
        simpa only [prefixLength] using witness.lyapunov_lower_le_terminal omega
      descent := by
        intro k hkPos hk
        simpa only [prefixLength] using
          witness.lyapunov_descent omega hkPos hk
    }
  have hinactiveStep :
      ∀ (omega : Ω) (k : ℕ), prefixLength omega ≤ k → k < K →
        activeBaseStepIntegrand attempt k omega = 0 := by
    intro omega k hkPrefix hkK
    have hnotactive : ¬ StoppedAttempt.activeAt attempt k omega := by
      rw [activeAt_iff_lt_canonicalPrefixLength attempt omega k hkK]
      exact Nat.not_lt_of_ge hkPrefix
    rw [activeBaseStepIntegrand, dif_pos hkK]
    unfold StoppedAttempt.baseStep
    rw [dif_pos hkK]
    cases hstate : attempt.state ⟨k, Nat.lt_succ_of_lt hkK⟩ omega with
    | inl u => simp [hstate]
    | inr a =>
        exfalso
        apply hnotactive
        apply (StoppedAttempt.activeAt_iff_state attempt k omega
          (Nat.le_of_lt hkK)).mpr
        exact ⟨a, hstate⟩
  have hinactiveError :
      ∀ (omega : Ω) (k : ℕ), prefixLength omega ≤ k → k < K →
        activeGradientErrorIntegrand attempt k omega = 0 := by
    intro omega k hkPrefix hkK
    have hnotactive : ¬ StoppedAttempt.activeAt attempt k omega := by
      rw [activeAt_iff_lt_canonicalPrefixLength attempt omega k hkK]
      exact Nat.not_lt_of_ge hkPrefix
    rw [activeGradientErrorIntegrand, dif_pos hkK]
    cases hstate : attempt.state ⟨k, Nat.lt_succ_of_lt hkK⟩ omega with
    | inl u => simp [hstate]
    | inr a =>
        exfalso
        apply hnotactive
        apply (StoppedAttempt.activeAt_iff_state attempt k omega
          (Nat.le_of_lt hkK)).mpr
        exact ⟨a, hstate⟩
  have hbudget := initialStepBound_nonneg_of_attempt attempt
  refine {
    prefixLength := prefixLength
    prefixLength_pos := hprefix_pos
    prefixLength_le := hprefix_le
    data := data
    stepEnergy_eq_active := by intro omega k hk; rfl
    errorEnergy_eq_active := by intro omega k hk; rfl
    inactive_step_zero := hinactiveStep
    inactive_error_zero := hinactiveError
    initial_step_bound := by
      intro omega
      exact canonical_initial_step_bound attempt (by omega) omega
    initial_budget_nonneg := hbudget
  }

end StoppedAttemptAnalysis

end LALM.Correction

end
