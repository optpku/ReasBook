/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedEnergy
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedEnergy

public section

open MeasureTheory
open scoped BigOperators NNReal

namespace LALM.FiniteStopped.StoppedAttemptAnalysis

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
variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

open LALM.StochasticRun.Localization

/-- The finite base prefix length is the horizon clipped at the first stopped
exit endpoint.  Thus a successful attempt has length `K`, while a failed one
charges exactly the transitions before its first outside endpoint. -/
noncomputable def canonicalPrefixLength
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) : ℕ :=
  min K (StoppedAttempt.firstExitEndpoint attempt omega)

/-- The canonical finite base prefix is nonempty when the prescribed horizon
is nonzero. -/
theorem canonicalPrefixLength_pos
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (hK : 1 ≤ K) (omega : Ω) :
    1 ≤ canonicalPrefixLength attempt omega := by
  have hactive := StoppedAttempt.activeAt_zero attempt omega
  have hτ :=
    (StoppedAttempt.activeAt_iff_lt_firstExitEndpoint attempt omega
      (⟨0, Nat.zero_lt_succ K⟩ : Fin (K + 1))).mp hactive
  dsimp [canonicalPrefixLength]
  omega

/-- The canonical finite base prefix never exceeds the prescribed horizon. -/
theorem canonicalPrefixLength_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) :
    canonicalPrefixLength attempt omega ≤ K := by
  exact min_le_left _ _

/-- For every charged transition index, activity is exactly membership in the
strict canonical prefix.  The explicit `k < K` hypothesis records that an
endpoint at index `K` is a terminal state, not another charged transition. -/
theorem activeAt_iff_lt_canonicalPrefixLength
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (k : ℕ) (hk : k < K) :
    StoppedAttempt.activeAt attempt
        (⟨k, Nat.lt_succ_of_lt hk⟩ : Fin (K + 1)) omega ↔
      k < canonicalPrefixLength attempt omega := by
  rw [StoppedAttempt.activeAt_iff_lt_firstExitEndpoint]
  dsimp [canonicalPrefixLength]
  omega

/-- On charged natural indices, the natural-index activity adapter has the
same canonical-prefix characterization.  The `k < K` guard is essential:
on a successful attempt the terminal state at `k = K` is active but is not a
charged transition. -/
theorem activeAtNat_iff_lt_canonicalPrefixLength
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (k : ℕ) (hk : k < K) :
    StoppedAttempt.activeAtNat attempt k omega ↔
      k < canonicalPrefixLength attempt omega := by
  rw [StoppedAttempt.activeAtNat_iff_lt_firstExitEndpoint]
  dsimp [canonicalPrefixLength]
  omega

/-- The executed-transition count is the canonical finite prefix length. -/
theorem executedIterations_eq_canonicalPrefixLength
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) :
    attempt.executedIterations omega = canonicalPrefixLength attempt omega := by
  exact StoppedAttempt.executedIterations_eq_min_firstExitEndpoint attempt omega

/-- A state strictly before the canonical base prefix is localized in `X`. -/
theorem point_mem_X_of_lt_canonicalPrefixLength
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (k : ℕ)
    (hk : k < canonicalPrefixLength attempt omega) :
    attempt.point
        (⟨k, Nat.lt_succ_of_lt
          (by
            have hprefix := canonicalPrefixLength_le attempt omega
            omega)⟩ : Fin (K + 1)) omega ∈ X := by
  have hkK : k < K := by
    have hprefix := canonicalPrefixLength_le attempt omega
    omega
  have hactive :=
    (activeAt_iff_lt_canonicalPrefixLength attempt omega k hkK).mpr hk
  exact StoppedAttemptAnalysis.point_mem_of_active attempt
    ⟨k, Nat.lt_succ_of_lt hkK⟩ omega hactive

/-- A state strictly before the canonical base prefix lies in the local
regularity region supplied by the localization buffer. -/
theorem point_mem_region_of_lt_canonicalPrefixLength
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (k : ℕ)
    (hk : k < canonicalPrefixLength attempt omega) :
    attempt.point
        (⟨k, Nat.lt_succ_of_lt
          (by
            have hprefix := canonicalPrefixLength_le attempt omega
            omega)⟩ : Fin (K + 1)) omega ∈ h.region := by
  have hkK : k < K := by
    have hprefix := canonicalPrefixLength_le attempt omega
    omega
  have hactive :=
    (activeAt_iff_lt_canonicalPrefixLength attempt omega k hkK).mpr hk
  exact StoppedAttemptAnalysis.point_mem_region_of_active attempt
    ⟨k, Nat.lt_succ_of_lt hkK⟩ omega hactive

/-- A finite base-prefix invariant records the two genuinely analytic
pathwise bounds still needed by the TeX proof: the model-step radius and the
multiplier radius.  The prefix itself and all observables are fixed by the
absorbing stopped transition, so these fields cannot choose unrelated paths. -/
structure FiniteStoppedPrefixInvariant
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    where
  /-- Every charged transition before the first exit has the prescribed step
  radius. -/
  step_bound :
    ∀ (omega : Ω) (k : Fin K),
      k.1 < canonicalPrefixLength attempt omega →
      ‖attempt.baseStep k omega‖ ≤ params.delta
  /-- Every state through the charged prefix, including a first outside
  endpoint, has the theorem's multiplier radius. -/
  multiplier_bound :
    ∀ (omega : Ω) (k : Fin (K + 1)),
      k.1 ≤ canonicalPrefixLength attempt omega →
      ‖attempt.multiplier k omega‖ ≤ params.multiplierBound

/-- A bounded active finite base step puts its computed endpoint in the local
regularity region.  This is the finite stopped version of the buffer argument
in the TeX proof; it does not assume the endpoint remains in `X`. -/
theorem nextPoint_mem_region_of_active_of_step_bound
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω)
    (hactive : attempt.activeAt k.castSucc omega)
    (hstep : ‖attempt.baseStep k omega‖ ≤ params.delta) :
    nextPointAt h oracle params Q B b k.1
        (attempt.state k.castSucc omega, attempt.batch k.1 omega) ∈ h.region := by
  have hx : attempt.point k.castSucc omega ∈ X :=
    StoppedAttemptAnalysis.point_mem_of_active attempt k.castSucc omega
      hactive
  have hmodelStep :=
    StoppedAttempt.baseStep_eq_activeModelStep attempt k omega hactive
  apply nextPointAt_mem_region_of_mem_of_norm_baseStep_le
    (h := h) (oracle := oracle) (params := params) (Q := Q) (B := B) (b := b)
    confidence X attempt.region_condition k.1
    (attempt.state k.castSucc omega, attempt.batch k.1 omega) hx
  rw [← hmodelStep]
  exact hstep

/-- The finite stopped multiplier projection agrees with the TeX update on an
active transition once the step bound has certified regularity of its
endpoint. -/
theorem multiplier_succ_eq_actual_of_active_of_step_bound
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω)
    (hactive : attempt.activeAt k.castSucc omega)
    (hstep : ‖attempt.baseStep k omega‖ ≤ params.delta) :
    attempt.multiplier k.succ omega =
      attempt.multiplier k.castSucc omega +
        (params.rho : ℝ) • c (attempt.point k.succ omega) := by
  have hnextRegion :=
    nextPoint_mem_region_of_active_of_step_bound attempt k omega hactive hstep
  have hmultiplier :=
    StoppedAttempt.multiplier_succ_of_active attempt k omega hactive
  have hactual :=
    nextMultiplierAt_eq_actual_of_nextPoint_mem_region
      (h := h) (oracle := oracle) (params := params) (Q := Q) (B := B) (b := b)
      k.1 (attempt.state k.castSucc omega, attempt.batch k.1 omega) hnextRegion
  have hpoint := StoppedAttempt.point_succ_of_active attempt k omega hactive
  rw [hmultiplier, hactual]
  rw [← hpoint]
  rfl

/-- The step component of a finite stopped prefix invariant certifies local
regularity for every endpoint that is actually charged. -/
theorem endpoint_mem_region_of_prefix_invariant
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (omega : Ω) (k : Fin K)
    (hk : k.1 < canonicalPrefixLength attempt omega) :
    nextPointAt h oracle params Q B b k.1
        (attempt.state k.castSucc omega, attempt.batch k.1 omega) ∈ h.region := by
  have hactive : attempt.activeAt k.castSucc omega :=
    (activeAt_iff_lt_canonicalPrefixLength attempt omega k.1 k.isLt).mpr hk
  exact nextPoint_mem_region_of_active_of_step_bound attempt k omega hactive
    (invariant.step_bound omega k hk)

/-- The multiplier update supplied by a finite stopped prefix invariant is the
actual constraint-map update from the TeX recurrence, including the first
transition whose endpoint exits `X`. -/
theorem multiplier_succ_eq_actual_of_prefix_invariant
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (omega : Ω) (k : Fin K)
    (hk : k.1 < canonicalPrefixLength attempt omega) :
    attempt.multiplier k.succ omega =
      attempt.multiplier k.castSucc omega +
        (params.rho : ℝ) • c (attempt.point k.succ omega) := by
  have hactive : attempt.activeAt k.castSucc omega :=
    (activeAt_iff_lt_canonicalPrefixLength attempt omega k.1 k.isLt).mpr hk
  exact multiplier_succ_eq_actual_of_active_of_step_bound attempt k omega hactive
    (invariant.step_bound omega k hk)

/-- Helper for Theorem 3.7: at a failed first exit, the actual multiplier
update and the prefix multiplier bounds control the endpoint constraint by
`ρ ‖c xτ‖ ≤ 2 * Λ`.  The endpoint is the charged successor, not a post-exit
state. -/
theorem firstExitEndpoint_constraint_norm_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (omega : Ω) (hfailure : omega ∉ attempt.successEvent) :
    (params.rho : ℝ) *
        ‖c (attempt.point
          (⟨StoppedAttempt.firstExitEndpoint attempt omega,
            Nat.lt_succ_of_le
              ((StoppedAttempt.not_mem_successEvent_iff_firstExitEndpoint_le
                attempt omega).mp hfailure)⟩ : Fin (K + 1)) omega)‖ ≤
      2 * (params.multiplierBound : ℝ) := by
  have hspec := StoppedAttempt.firstExitEndpoint_spec_of_failure attempt omega hfailure
  let tau : ℕ := StoppedAttempt.firstExitEndpoint attempt omega
  have htau_pos : 1 ≤ tau := by
    simpa only [tau] using hspec.1
  have htau_le : tau ≤ K := by
    simpa only [tau] using hspec.2.1
  let k : Fin K := ⟨tau - 1, by omega⟩
  have hkprefix : k.1 < canonicalPrefixLength attempt omega := by
    dsimp [k, canonicalPrefixLength, tau]
    omega
  have hupdate :=
    multiplier_succ_eq_actual_of_prefix_invariant attempt invariant omega k hkprefix
  have hendpoint :
      k.succ =
        (⟨StoppedAttempt.firstExitEndpoint attempt omega,
          Nat.lt_succ_of_le htau_le⟩ : Fin (K + 1)) := by
    apply Fin.ext
    dsimp [k, tau]
    omega
  have hpreviousBound :
      ‖attempt.multiplier k.castSucc omega‖ ≤ (params.multiplierBound : ℝ) := by
    apply invariant.multiplier_bound omega k.castSucc
    dsimp [k, canonicalPrefixLength, tau]
    omega
  have hendpointBound :
      ‖attempt.multiplier k.succ omega‖ ≤ (params.multiplierBound : ℝ) := by
    apply invariant.multiplier_bound omega k.succ
    dsimp [k, canonicalPrefixLength, tau]
    omega
  have hresidualIdentity :
      (params.rho : ℝ) • c (attempt.point k.succ omega) =
        attempt.multiplier k.succ omega - attempt.multiplier k.castSucc omega := by
    rw [hupdate]
    module
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  rw [← hendpoint]
  calc
    (params.rho : ℝ) * ‖c (attempt.point k.succ omega)‖ =
        ‖(params.rho : ℝ) • c (attempt.point k.succ omega)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrho]
    _ = ‖attempt.multiplier k.succ omega -
          attempt.multiplier k.castSucc omega‖ :=
      congrArg norm hresidualIdentity
    _ ≤ ‖attempt.multiplier k.succ omega‖ +
          ‖attempt.multiplier k.castSucc omega‖ := norm_sub_le _ _
    _ ≤ 2 * (params.multiplierBound : ℝ) := by linarith

/-- The endpoint of a failed canonical prefix is outside `X`; the state is
still retained so the final transition can be inspected without invoking a
post-exit oracle row. -/
theorem firstExitEndpoint_point_not_mem_of_failure_canonical
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (hfailure : omega ∉ attempt.successEvent) :
    attempt.point
        (⟨StoppedAttempt.firstExitEndpoint attempt omega,
          Nat.lt_succ_of_le
            ((StoppedAttempt.not_mem_successEvent_iff_firstExitEndpoint_le
              attempt omega).mp hfailure)⟩ : Fin (K + 1)) omega ∉ X :=
  StoppedAttempt.firstExitEndpoint_point_not_mem_of_failure attempt omega hfailure

end LALM.FiniteStopped.StoppedAttemptAnalysis

end
