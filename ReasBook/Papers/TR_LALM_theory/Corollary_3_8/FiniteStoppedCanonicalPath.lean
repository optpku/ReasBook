/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedPathRealization
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedExitGeometry
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedLyapunovStep
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedEstimatorMoments
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedPathRealization
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedExitGeometry
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedLyapunovStep
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedEstimatorMoments

public section

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace LALM NNReal

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

open LALM.FiniteStopped

variable {attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X}

/-- Helper for Theorem 3.7: the natural-index point observable extends the
finite stopped point by zero beyond the prescribed horizon. -/
noncomputable def canonicalPointNat
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) : EuclideanSpace ℝ (Fin n) :=
  if hk : k ≤ K then
    attempt.point ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega
  else 0

/-- Helper for Theorem 3.7: the natural-index multiplier observable extends
the finite stopped multiplier by zero beyond the prescribed horizon. -/
noncomputable def canonicalMultiplierNat
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) : EuclideanSpace ℝ (Fin m) :=
  if hk : k ≤ K then
    attempt.multiplier ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega
  else 0

/-- Helper for Theorem 3.7: the preceding stopped base step is zero at
initialization and outside the finite horizon. -/
noncomputable def canonicalPreviousStep
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) : EuclideanSpace ℝ (Fin n) :=
  if _hk : k = 0 then 0
  else if hkK : k - 1 < K then
    attempt.baseStep ⟨k - 1, hkK⟩ omega
  else 0

/-- Helper for Theorem 3.7: the finite stopped Lyapunov value is the augmented
Lagrangian plus the scaled preceding-step square. -/
noncomputable def finiteActiveLyapunov
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (previousStep : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ℒ[f, c; params.rho](x, multiplier) +
    (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
      params.multiplierBound / params.rho) * ‖previousStep‖ ^ 2

/-- Helper for Theorem 3.7: the actual finite stopped Lyapunov sequence is
defined on natural indices using the bounded stopped observables. -/
noncomputable def canonicalFiniteLyapunov
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) : ℝ :=
  finiteActiveLyapunov h params
    (canonicalPointNat attempt k omega)
    (canonicalMultiplierNat attempt k omega)
    (canonicalPreviousStep attempt k omega)

/-- Helper for Theorem 3.7: bounded natural indices reduce the point adapter
to the original finite stopped point. -/
theorem canonicalPointNat_eq_point
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hk : k ≤ K) (omega : Ω) :
    canonicalPointNat attempt k omega =
      attempt.point ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega := by
  rw [canonicalPointNat, dif_pos hk]

/-- Helper for Theorem 3.7: bounded natural indices reduce the multiplier
adapter to the original finite stopped multiplier. -/
theorem canonicalMultiplierNat_eq_multiplier
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hk : k ≤ K) (omega : Ω) :
    canonicalMultiplierNat attempt k omega =
      attempt.multiplier ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega := by
  rw [canonicalMultiplierNat, dif_pos hk]

/-- Helper for Theorem 3.7: the natural previous-step adapter at a positive
index is the corresponding finite stopped base step. -/
theorem canonicalPreviousStep_succ_eq_baseStep
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω) :
    canonicalPreviousStep attempt (k.1 + 1) omega =
      attempt.baseStep k omega := by
  unfold canonicalPreviousStep
  rw [dif_neg (Nat.succ_ne_zero k.1)]
  have hindex : k.1 + 1 - 1 = k.1 := by omega
  rw [hindex, dif_pos k.isLt]

/-- Helper for Theorem 3.7: an active finite transition stores the canonical
successor point in the natural-index adapter, including a first-exit endpoint. -/
theorem canonicalPointNat_succ_eq_nextPointAt_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω)
    (hactive : attempt.activeAt k.castSucc omega) :
    canonicalPointNat attempt (k.1 + 1) omega =
      nextPointAt h oracle params Q B b k.1
        (attempt.state k.castSucc omega, attempt.batch k.1 omega) := by
  have hpoint := StoppedAttempt.point_succ_of_active attempt k omega hactive
  rw [canonicalPointNat_eq_point attempt (k.1 + 1) (by omega) omega]
  have hfin : (⟨k.1 + 1, by omega⟩ : Fin (K + 1)) = k.succ := by
    apply Fin.ext
    rfl
  rw [hfin]
  exact hpoint

/-- Helper for Theorem 3.7: an active finite transition stores the canonical
successor multiplier in the natural-index adapter. -/
theorem canonicalMultiplierNat_succ_eq_nextMultiplierAt_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω)
    (hactive : attempt.activeAt k.castSucc omega) :
    canonicalMultiplierNat attempt (k.1 + 1) omega =
      nextMultiplierAt h oracle params Q B b k.1
        (attempt.state k.castSucc omega, attempt.batch k.1 omega) := by
  have hmultiplier := StoppedAttempt.multiplier_succ_of_active attempt k omega hactive
  rw [canonicalMultiplierNat_eq_multiplier attempt (k.1 + 1) (by omega) omega]
  have hfin : (⟨k.1 + 1, by omega⟩ : Fin (K + 1)) = k.succ := by
    apply Fin.ext
    rfl
  rw [hfin]
  exact hmultiplier

/-- Helper for Theorem 3.7: the finite stopped Lyapunov at an active successor
is exactly the Lyapunov of the actual canonical transition. -/
theorem canonicalFiniteLyapunov_succ_eq_transition_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω)
    (hactive : attempt.activeAt k.castSucc omega) :
    canonicalFiniteLyapunov attempt (k.1 + 1) omega =
      finiteActiveLyapunov h params
        (nextPointAt h oracle params Q B b k.1
          (attempt.state k.castSucc omega, attempt.batch k.1 omega))
        (nextMultiplierAt h oracle params Q B b k.1
          (attempt.state k.castSucc omega, attempt.batch k.1 omega))
        (baseStepAt h oracle params Q B b k.1
          (attempt.state k.castSucc omega, attempt.batch k.1 omega)) := by
  unfold canonicalFiniteLyapunov
  rw [canonicalPointNat_succ_eq_nextPointAt_of_active attempt k omega hactive,
    canonicalMultiplierNat_succ_eq_nextMultiplierAt_of_active attempt k omega hactive,
    canonicalPreviousStep_succ_eq_baseStep attempt k omega]
  rw [StoppedAttempt.baseStep_eq_activeModelStep attempt k omega hactive]

/-- Helper for Theorem 3.7: an active stopped base-step square is the square
of the base step used by the canonical finite transition. -/
theorem activeBaseStepIntegrand_eq_baseStepAt_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω)
    (hactive : attempt.activeAt k.castSucc omega) :
    activeBaseStepIntegrand attempt k.1 omega =
      ‖baseStepAt h oracle params Q B b k.1
        (attempt.state k.castSucc omega, attempt.batch k.1 omega)‖ ^ 2 := by
  rw [activeBaseStepIntegrand, dif_pos k.isLt]
  rw [StoppedAttempt.baseStep_eq_activeModelStep attempt k omega hactive]

/-- Helper for Theorem 3.7: the clipped-error square at an active transition is
the square of the finite transition's clipped-estimator error. -/
theorem activeGradientErrorIntegrand_eq_transitionError_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω)
    (hactive : attempt.activeAt k.castSucc omega) :
    activeGradientErrorIntegrand attempt k.1 omega =
      ‖clippedEstimateAt h oracle Q B b k.1
          (attempt.state k.castSucc omega, attempt.batch k.1 omega) -
        h.objectiveGradientExtension (attempt.point k.castSucc omega)‖ ^ 2 := by
  unfold activeGradientErrorIntegrand
  simp only [dif_pos k.isLt]
  have hfin : (⟨k.1, Nat.lt_succ_of_lt k.isLt⟩ : Fin (K + 1)) = k.castSucc := by
    apply Fin.ext
    rfl
  rw [hfin]
  rw [if_pos hactive]

/- The active branch of the stopped transition is the regular branch of the
   globally extended model solver.  This is the small proof interface used by
   the adjacent-transition descent theorem below. -/

/-- Helper for Theorem 3.7: every finite base-step observable is the
displacement in the corresponding point recurrence. -/
theorem point_succ_eq_add_baseStep
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω) :
    attempt.point k.succ omega =
      attempt.point k.castSucc omega + attempt.baseStep k omega := by
  unfold StoppedAttempt.baseStep
  module

/-- Helper for Theorem 3.7: an active stopped base step globally minimizes the
explicit-gradient quadratic model at its current state. -/
theorem activeBaseStep_minimizes_model_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω)
    (hactive : attempt.activeAt k.castSucc omega) :
    IsMinOn
      (LALM.stepModelWithGradient c
        (clippedEstimateAt h oracle Q B b k.1
          (attempt.state k.castSucc omega, attempt.batch k.1 omega))
        params.rho params.beta
        (attempt.point k.castSucc omega)
        (attempt.multiplier k.castSucc omega)) Set.univ
      (attempt.baseStep k omega) := by
  have hpoint : attempt.point k.castSucc omega ∈ h.region :=
    StoppedAttemptAnalysis.point_mem_region_of_active attempt k.castSucc omega
      (by simpa only [Fin.castSucc_mk] using hactive)
  have hcanonical := canonicalModelStep_minimizes c params.rho params.beta
    (attempt.point k.castSucc omega)
    (clippedEstimateAt h oracle Q B b k.1
      (attempt.state k.castSucc omega, attempt.batch k.1 omega))
    (attempt.multiplier k.castSucc omega)
    params.spec.1.2.2.1 params.spec.1.2.1
  have hbase := StoppedAttempt.baseStep_eq_activeModelStep attempt k omega hactive
  rw [hbase]
  have hstepEq :
      baseStepAt h oracle params Q B b k.1
          (attempt.state k.castSucc omega, attempt.batch k.1 omega) =
        canonicalModelStep c params.rho params.beta
          (attempt.point k.castSucc omega)
          (clippedEstimateAt h oracle Q B b k.1
            (attempt.state k.castSucc omega, attempt.batch k.1 omega))
          (attempt.multiplier k.castSucc omega) := by
    unfold baseStepAt
    rw [Function.comp_apply]
    rw [canonicalModelStepExtension_eq h params.rho params.beta]
    · rfl
    simpa only [modelInputAt, StoppedAttempt.point, StoppedAttempt.multiplier]
      using hpoint
  rw [hstepEq]
  exact hcanonical

/-- Helper for Theorem 3.7: a point in the localization set and a bounded step
give a whole regularity segment, including a possible exit endpoint. -/
theorem segment_subset_region_of_mem_X_of_step_bound
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (x p : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ X) (hstep : ‖p‖ ≤ params.delta) :
    segment ℝ x (x + p) ⊆ h.region := by
  intro y hy
  apply attempt.region_condition.thickening_subset
  apply Metric.mem_cthickening_of_dist_le y x params.delta X hx
  have hdist : dist x (x + p) ≤ params.delta := by
    rw [dist_eq_norm, norm_sub_rev, add_sub_cancel_left]
    exact hstep
  exact (Metric.mem_closedBall.mp
    (segment_subset_closedBall_left x (x + p) hy)).trans hdist

/-- Helper for Theorem 3.7: earlier finite-prefix bounds control the effective
multiplier appearing in the current base-model normal equation. -/
theorem norm_effectiveMultiplier_le_of_prefix_bounds
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (k : Fin K)
    (hkPrefix : k.1 < canonicalPrefixLength attempt omega)
    (hstepBound : ∀ j : Fin K, j.1 < k.1 →
      ‖attempt.baseStep j omega‖ ≤ params.delta)
    (hmultiplierBound : ∀ j : Fin (K + 1), j.1 ≤ k.1 →
      ‖attempt.multiplier j omega‖ ≤ params.multiplierBound) :
    ‖attempt.multiplier k.castSucc omega +
        (params.rho : ℝ) • c (attempt.point k.castSucc omega)‖ ≤
      3 * (params.multiplierBound : ℝ) := by
  by_cases hkZero : k.1 = 0
  · have hindex : k.castSucc =
        (⟨0, Nat.zero_lt_succ K⟩ : Fin (K + 1)) := by
      apply Fin.ext
      exact hkZero
    rw [hindex]
    unfold StoppedAttempt.multiplier StoppedAttempt.point
    rw [attempt.state_zero]
    change ‖multiplier₀ + (params.rho : ℝ) • c x₀‖ ≤
      3 * (params.multiplierBound : ℝ)
    calc
      ‖multiplier₀ + (params.rho : ℝ) • c x₀‖ ≤
          ‖multiplier₀‖ + ‖(params.rho : ℝ) • c x₀‖ := norm_add_le _ _
      _ = ‖multiplier₀‖ + params.rho * ‖c x₀‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos params.spec.1.2.2.1]
      _ ≤ 3 * params.multiplierBound := by
        have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
        linarith [params.norm_multiplier₀_le, params.initialResidual_le]
  · let previous : Fin K := ⟨k.1 - 1, by omega⟩
    have hkPos : 1 ≤ k.1 := Nat.one_le_iff_ne_zero.mpr hkZero
    have hpreviousPrefix :
        previous.1 < canonicalPrefixLength attempt omega := by
      dsimp only [previous]
      omega
    have hpreviousActive : attempt.activeAt previous.castSucc omega :=
      (activeAt_iff_lt_canonicalPrefixLength attempt omega previous.1
        previous.isLt).2 hpreviousPrefix
    have hpreviousStep : ‖attempt.baseStep previous omega‖ ≤ params.delta :=
      hstepBound previous (by
        dsimp only [previous]
        omega)
    have hupdate := multiplier_succ_eq_actual_of_active_of_step_bound attempt
      previous omega hpreviousActive hpreviousStep
    have hindex : previous.succ = k.castSucc := by
      apply Fin.ext
      change (k.1 - 1) + 1 = k.1
      omega
    have heffective :
        attempt.multiplier k.castSucc omega +
            (params.rho : ℝ) • c (attempt.point k.castSucc omega) =
          (2 : ℝ) • attempt.multiplier k.castSucc omega -
            attempt.multiplier previous.castSucc omega := by
      rw [← hindex, hupdate]
      module
    rw [heffective]
    calc
      ‖(2 : ℝ) • attempt.multiplier k.castSucc omega -
          attempt.multiplier previous.castSucc omega‖ ≤
          ‖(2 : ℝ) • attempt.multiplier k.castSucc omega‖ +
            ‖attempt.multiplier previous.castSucc omega‖ := norm_sub_le _ _
      _ = 2 * ‖attempt.multiplier k.castSucc omega‖ +
          ‖attempt.multiplier previous.castSucc omega‖ := by
        rw [norm_smul, Real.norm_ofNat]
      _ ≤ 3 * params.multiplierBound := by
        have hcurrent := hmultiplierBound k.castSucc (by exact le_rfl)
        have hprevious := hmultiplierBound previous.castSucc (by
          change k.1 - 1 ≤ k.1
          exact Nat.sub_le _ _)
        have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
        linarith

/-- Helper for Theorem 3.7: the clipped stochastic base recursion satisfies the
step and multiplier bounds on every finite stopped prefix. -/
theorem canonicalPrefix_normBounds
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (N : ℕ)
    (hN : N ≤ canonicalPrefixLength attempt omega) :
    (∀ k : Fin K, k.1 < N →
      ‖attempt.baseStep k omega‖ ≤ params.delta) ∧
    (∀ k : Fin (K + 1), k.1 ≤ N →
      ‖attempt.multiplier k omega‖ ≤ params.multiplierBound) := by
  induction N with
  | zero =>
      constructor
      · intro k hk
        omega
      · intro k hk
        have hkzero : k.1 = 0 := by omega
        have hindex : k = (⟨0, Nat.zero_lt_succ K⟩ : Fin (K + 1)) := by
          apply Fin.ext
          exact hkzero
        rw [hindex]
        unfold StoppedAttempt.multiplier
        rw [attempt.state_zero]
        exact params.norm_multiplier₀_le
  | succ N ih =>
      have hprefixN : N ≤ canonicalPrefixLength attempt omega := by omega
      have hbounds := ih hprefixN
      have hprefixLe : canonicalPrefixLength attempt omega ≤ K :=
        canonicalPrefixLength_le attempt omega
      have hNK : N < K := by omega
      let k : Fin K := ⟨N, hNK⟩
      have hkPrefix : k.1 < canonicalPrefixLength attempt omega := by
        dsimp only [k]
        omega
      have hactive : attempt.activeAt k.castSucc omega :=
        (activeAt_iff_lt_canonicalPrefixLength attempt omega k.1 k.isLt).2
          hkPrefix
      have hx : attempt.point k.castSucc omega ∈ h.region :=
        point_mem_region_of_active attempt k.castSucc omega hactive
      have hxX : attempt.point k.castSucc omega ∈ X :=
        point_mem_of_active attempt k.castSucc omega hactive
      have hgradient :
          ‖clippedEstimateAt h oracle Q B b k.1
              (attempt.state k.castSucc omega, attempt.batch k.1 omega)‖ ≤
            h.gradientBound := by
        unfold clippedEstimateAt
        exact SPIDER.norm_clip_le h.gradientBound _
      have heffective := norm_effectiveMultiplier_le_of_prefix_bounds attempt
        omega k hkPrefix
        (fun j hj ↦ hbounds.1 j (by
          exact hj))
        (fun j hj ↦ hbounds.2 j (by
          exact hj))
      have hminimizes := activeBaseStep_minimizes_model_of_active attempt
        k omega hactive
      have hnewStep : ‖attempt.baseStep k omega‖ ≤ params.delta :=
        normBaseStep_le_of_minimizes h params
          (attempt.point k.castSucc omega)
          (clippedEstimateAt h oracle Q B b k.1
            (attempt.state k.castSucc omega, attempt.batch k.1 omega))
          (attempt.multiplier k.castSucc omega)
          (attempt.baseStep k omega) hx hgradient heffective hminimizes
      have hsegment := segment_subset_region_of_mem_X_of_step_bound attempt
        (attempt.point k.castSucc omega) (attempt.baseStep k omega) hxX hnewStep
      have hnewMultiplierBase := normBaseNextMultiplier_le_of_minimizes h params
        (attempt.point k.castSucc omega)
        (clippedEstimateAt h oracle Q B b k.1
          (attempt.state k.castSucc omega, attempt.batch k.1 omega))
        (attempt.baseStep k omega)
        (attempt.multiplier k.castSucc omega) hsegment hnewStep hgradient
        hminimizes
      have hupdate := multiplier_succ_eq_actual_of_active_of_step_bound attempt
        k omega hactive hnewStep
      have hpoint := point_succ_eq_add_baseStep attempt k omega
      have hnewMultiplier :
          ‖attempt.multiplier k.succ omega‖ ≤ params.multiplierBound := by
        have hbridge :
            attempt.multiplier k.succ omega =
              baseNextMultiplier c params.rho
                (attempt.point k.castSucc omega)
                (attempt.multiplier k.castSucc omega)
                (attempt.baseStep k omega) := by
          rw [hupdate, baseNextMultiplier_def, ← hpoint]
        rw [hbridge]
        exact hnewMultiplierBase
      constructor
      · intro j hj
        by_cases hjold : j.1 < N
        · exact hbounds.1 j hjold
        · have hjeq : j = k := by
            apply Fin.ext
            dsimp only [k]
            omega
          simpa only [hjeq] using hnewStep
      · intro j hj
        by_cases hjold : j.1 ≤ N
        · exact hbounds.2 j hjold
        · have hjeq : j = k.succ := by
            apply Fin.ext
            change j.1 = N + 1
            omega
          simpa only [hjeq] using hnewMultiplier

/-- Theorem 3.7: safe parameters, the localization buffer, and clipped
stochastic gradients imply the canonical finite stopped-prefix invariant. -/
theorem finiteStoppedPrefixInvariant
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    FiniteStoppedPrefixInvariant attempt := by
  refine {
    step_bound := ?_
    multiplier_bound := ?_
  }
  · intro omega k hk
    exact (canonicalPrefix_normBounds attempt omega
      (canonicalPrefixLength attempt omega) le_rfl).1 k hk
  · intro omega k hk
    exact (canonicalPrefix_normBounds attempt omega
      (canonicalPrefixLength attempt omega) le_rfl).2 k hk

/-- Theorem 3.7: the canonical finite stopped attempt satisfies the actual
refresh/update SPIDER moment recursion without an additional probabilistic
certificate. -/
theorem canonicalFiniteStoppedSPIDERRecursion
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    FiniteStoppedSPIDERRecursion attempt :=
  finiteStoppedSPIDERRecursion_of_prefixInvariant attempt
    (finiteStoppedPrefixInvariant attempt)

/-- Theorem 3.7: the canonical finite stopped attempt has the pathwise and
probabilistic components of the stopped energy coupling. -/
theorem canonicalFiniteStoppedEnergyCoupling
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    FiniteStoppedEnergyCoupling attempt :=
  finiteStoppedEnergyCoupling_of_prefixInvariant attempt
    (finiteStoppedPrefixInvariant attempt)

/-- Helper for Theorem 3.7: an active successor's canonical Lyapunov value can
be read directly from the finite stopped state and base step. -/
theorem canonicalFiniteLyapunov_succ_eq_finiteState_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω)
    (hactive : attempt.activeAt k.castSucc omega) :
    canonicalFiniteLyapunov attempt (k.1 + 1) omega =
      finiteActiveLyapunov h params
        (attempt.point k.succ omega)
        (attempt.multiplier k.succ omega)
        (attempt.baseStep k omega) := by
  have hbridge := canonicalFiniteLyapunov_succ_eq_transition_of_active
    attempt k omega hactive
  have hpoint := StoppedAttempt.point_succ_of_active attempt k omega hactive
  have hmultiplier := StoppedAttempt.multiplier_succ_of_active attempt k omega hactive
  have hbaseStep := StoppedAttempt.baseStep_eq_activeModelStep attempt k omega hactive
  rw [← hpoint, ← hmultiplier, ← hbaseStep] at hbridge
  exact hbridge

/-- Helper for Theorem 3.7: an active stopped step square is the square used by
the corresponding finite transition. -/
theorem activeBaseStepIntegrand_eq_stepSquare_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω)
    (hactive : attempt.activeAt k.castSucc omega) :
    activeBaseStepIntegrand attempt k.1 omega =
      ‖attempt.baseStep k omega‖ ^ 2 := by
  rw [activeBaseStepIntegrand_eq_baseStepAt_of_active attempt k omega hactive]
  rw [← StoppedAttempt.baseStep_eq_activeModelStep attempt k omega hactive]

/-- Helper for Theorem 3.7: on an active transition the clipped estimator error
is measured against the ordinary objective gradient. -/
theorem activeGradientErrorIntegrand_eq_gradientErrorSquare_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω)
    (hactive : attempt.activeAt k.castSucc omega) :
    activeGradientErrorIntegrand attempt k.1 omega =
      ‖clippedEstimateAt h oracle Q B b k.1
          (attempt.state k.castSucc omega, attempt.batch k.1 omega) -
        gradient f (attempt.point k.castSucc omega)‖ ^ 2 := by
  rw [activeGradientErrorIntegrand_eq_transitionError_of_active attempt k omega hactive]
  rw [h.objectiveGradientExtension_eq
    (StoppedAttemptAnalysis.point_mem_region_of_active attempt k.castSucc omega
      hactive)]

/-- Helper for Theorem 3.7: completion of squares bounds the augmented
Lagrangian from below at every regular point with a bounded multiplier. -/
theorem augmentedLagrangianLowerBound_of_norm_multiplier_le
    (h : EqualityConstrained.Regularity f c) (rho : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (bound : ℝ)
    (hrho : 0 < rho) (hx : x ∈ h.region)
    (hmultiplier : ‖multiplier‖ ≤ bound) (hbound : 0 ≤ bound) :
    h.objectiveLower - bound ^ 2 / (2 * rho) ≤
      ℒ[f, c; rho](x, multiplier) := by
  have hinner : -(‖multiplier‖ * ‖c x‖) ≤ ⟪multiplier, c x⟫_ℝ :=
    neg_le_of_abs_le (abs_real_inner_le_norm multiplier (c x))
  have hyoung :
      2 * ‖c x‖ * ‖multiplier‖ ≤
        rho * ‖c x‖ ^ 2 + rho⁻¹ * ‖multiplier‖ ^ 2 :=
    two_mul_le_add_mul_sq hrho
  have hyoungDivided := div_le_div_of_nonneg_right hyoung (by norm_num : (0 : ℝ) ≤ 2)
  have hyoungHalf :
      ‖multiplier‖ * ‖c x‖ ≤
        rho / 2 * ‖c x‖ ^ 2 + ‖multiplier‖ ^ 2 / (2 * rho) := by
    calc
      ‖multiplier‖ * ‖c x‖ = (2 * ‖c x‖ * ‖multiplier‖) / 2 := by ring
      _ ≤ (rho * ‖c x‖ ^ 2 + rho⁻¹ * ‖multiplier‖ ^ 2) / 2 :=
        hyoungDivided
      _ = rho / 2 * ‖c x‖ ^ 2 + ‖multiplier‖ ^ 2 / (2 * rho) := by
        field_simp [hrho.ne']
  have hmultiplierSq : ‖multiplier‖ ^ 2 ≤ bound ^ 2 :=
    (sq_le_sq₀ (norm_nonneg multiplier) hbound).2 hmultiplier
  have hdiv :
      ‖multiplier‖ ^ 2 / (2 * rho) ≤ bound ^ 2 / (2 * rho) :=
    (div_le_div_iff_of_pos_right (by positivity)).2 hmultiplierSq
  rw [LALM.augmentedLagrangian_def]
  have hobjective := h.objectiveLower_le x hx
  linarith

/-- Helper for Theorem 3.7: adding the nonnegative preceding-step correction
preserves the uniform Lyapunov lower bound. -/
theorem finiteActiveLyapunov_lowerBound
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (previousStep : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ h.region)
    (hmultiplier : ‖multiplier‖ ≤ params.multiplierBound) :
    LALM.lyapunovLowerBound h params ≤
      finiteActiveLyapunov h params x multiplier previousStep := by
  have hlower := augmentedLagrangianLowerBound_of_norm_multiplier_le
    h params.rho x multiplier params.multiplierBound
      params.spec.1.2.2.1 hx hmultiplier (by positivity)
  have hconstantNonneg :
      0 ≤ LALM.multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [LALM.multiplierPrimalConstant_def]
    positivity
  have hcorrectionNonneg :
      0 ≤ (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖previousStep‖ ^ 2 :=
    mul_nonneg (div_nonneg hconstantNonneg params.spec.1.2.2.1.le)
      (sq_nonneg _)
  rw [LALM.lyapunovLowerBound_def, finiteActiveLyapunov]
  linarith

/-- Helper for Theorem 3.7: a bounded multiplier lets the finite stopped
Lyapunov value control the objective at the same regular point. -/
theorem objective_le_finiteActiveLyapunov_add_multiplierCorrection
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (previousStep : EuclideanSpace ℝ (Fin n))
    (hmultiplier : ‖multiplier‖ ≤ params.multiplierBound) :
    f x ≤ finiteActiveLyapunov h params x multiplier previousStep +
      params.multiplierBound ^ 2 / (2 * params.rho) := by
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
  have hinner :
      -(‖multiplier‖ * ‖c x‖) ≤ ⟪multiplier, c x⟫_ℝ :=
    neg_le_of_abs_le (abs_real_inner_le_norm multiplier (c x))
  have hyoung :
      2 * ‖c x‖ * ‖multiplier‖ ≤
        params.rho * ‖c x‖ ^ 2 +
          (params.rho : ℝ)⁻¹ * ‖multiplier‖ ^ 2 :=
    two_mul_le_add_mul_sq hrho
  have hyoungHalf :
      ‖multiplier‖ * ‖c x‖ ≤
        params.rho / 2 * ‖c x‖ ^ 2 +
          ‖multiplier‖ ^ 2 / (2 * params.rho) := by
    have hdivided := div_le_div_of_nonneg_right hyoung
      (by norm_num : (0 : ℝ) ≤ 2)
    calc
      ‖multiplier‖ * ‖c x‖ =
          (2 * ‖c x‖ * ‖multiplier‖) / 2 := by ring
      _ ≤ (params.rho * ‖c x‖ ^ 2 +
          (params.rho : ℝ)⁻¹ * ‖multiplier‖ ^ 2) / 2 := hdivided
      _ = params.rho / 2 * ‖c x‖ ^ 2 +
          ‖multiplier‖ ^ 2 / (2 * params.rho) := by
        field_simp [hrho.ne']
  have hmultiplierSq :
      ‖multiplier‖ ^ 2 ≤ (params.multiplierBound : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hboundNonneg).2 hmultiplier
  have hmultiplierDiv :
      ‖multiplier‖ ^ 2 / (2 * (params.rho : ℝ)) ≤
        (params.multiplierBound : ℝ) ^ 2 / (2 * params.rho) :=
    (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hrho)).2
      hmultiplierSq
  have hconstraintLower :
      -(params.multiplierBound ^ 2 / (2 * (params.rho : ℝ))) ≤
        ⟪multiplier, c x⟫_ℝ + params.rho / 2 * ‖c x‖ ^ 2 := by
    linarith
  have hconstantNonneg :
      0 ≤ LALM.multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [LALM.multiplierPrimalConstant_def]
    positivity
  have hcorrectionNonneg :
      0 ≤ (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖previousStep‖ ^ 2 :=
    mul_nonneg (div_nonneg hconstantNonneg hrho.le) (sq_nonneg _)
  rw [finiteActiveLyapunov, LALM.augmentedLagrangian_def]
  linarith

/-- Helper for Theorem 3.7: a bounded first transition with the actual
multiplier update puts its Lyapunov value below the deterministic initial
potential. -/
theorem finiteActiveLyapunov_le_initialPotentialBound
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x₁ : EuclideanSpace ℝ (Fin n))
    (multiplierZero multiplierOne : EuclideanSpace ℝ (Fin m))
    (step : EuclideanSpace ℝ (Fin n))
    (hsegment : segment ℝ x₀ x₁ ⊆ h.region)
    (hdisplacement : x₁ - x₀ = step)
    (hupdate : multiplierOne =
      multiplierZero + (params.rho : ℝ) • c x₁)
    (hstep : ‖step‖ ≤ params.delta)
    (hmultiplierZero : ‖multiplierZero‖ ≤ params.multiplierBound)
    (hmultiplierOne : ‖multiplierOne‖ ≤ params.multiplierBound) :
    finiteActiveLyapunov h params x₁ multiplierOne step ≤
      LALM.initialPotentialBound h params := by
  have hobjectiveIncrement :
      ‖f x₁ - f x₀‖ ≤ h.gradientBound * ‖x₁ - x₀‖ := by
    apply (convex_segment x₀ x₁).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ)
    · intro u hu
      exact h.differentiableAt_objective (hsegment hu)
    · intro u hu
      simpa only [← toDual_gradient, LinearIsometryEquiv.norm_map] using
        h.norm_gradient_le u (hsegment hu)
    · exact left_mem_segment ℝ x₀ x₁
    · exact right_mem_segment ℝ x₀ x₁
  have hsignedObjective : f x₁ - f x₀ ≤ ‖f x₁ - f x₀‖ := by
    simpa only [Real.norm_eq_abs] using le_abs_self (f x₁ - f x₀)
  have hobjective : f x₁ ≤ f x₀ + h.gradientBound * params.delta := by
    have hgradientStep :
        (h.gradientBound : ℝ) * ‖step‖ ≤ h.gradientBound * params.delta :=
      mul_le_mul_of_nonneg_left hstep (NNReal.coe_nonneg h.gradientBound)
    rw [hdisplacement] at hobjectiveIncrement
    linarith
  have hresidualIdentity :
      (params.rho : ℝ) • c x₁ = multiplierOne - multiplierZero := by
    rw [hupdate]
    module
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hscaledResidual :
      params.rho * ‖c x₁‖ ≤ 2 * params.multiplierBound := by
    calc
      params.rho * ‖c x₁‖ = ‖(params.rho : ℝ) • c x₁‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrho]
      _ = ‖multiplierOne - multiplierZero‖ := congrArg norm hresidualIdentity
      _ ≤ ‖multiplierOne‖ + ‖multiplierZero‖ := norm_sub_le _ _
      _ ≤ 2 * params.multiplierBound := by linarith
  have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
  have hinnerBound :
      ⟪multiplierOne, c x₁⟫_ℝ ≤
        params.multiplierBound * ‖c x₁‖ := by
    calc
      ⟪multiplierOne, c x₁⟫_ℝ ≤ ‖multiplierOne‖ * ‖c x₁‖ :=
        real_inner_le_norm _ _
      _ ≤ params.multiplierBound * ‖c x₁‖ :=
        mul_le_mul_of_nonneg_right hmultiplierOne (norm_nonneg _)
  have hinnerScaled :
      params.rho * ⟪multiplierOne, c x₁⟫_ℝ ≤
        2 * params.multiplierBound ^ 2 := by
    have hinnerRho := mul_le_mul_of_nonneg_left hinnerBound hrho.le
    have hresidualBound :=
      mul_le_mul_of_nonneg_left hscaledResidual hboundNonneg
    nlinarith
  have hscaledResidualSq :
      (params.rho * ‖c x₁‖) ^ 2 ≤
        (2 * params.multiplierBound) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hrho.le (norm_nonneg _))
      (mul_nonneg (by norm_num) hboundNonneg)).2 hscaledResidual
  have hconstraintContribution :
      ⟪multiplierOne, c x₁⟫_ℝ +
          params.rho / 2 * ‖c x₁‖ ^ 2 ≤
        4 * params.multiplierBound ^ 2 / params.rho := by
    apply (le_div_iff₀ hrho).2
    nlinarith
  have hconstantNonneg :
      0 ≤ LALM.multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [LALM.multiplierPrimalConstant_def]
    positivity
  have hstepSq : ‖step‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have hcorrection :
      (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖step‖ ^ 2 ≤
        (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * params.delta ^ 2 :=
    mul_le_mul_of_nonneg_left hstepSq
      (div_nonneg hconstantNonneg hrho.le)
  rw [finiteActiveLyapunov, LALM.augmentedLagrangian_def,
    LALM.initialPotentialBound_def]
  linarith

/-- Helper for Theorem 3.7: the actual first stopped transition has the
deterministic initial Lyapunov upper bound whenever the canonical prefix
invariant holds. -/
theorem canonicalFiniteLyapunov_one_le_initialPotentialBound
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (hK : 1 ≤ K) (omega : Ω) :
    canonicalFiniteLyapunov attempt 1 omega ≤
      LALM.initialPotentialBound h params := by
  let kZero : Fin K := ⟨0, by omega⟩
  have hprefixPos := canonicalPrefixLength_pos attempt hK omega
  have hkPrefix : kZero.1 < canonicalPrefixLength attempt omega := by
    dsimp only [kZero]
    omega
  have hactive : attempt.activeAt kZero.castSucc omega :=
    (activeAt_iff_lt_canonicalPrefixLength attempt omega kZero.1 kZero.isLt).2
      hkPrefix
  have hstep := invariant.step_bound omega kZero hkPrefix
  have hpointZero : attempt.point kZero.castSucc omega = x₀ := by
    unfold StoppedAttempt.point
    have hindex : kZero.castSucc =
        (⟨0, Nat.zero_lt_succ K⟩ : Fin (K + 1)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    rw [attempt.state_zero]
  have hdisplacement :
      attempt.point kZero.succ omega - x₀ = attempt.baseStep kZero omega := by
    unfold StoppedAttempt.baseStep
    rw [hpointZero]
  have hstepDistance :
      dist x₀ (attempt.point kZero.succ omega) ≤ params.delta := by
    calc
      dist x₀ (attempt.point kZero.succ omega) =
          dist (attempt.point kZero.succ omega) x₀ := dist_comm _ _
      _ = ‖attempt.point kZero.succ omega - x₀‖ := by rw [dist_eq_norm]
      _ = ‖attempt.baseStep kZero omega‖ := congrArg norm hdisplacement
      _ ≤ params.delta := hstep
  have hsegment :
      segment ℝ x₀ (attempt.point kZero.succ omega) ⊆ h.region := by
    intro y hy
    apply attempt.region_condition.thickening_subset
    apply Metric.mem_cthickening_of_dist_le y x₀ params.delta X
      attempt.initial_mem
    exact (Metric.mem_closedBall.mp
      (segment_subset_closedBall_left x₀
        (attempt.point kZero.succ omega) hy)).trans hstepDistance
  have hmultiplierZero := invariant.multiplier_bound omega kZero.castSucc (by
    change 0 ≤ canonicalPrefixLength attempt omega
    omega)
  have hmultiplierOne := invariant.multiplier_bound omega kZero.succ (by
    change 1 ≤ canonicalPrefixLength attempt omega
    exact hprefixPos)
  have hupdate := multiplier_succ_eq_actual_of_prefix_invariant
    attempt invariant omega kZero hkPrefix
  have hbridge :=
    canonicalFiniteLyapunov_succ_eq_transition_of_active
      attempt kZero omega hactive
  have hpoint := StoppedAttempt.point_succ_of_active attempt kZero omega hactive
  have hmultiplier :=
    StoppedAttempt.multiplier_succ_of_active attempt kZero omega hactive
  have hbaseStep :=
    StoppedAttempt.baseStep_eq_activeModelStep attempt kZero omega hactive
  rw [← hpoint, ← hmultiplier, ← hbaseStep] at hbridge
  have hinitial := finiteActiveLyapunov_le_initialPotentialBound h params
    (attempt.point kZero.succ omega)
    (attempt.multiplier kZero.castSucc omega)
    (attempt.multiplier kZero.succ omega)
    (attempt.baseStep kZero omega) hsegment hdisplacement hupdate hstep
    hmultiplierZero hmultiplierOne
  rw [← hbridge] at hinitial
  simpa only [kZero, Nat.zero_add] using hinitial

/-- Theorem 3.7: the actual endpoint of the canonical stopped prefix has the
uniform Lyapunov lower bound. This includes the first endpoint outside `X`,
which remains inside the buffered regularity region. -/
theorem canonicalFiniteLyapunov_lowerBound_of_prefixInvariant
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (hK : 1 ≤ K) (omega : Ω) :
    LALM.lyapunovLowerBound h params ≤
      canonicalFiniteLyapunov attempt
        (canonicalPrefixLength attempt omega) omega := by
  let N : ℕ := canonicalPrefixLength attempt omega
  have hNpos : 1 ≤ N := by
    simpa only [N] using canonicalPrefixLength_pos attempt hK omega
  have hNle : N ≤ K := by
    simpa only [N] using canonicalPrefixLength_le attempt omega
  let k : Fin K := ⟨N - 1, by omega⟩
  have hkprefix : k.1 < canonicalPrefixLength attempt omega := by
    dsimp only [k, N]
    omega
  have hactive : attempt.activeAt k.castSucc omega :=
    (activeAt_iff_lt_canonicalPrefixLength attempt omega k.1 k.isLt).2
      hkprefix
  have hendpointRegion :=
    endpoint_mem_region_of_prefix_invariant attempt invariant omega k hkprefix
  have hpoint := StoppedAttempt.point_succ_of_active attempt k omega hactive
  have hendpointIndex :
      k.succ = (⟨N, Nat.lt_succ_iff.mpr hNle⟩ : Fin (K + 1)) := by
    apply Fin.ext
    change (N - 1) + 1 = N
    omega
  have hx : canonicalPointNat attempt N omega ∈ h.region := by
    rw [canonicalPointNat_eq_point attempt N hNle omega]
    rw [← hendpointIndex, hpoint]
    exact hendpointRegion
  have hmultiplier :
      ‖canonicalMultiplierNat attempt N omega‖ ≤ params.multiplierBound := by
    rw [canonicalMultiplierNat_eq_multiplier attempt N hNle omega]
    apply invariant.multiplier_bound omega
      (⟨N, Nat.lt_succ_iff.mpr hNle⟩ : Fin (K + 1))
    exact le_rfl
  have hlower := finiteActiveLyapunov_lowerBound h params
    (canonicalPointNat attempt N omega)
    (canonicalMultiplierNat attempt N omega)
    (canonicalPreviousStep attempt N omega) hx hmultiplier
  simpa only [canonicalFiniteLyapunov, N] using hlower

/-- Helper for Theorem 3.7: after the canonical active prefix, every padded
base-step square vanishes by the absorbing stopped transition. -/
theorem activeBaseStepIntegrand_eq_zero_of_canonicalPrefix_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (k : ℕ)
    (hkPrefix : canonicalPrefixLength attempt omega ≤ k) (hkK : k < K) :
    activeBaseStepIntegrand attempt k omega = 0 := by
  let kFin : Fin K := ⟨k, hkK⟩
  have hnotActive : ¬ attempt.activeAt kFin.castSucc omega := by
    have hindex : kFin.castSucc =
        (⟨k, Nat.lt_succ_of_lt hkK⟩ : Fin (K + 1)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    rw [activeAt_iff_lt_canonicalPrefixLength attempt omega k hkK]
    exact Nat.not_lt_of_ge hkPrefix
  have hfrozen :=
    StoppedAttempt.frozen_successor_of_inactive attempt kFin omega hnotActive
  rw [activeBaseStepIntegrand, dif_pos hkK]
  change ‖attempt.baseStep kFin omega‖ ^ 2 = 0
  rw [hfrozen.2.2, norm_zero]
  norm_num

/-- Helper for Theorem 3.7: after the canonical active prefix, every padded
clipped-estimator error square vanishes without reading an inactive oracle
transition. -/
theorem activeGradientErrorIntegrand_eq_zero_of_canonicalPrefix_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (k : ℕ)
    (hkPrefix : canonicalPrefixLength attempt omega ≤ k) (hkK : k < K) :
    activeGradientErrorIntegrand attempt k omega = 0 := by
  have hnotActive :
      ¬ attempt.activeAt ⟨k, Nat.lt_succ_of_lt hkK⟩ omega := by
    rw [activeAt_iff_lt_canonicalPrefixLength attempt omega k hkK]
    exact Nat.not_lt_of_ge hkPrefix
  rw [activeGradientErrorIntegrand, dif_pos hkK, if_neg hnotActive]

/-- Helper for Theorem 3.7: the actual index-zero base-step square is bounded
by the localization radius recorded in the canonical prefix invariant. -/
theorem canonicalInitialBaseStepIntegrand_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (hK : 1 ≤ K) (omega : Ω) :
    activeBaseStepIntegrand attempt 0 omega ≤ (params.delta : ℝ) ^ 2 := by
  let kZero : Fin K := ⟨0, by omega⟩
  have hprefixPos := canonicalPrefixLength_pos attempt hK omega
  have hstep : ‖attempt.baseStep kZero omega‖ ≤ params.delta :=
    invariant.step_bound omega kZero (by
      dsimp only [kZero]
      omega)
  rw [activeBaseStepIntegrand, dif_pos (by omega : 0 < K)]
  change ‖attempt.baseStep kZero omega‖ ^ 2 ≤ (params.delta : ℝ) ^ 2
  exact (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep

/-- Theorem 3.7: the finite stopped prefix invariant implies the positive-index
Lyapunov descent claimed for the actual canonical stopped trajectory. -/
theorem canonicalFiniteLyapunovDescent_of_prefixInvariant
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (omega : Ω) {k : ℕ}
    (hkPos : 1 ≤ k)
    (hkPrefix : k < canonicalPrefixLength attempt omega) :
    canonicalFiniteLyapunov attempt (k + 1) omega ≤
      canonicalFiniteLyapunov attempt k omega -
        (params.beta / 4) * activeBaseStepIntegrand attempt k omega +
        LALM.StochasticRun.lyapunovErrorConstant h params *
          (activeGradientErrorIntegrand attempt k omega +
            activeGradientErrorIntegrand attempt (k - 1) omega) := by
  have hprefixLe : canonicalPrefixLength attempt omega ≤ K :=
    canonicalPrefixLength_le attempt omega
  have hK : 1 ≤ K := by omega
  let previous : Fin K := ⟨k - 1, by omega⟩
  let current : Fin K := ⟨k, by omega⟩
  have hpreviousPrefix : previous.1 < canonicalPrefixLength attempt omega := by
    dsimp only [previous]
    omega
  have hcurrentPrefix : current.1 < canonicalPrefixLength attempt omega := by
    dsimp only [current]
    exact hkPrefix
  have hactivePrevious : attempt.activeAt previous.castSucc omega :=
    (activeAt_iff_lt_canonicalPrefixLength attempt omega previous.1 previous.isLt).2
      hpreviousPrefix
  have hactiveCurrent : attempt.activeAt current.castSucc omega :=
    (activeAt_iff_lt_canonicalPrefixLength attempt omega current.1 current.isLt).2
      hcurrentPrefix
  have hprevSucc : previous.succ = current.castSucc := by
    apply Fin.ext
    change (k - 1) + 1 = k
    omega
  have hpointPreviousSucc :
      attempt.point previous.succ omega =
        attempt.point previous.castSucc omega + attempt.baseStep previous omega := by
    unfold StoppedAttempt.baseStep
    calc
      attempt.point previous.succ omega =
          (attempt.point previous.succ omega - attempt.point previous.castSucc omega) +
            attempt.point previous.castSucc omega :=
        (sub_add_cancel (attempt.point previous.succ omega)
          (attempt.point previous.castSucc omega)).symm
      _ = attempt.point previous.castSucc omega +
          (attempt.point previous.succ omega - attempt.point previous.castSucc omega) :=
        add_comm _ _
  have hpoint :
      attempt.point current.castSucc omega =
        attempt.point previous.castSucc omega + attempt.baseStep previous omega := by
    rw [← hprevSucc]
    exact hpointPreviousSucc
  have hpointCurrentSucc :
      attempt.point current.succ omega =
        attempt.point current.castSucc omega + attempt.baseStep current omega := by
    unfold StoppedAttempt.baseStep
    module
  have hpreviousStep : ‖attempt.baseStep previous omega‖ ≤ params.delta :=
    invariant.step_bound omega previous hpreviousPrefix
  have hcurrentStep : ‖attempt.baseStep current omega‖ ≤ params.delta :=
    invariant.step_bound omega current hcurrentPrefix
  have hpreviousMultiplier :
      ‖attempt.multiplier previous.castSucc omega‖ ≤ params.multiplierBound := by
    apply invariant.multiplier_bound omega previous.castSucc
    change k - 1 ≤ canonicalPrefixLength attempt omega
    omega
  have hcurrentMultiplier :
      ‖attempt.multiplier current.castSucc omega‖ ≤ params.multiplierBound := by
    apply invariant.multiplier_bound omega current.castSucc
    change k ≤ canonicalPrefixLength attempt omega
    omega
  have hmultiplierPreviousUpdate :=
    multiplier_succ_eq_actual_of_prefix_invariant attempt invariant omega previous
      hpreviousPrefix
  have hmultiplierUpdate :
      attempt.multiplier current.castSucc omega =
        baseNextMultiplier c params.rho
          (attempt.point previous.castSucc omega)
          (attempt.multiplier previous.castSucc omega)
          (attempt.baseStep previous omega) := by
    rw [baseNextMultiplier_def, ← hpointPreviousSucc, ← hprevSucc]
    exact hmultiplierPreviousUpdate
  have hpreviousPointMem : attempt.point previous.castSucc omega ∈ X :=
    StoppedAttemptAnalysis.point_mem_of_active attempt previous.castSucc omega
      hactivePrevious
  have hcurrentPointMem : attempt.point current.castSucc omega ∈ X :=
    StoppedAttemptAnalysis.point_mem_of_active attempt current.castSucc omega
      hactiveCurrent
  have hsegmentPrevious := segment_subset_region_of_mem_X_of_step_bound attempt
    (attempt.point previous.castSucc omega) (attempt.baseStep previous omega)
    hpreviousPointMem hpreviousStep
  have hsegmentCurrent := segment_subset_region_of_mem_X_of_step_bound attempt
    (attempt.point current.castSucc omega) (attempt.baseStep current omega)
    hcurrentPointMem hcurrentStep
  have hpreviousMinimizes :=
    activeBaseStep_minimizes_model_of_active attempt previous omega hactivePrevious
  have hcurrentMinimizes :=
    activeBaseStep_minimizes_model_of_active attempt current omega hactiveCurrent
  have hdescent :=
    baseFiniteLyapunovDescent_of_adjacentTransitions
      (f := f) (c := c) h params
      (attempt.point previous.castSucc omega)
      (attempt.point current.castSucc omega)
      (attempt.multiplier previous.castSucc omega)
      (attempt.multiplier current.castSucc omega)
      (clippedEstimateAt h oracle Q B b previous.1
        (attempt.state previous.castSucc omega, attempt.batch previous.1 omega))
      (clippedEstimateAt h oracle Q B b current.1
        (attempt.state current.castSucc omega, attempt.batch current.1 omega))
      (attempt.baseStep previous omega) (attempt.baseStep current omega)
      hpreviousMinimizes hcurrentMinimizes hpoint hmultiplierUpdate
      hsegmentPrevious hsegmentCurrent hpreviousStep hcurrentStep
      hpreviousMultiplier hcurrentMultiplier
  have hnextMultiplierCurrentActual :
      attempt.multiplier current.succ omega =
        baseNextMultiplier c params.rho
          (attempt.point current.castSucc omega)
          (attempt.multiplier current.castSucc omega)
          (attempt.baseStep current omega) := by
    rw [baseNextMultiplier_def, ← hpointCurrentSucc]
    exact multiplier_succ_eq_actual_of_prefix_invariant attempt invariant omega
      current hcurrentPrefix
  have hlyapunovCurrent :=
    canonicalFiniteLyapunov_succ_eq_finiteState_of_active attempt current omega
      hactiveCurrent
  have hlyapunovPrevious :=
    canonicalFiniteLyapunov_succ_eq_finiteState_of_active attempt previous omega
      hactivePrevious
  have hpreviousIndex : previous.1 + 1 = k := by
    dsimp only [previous]
    omega
  have hlyapunovAtK :
      canonicalFiniteLyapunov attempt k omega =
        finiteActiveLyapunov h params
          (attempt.point previous.succ omega)
          (attempt.multiplier previous.succ omega)
          (attempt.baseStep previous omega) := by
    simpa only [hpreviousIndex] using hlyapunovPrevious
  have hcurrentStateLyapunov :
      finiteActiveLyapunov h params
          (attempt.point current.castSucc omega)
          (attempt.multiplier current.castSucc omega)
          (attempt.baseStep previous omega) =
        canonicalFiniteLyapunov attempt k omega := by
    simpa only [hprevSucc] using hlyapunovAtK.symm
  have hcurrentStepEnergy :=
    activeBaseStepIntegrand_eq_stepSquare_of_active attempt current omega
      hactiveCurrent
  have hcurrentErrorEnergy :=
    activeGradientErrorIntegrand_eq_gradientErrorSquare_of_active attempt current
      omega hactiveCurrent
  have hpreviousErrorEnergy :=
    activeGradientErrorIntegrand_eq_gradientErrorSquare_of_active attempt previous
      omega hactivePrevious
  have hcurrentCanonicalLyapunov :
      canonicalFiniteLyapunov attempt (k + 1) omega =
        finiteActiveLyapunov h params
          (attempt.point current.castSucc omega + attempt.baseStep current omega)
          (baseNextMultiplier c params.rho
            (attempt.point current.castSucc omega)
            (attempt.multiplier current.castSucc omega)
            (attempt.baseStep current omega))
          (attempt.baseStep current omega) := by
    rw [← hpointCurrentSucc, ← hnextMultiplierCurrentActual]
    simpa only [current] using hlyapunovCurrent
  calc
    canonicalFiniteLyapunov attempt (k + 1) omega =
        finiteActiveLyapunov h params
          (attempt.point current.castSucc omega + attempt.baseStep current omega)
          (baseNextMultiplier c params.rho
            (attempt.point current.castSucc omega)
            (attempt.multiplier current.castSucc omega)
            (attempt.baseStep current omega))
          (attempt.baseStep current omega) := hcurrentCanonicalLyapunov
    _ ≤ finiteActiveLyapunov h params
          (attempt.point current.castSucc omega)
          (attempt.multiplier current.castSucc omega)
          (attempt.baseStep previous omega) -
        (params.beta / 4) * ‖attempt.baseStep current omega‖ ^ 2 +
        LALM.StochasticRun.lyapunovErrorConstant h params *
          (‖clippedEstimateAt h oracle Q B b current.1
              (attempt.state current.castSucc omega, attempt.batch current.1 omega) -
            gradient f (attempt.point current.castSucc omega)‖ ^ 2 +
            ‖clippedEstimateAt h oracle Q B b previous.1
              (attempt.state previous.castSucc omega, attempt.batch previous.1 omega) -
            gradient f (attempt.point previous.castSucc omega)‖ ^ 2) := hdescent
    _ = canonicalFiniteLyapunov attempt k omega -
        (params.beta / 4) * activeBaseStepIntegrand attempt k omega +
        LALM.StochasticRun.lyapunovErrorConstant h params *
          (activeGradientErrorIntegrand attempt k omega +
            activeGradientErrorIntegrand attempt (k - 1) omega) := by
      rw [hcurrentStateLyapunov, ← hcurrentStepEnergy, ← hcurrentErrorEnergy,
        ← hpreviousErrorEnergy]

/-- Theorem 3.7: the analytic certificate for the actual finite stopped path is
exactly its step and multiplier prefix invariant. The Lyapunov descent and the
initial and terminal rank bounds are consequences, not independent fields. -/
structure CanonicalFiniteStoppedPathCertificate
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    where
  /-- The actual stopped prefix obeys the step and multiplier bounds. -/
  invariant : FiniteStoppedPrefixInvariant attempt

/-- Theorem 3.7: a finite stopped prefix invariant supplies the complete
canonical path certificate. -/
theorem canonicalFiniteStoppedPathCertificate_of_prefixInvariant
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
  (invariant : FiniteStoppedPrefixInvariant attempt) :
    CanonicalFiniteStoppedPathCertificate attempt :=
  ⟨invariant⟩

/-- Theorem 3.7: the canonical stopped attempt carries its analytic path
certificate without an additional pathwise-bound assumption. -/
theorem canonicalFiniteStoppedPathCertificate
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    CanonicalFiniteStoppedPathCertificate attempt :=
  canonicalFiniteStoppedPathCertificate_of_prefixInvariant attempt
    (finiteStoppedPrefixInvariant attempt)

/-- Helper for Theorem 3.7: a canonical certificate supplies the finite
Lyapunov telescope data on the exact stopped prefix. -/
noncomputable def finitePrefixLyapunovData_of_canonicalCertificate
    (certificate : CanonicalFiniteStoppedPathCertificate attempt)
    (hK : 1 ≤ K) (omega : Ω) :
    FinitePrefixLyapunovData (h := h) (params := params)
      (canonicalPrefixLength attempt omega) := by
  refine {
    lyapunov := fun k ↦ canonicalFiniteLyapunov attempt k omega
    stepEnergy := fun k ↦ activeBaseStepIntegrand attempt k omega
    errorEnergy := fun k ↦ activeGradientErrorIntegrand attempt k omega
    lyapunov_one_le_initial := ?_
    lyapunov_lower_le_terminal := ?_
    descent := ?_
  }
  · exact canonicalFiniteLyapunov_one_le_initialPotentialBound
      attempt certificate.invariant hK omega
  · exact canonicalFiniteLyapunov_lowerBound_of_prefixInvariant
      attempt certificate.invariant hK omega
  · intro k hkPos hkPrefix
    exact canonicalFiniteLyapunovDescent_of_prefixInvariant attempt
      certificate.invariant omega hkPos hkPrefix

/-- Theorem 3.7: a canonical certificate constructs the abstract stopped-path
witness from the actual absorbing state, prefix, Lyapunov values, and energy
observables. -/
noncomputable def finiteStoppedPathWitness_of_canonicalCertificate
    (certificate : CanonicalFiniteStoppedPathCertificate attempt)
    (hK : 1 ≤ K) :
    FiniteStoppedPathWitness attempt := by
  refine {
    invariant := certificate.invariant
    prefixLength := canonicalPrefixLength attempt
    prefixLength_pos := canonicalPrefixLength_pos attempt hK
    prefixLength_le := canonicalPrefixLength_le attempt
    data := finitePrefixLyapunovData_of_canonicalCertificate certificate hK
    stepEnergy_eq_active := ?_
    errorEnergy_eq_active := ?_
    inactive_step_zero := ?_
    inactive_error_zero := ?_
    initial_step_bound := ?_
    initial_budget_nonneg := (initialStepBound_pos_of_stoppedAttempt attempt).le
  }
  · intro _omega _k _hk
    simp only [finitePrefixLyapunovData_of_canonicalCertificate]
  · intro _omega _k _hk
    simp only [finitePrefixLyapunovData_of_canonicalCertificate]
  · exact activeBaseStepIntegrand_eq_zero_of_canonicalPrefix_le attempt
  · exact activeGradientErrorIntegrand_eq_zero_of_canonicalPrefix_le attempt
  · intro omega
    simpa only [finitePrefixLyapunovData_of_canonicalCertificate] using
      canonicalInitialBaseStepIntegrand_le attempt certificate.invariant hK omega

/-- Theorem 3.7: the canonical finite Lyapunov telescope controls the objective
at the retained first-exit endpoint by the deterministic threshold and the
actual stopped clipped-estimator energy. -/
theorem canonicalObjectiveAtFirstExit_le
    (certificate : CanonicalFiniteStoppedPathCertificate attempt)
    (hK : 1 ≤ K) (omega : Ω)
    (hfailure : omega ∉ attempt.successEvent) :
    f (firstExitPointOfFailure attempt omega hfailure) ≤
      LALM.deterministicObjectiveBound h params +
        2 * LALM.StochasticRun.lyapunovErrorConstant h params *
          pathwiseGradientErrorEnergy attempt omega := by
  let N : ℕ := canonicalPrefixLength attempt omega
  let data := finitePrefixLyapunovData_of_canonicalCertificate
    certificate hK omega
  have hNpos : 1 ≤ N := by
    simpa only [N] using canonicalPrefixLength_pos attempt hK omega
  have hNle : N ≤ K := by
    simpa only [N] using canonicalPrefixLength_le attempt omega
  have hterminalData :=
    FinitePrefixLyapunovData.terminal_le_initial_plus_error data hNpos
      (by
        intro k hk
        simpa only [data, finitePrefixLyapunovData_of_canonicalCertificate] using
          activeBaseStepIntegrand_nonneg attempt k omega)
      (by
        intro k hk
        simpa only [data, finitePrefixLyapunovData_of_canonicalCertificate] using
          activeGradientErrorIntegrand_nonneg attempt k omega)
  have hterminal :
      canonicalFiniteLyapunov attempt N omega ≤
        LALM.initialPotentialBound h params +
          2 * LALM.StochasticRun.lyapunovErrorConstant h params *
            pathwiseGradientErrorEnergy attempt omega := by
    have hinitial := data.lyapunov_one_le_initial
    dsimp only [data, finitePrefixLyapunovData_of_canonicalCertificate] at hterminalData hinitial
    have hsubset : Finset.range N ⊆ Finset.range K := by
      intro k hk
      exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le
        (Finset.mem_range.mp hk) hNle)
    have hprefix :
        (∑ k ∈ Finset.range N,
            activeGradientErrorIntegrand attempt k omega) =
          ∑ k ∈ Finset.range K,
            activeGradientErrorIntegrand attempt k omega := by
      exact Finset.sum_subset hsubset (fun k hkK hkN ↦ by
        apply activeGradientErrorIntegrand_eq_zero_of_canonicalPrefix_le
          attempt omega k
        · exact Nat.not_lt.mp (by
            intro hk
            exact hkN (Finset.mem_range.mpr hk))
        · exact Finset.mem_range.mp hkK)
    have hterminalData' :
        canonicalFiniteLyapunov attempt N omega ≤
          canonicalFiniteLyapunov attempt 1 omega +
            2 * LALM.StochasticRun.lyapunovErrorConstant h params *
              (∑ k ∈ Finset.range N,
                activeGradientErrorIntegrand attempt k omega) := by
      simpa only [N] using hterminalData
    have hinitial' :
        canonicalFiniteLyapunov attempt 1 omega ≤
          LALM.initialPotentialBound h params := by
      simpa only [N] using hinitial
    rw [hprefix] at hterminalData'
    change canonicalFiniteLyapunov attempt N omega ≤
      LALM.initialPotentialBound h params +
        2 * LALM.StochasticRun.lyapunovErrorConstant h params *
          (∑ k ∈ Finset.range K,
            activeGradientErrorIntegrand attempt k omega)
    nlinarith
  have hspec := StoppedAttempt.firstExitEndpoint_spec_of_failure
    attempt omega hfailure
  let tau : ℕ := StoppedAttempt.firstExitEndpoint attempt omega
  have htauLe : tau ≤ K := by
    simpa only [tau] using hspec.2.1
  have hN_eq_tau : N = tau := by
    dsimp only [N, canonicalPrefixLength, tau]
    exact min_eq_right htauLe
  have hpoint :
      canonicalPointNat attempt N omega =
        firstExitPointOfFailure attempt omega hfailure := by
    rw [canonicalPointNat_eq_point attempt N hNle omega]
    unfold firstExitPointOfFailure
    apply congrArg (fun j : Fin (K + 1) ↦ attempt.point j omega)
    apply Fin.ext
    exact hN_eq_tau
  have hmultiplier :
      ‖canonicalMultiplierNat attempt N omega‖ ≤ params.multiplierBound := by
    rw [canonicalMultiplierNat_eq_multiplier attempt N hNle omega]
    exact certificate.invariant.multiplier_bound omega
      (⟨N, Nat.lt_succ_iff.mpr hNle⟩ : Fin (K + 1)) le_rfl
  have hobjective := objective_le_finiteActiveLyapunov_add_multiplierCorrection
    h params (canonicalPointNat attempt N omega)
      (canonicalMultiplierNat attempt N omega)
      (canonicalPreviousStep attempt N omega) hmultiplier
  have hobjective' :
      f (firstExitPointOfFailure attempt omega hfailure) ≤
        finiteActiveLyapunov h params
            (canonicalPointNat attempt N omega)
            (canonicalMultiplierNat attempt N omega)
            (canonicalPreviousStep attempt N omega) +
          params.multiplierBound ^ 2 / (2 * params.rho) := by
    rw [← hpoint]
    exact hobjective
  rw [deterministicObjectiveBound_def]
  have hcanonical :
      finiteActiveLyapunov h params
          (canonicalPointNat attempt N omega)
          (canonicalMultiplierNat attempt N omega)
          (canonicalPreviousStep attempt N omega) =
        canonicalFiniteLyapunov attempt N omega := rfl
  rw [hcanonical] at hobjective'
  nlinarith [hobjective', hterminal]

/-- Theorem 3.7: every finite stopped path carried by a canonical certificate
inherits the objective bound at its actual first-exit endpoint. -/
theorem finiteStoppedObjectiveExitBound_of_canonicalCertificate
    (certificate : CanonicalFiniteStoppedPathCertificate attempt)
    (hK : 1 ≤ K) (path : FiniteStoppedPath attempt) :
    FiniteStoppedObjectiveExitBound path := by
  refine { objective_le := ?_ }
  intro omega hfailure
  exact canonicalObjectiveAtFirstExit_le certificate hK omega hfailure

/-- Theorem 3.7: the canonical analytic certificate yields the pathwise
energy interface with exactly the initial and error coefficients used by the
finite stopped localization proof. -/
theorem finiteStoppedPath_exists_of_canonicalCertificate
    (certificate : CanonicalFiniteStoppedPathCertificate attempt)
    (hK : 1 ≤ K) :
    ∃ path : FiniteStoppedPath attempt,
      path.baseStepBudget = LALM.StochasticRun.initialStepBound h params ∧
        path.errorStepCoefficient =
          LALM.StochasticRun.errorStepConstant h params := by
  exact finiteStoppedPath_exists_of_witness
    (finiteStoppedPathWitness_of_canonicalCertificate certificate hK)

/-- Theorem 3.7: the actual finite prefix invariant alone yields the pathwise
energy interface with the TeX coefficients. -/
theorem finiteStoppedPath_exists_of_prefixInvariant
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (hK : 1 ≤ K) :
    ∃ path : FiniteStoppedPath attempt,
      path.baseStepBudget = LALM.StochasticRun.initialStepBound h params ∧
        path.errorStepCoefficient =
          LALM.StochasticRun.errorStepConstant h params := by
  exact finiteStoppedPath_exists_of_canonicalCertificate
    (canonicalFiniteStoppedPathCertificate_of_prefixInvariant attempt invariant) hK

/-- Theorem 3.7: every nontrivial canonical stopped attempt realizes the finite
pathwise energy interface with the TeX coefficients. -/
theorem finiteStoppedPath_exists
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (hK : 1 ≤ K) :
    ∃ path : FiniteStoppedPath attempt,
      path.baseStepBudget = LALM.StochasticRun.initialStepBound h params ∧
        path.errorStepCoefficient =
          LALM.StochasticRun.errorStepConstant h params := by
  exact finiteStoppedPath_exists_of_canonicalCertificate
    (canonicalFiniteStoppedPathCertificate attempt) hK

/-- Theorem 3.7: a canonical stopped attempt supplies both a finite path and
the source-shaped first-exit objective certificate. -/
theorem finiteStoppedObjectiveExitBound_exists
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (hK : 1 ≤ K) :
    ∃ path : FiniteStoppedPath attempt, FiniteStoppedObjectiveExitBound path := by
  obtain ⟨path, _hbudget, _hcoefficient⟩ := finiteStoppedPath_exists attempt hK
  exact ⟨path,
    finiteStoppedObjectiveExitBound_of_canonicalCertificate
      (canonicalFiniteStoppedPathCertificate attempt) hK path⟩

/-- Theorem 3.7: the canonical finite geometry produces the Markov exit
control with the prescribed `Γe / confidence` threshold. -/
theorem finiteStoppedExitControl_exists_of_canonicalAttempt
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (hK : 1 ≤ K) (confidence_pos : 0 < confidence) :
    ∃ path : FiniteStoppedPath attempt,
      ∃ control : FiniteStoppedExitControl path,
        control.threshold =
          LALM.StochasticRun.errorAverageConstant h oracle params /
            confidence := by
  obtain ⟨path, _hbudget, _hcoefficient⟩ := finiteStoppedPath_exists attempt hK
  obtain ⟨control, hthreshold⟩ :=
    finiteStoppedExitControl_exists_of_objectiveExitBound path
      (finiteStoppedObjectiveExitBound_of_canonicalCertificate
        (canonicalFiniteStoppedPathCertificate attempt) hK path)
      confidence_pos
  exact ⟨path, control, hthreshold⟩

end LALM.FiniteStopped.StoppedAttemptAnalysis

end
