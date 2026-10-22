/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Order.Filter.EventuallyConst
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Corollary_13_6_5

noncomputable section

open Filter

section

variable {m n : ℕ}

-- Domain sampling for this refine pass:
-- * primary domain: Chapter 13 Powell-Yuan algorithmic stabilization of the Step-3 penalty
--   sequence;
-- * inspected owner declarations:
--   `Filter.EventuallyConst` and `Filter.eventuallyConst_atTop_nat` from mathlib,
--   `PowellYuanTrustRegionMethod.step3AcceptsAt`,
--   `PowellYuanTrustRegionMethod.sigmaCandidate_succ_eq`,
--   `PowellYuanTrustRegionMethod.sigma_eq_candidate_of_step3`, and
--   `PowellYuanTrustRegionMethod.constraintJacobian_eq_at` from `Algorithm_13_6_1`,
--   `powellYuanPredictedReductionLowerBound_of_smallConstraintResidual` from
--   `Corollary_13_6_5`;
-- * owner abstraction: the Chapter 13 method owner `PowellYuanTrustRegionMethod`;
-- * source/core/bridge triage:
--   - source-facing: eventual constancy of the recorded incoming Step-3 penalty parameters
--     `method.sigmaCandidate`
--   - core/canonical: `PowellYuanTrustRegionMethod`,
--     `powellYuanPredictedReductionLowerBound_of_smallConstraintResidual`, and
--     `Filter.EventuallyConst`
--   - bridge/view: direct reuse of Corollary 13.6.5 on the recorded method data when a
--     lower-bound witness is needed;
-- * primitive data vs derived API:
--   - primitive data: the recorded method fields, the Section 13.3 branch hypothesis, and the
--     identification of the recorded projected direction with the canonical `d̂_k`
--   - derived API: `terminatedAt`, `finitelyTerminates`, `step3AcceptsAt`, and the Corollary
--     13.6.5 lower-bound theorem reused on the method owner.

namespace PowellYuanTrustRegionMethod

local notation "Method" => @PowellYuanTrustRegionMethod m n

private theorem not_terminatedAt_of_not_finitelyTerminates
    (method : Method)
    (hNoTerminate : ¬ method.finitelyTerminates)
    {k : ℕ}
    (hk : 1 ≤ k) :
    ¬ method.terminatedAt k := by
  intro hk_term
  exact hNoTerminate ⟨k, hk, hk_term⟩

private theorem step3AcceptsAt_eventually_of_smallConstraintResidual
    (method : Method)
    (delta3 delta4 : ℝ)
    (hNoTerminate : ¬ method.finitelyTerminates)
    (h_projectedDirection :
      ∀ k : ℕ, 1 ≤ k →
        method.projectedDirection k =
          powellYuanHatDirection
            (powellYuanProjector (method.constraintJacobian k))
            (method.direction k))
    (h_delta4 : 0 ≤ delta4)
    (h_lowerBound :
      ∀ k : ℕ, 1 ≤ k →
        ‖method.constraintResidual k‖ ≤ delta3 * method.radius k →
          (method.sigmaCandidate k / 2 : ℝ) *
              powellYuanSigmaUpdateDenominator
                (method.constraintResidual k)
                (method.constraintJacobianAt (method.iterate k))
                (method.direction k) +
            delta4 * method.radius k ≤
              powellYuanPredictedReduction
                (method.gradient k)
                (method.hessianApproximation k)
                (method.constraintJacobianAt (method.iterate k))
                (method.constraintResidual k)
                (method.multiplier k)
                (method.trialMultiplier k)
                (method.sigmaCandidate k)
                (method.direction k)
                (powellYuanHatDirection
                  (powellYuanProjector
                    (method.constraintJacobianAt (method.iterate k)))
                  (method.direction k)))
    (h_smallResidual :
      ∀ᶠ k in atTop, ‖method.constraintResidual k‖ ≤ delta3 * method.radius k) :
    ∀ᶠ k in atTop, method.step3AcceptsAt k := by
  have h_one : ∀ᶠ k : ℕ in atTop, 1 ≤ k :=
    Filter.eventually_atTop.2 ⟨1, fun k hk ↦ hk⟩
  filter_upwards [h_one, h_smallResidual] with k hk hk_small
  have h_not_term :=
    not_terminatedAt_of_not_finitelyTerminates method hNoTerminate hk
  have h_jacobian := method.constraintJacobian_eq_at hk
  have h_predictedReduction :
      method.predictedReductionCandidate k =
        powellYuanPredictedReduction
          (method.gradient k)
          (method.hessianApproximation k)
          (method.constraintJacobianAt (method.iterate k))
          (method.constraintResidual k)
          (method.multiplier k)
          (method.trialMultiplier k)
          (method.sigmaCandidate k)
          (method.direction k)
          (powellYuanHatDirection
            (powellYuanProjector
              (method.constraintJacobianAt (method.iterate k)))
            (method.direction k)) := by
    simpa [h_jacobian, h_projectedDirection k hk] using
      method.predictedReductionCandidate_spec k hk h_not_term
  have h_radius_nonneg : 0 ≤ method.radius k :=
    le_of_lt (method.radius_pos k hk)
  have h_step :
      (method.sigmaCandidate k / 2 : ℝ) *
            powellYuanSigmaUpdateDenominator
              (method.constraintResidual k)
              (method.constraintJacobian k)
              (method.direction k) ≤
        (method.sigmaCandidate k / 2 : ℝ) *
              powellYuanSigmaUpdateDenominator
                (method.constraintResidual k)
                (method.constraintJacobian k)
                (method.direction k) +
            delta4 * method.radius k := by
    have h_nonneg : 0 ≤ delta4 * method.radius k :=
      mul_nonneg h_delta4 h_radius_nonneg
    linarith
  have h_lowerBound' :
      (method.sigmaCandidate k / 2 : ℝ) *
            powellYuanSigmaUpdateDenominator
              (method.constraintResidual k)
              (method.constraintJacobian k)
              (method.direction k) +
          delta4 * method.radius k ≤
        method.predictedReductionCandidate k := by
    calc
      (method.sigmaCandidate k / 2 : ℝ) *
            powellYuanSigmaUpdateDenominator
              (method.constraintResidual k)
              (method.constraintJacobian k)
              (method.direction k) +
          delta4 * method.radius k
        =
          (method.sigmaCandidate k / 2 : ℝ) *
              powellYuanSigmaUpdateDenominator
                (method.constraintResidual k)
                (method.constraintJacobianAt (method.iterate k))
                (method.direction k) +
            delta4 * method.radius k := by
              simp [h_jacobian]
      _ ≤
          powellYuanPredictedReduction
            (method.gradient k)
            (method.hessianApproximation k)
            (method.constraintJacobianAt (method.iterate k))
            (method.constraintResidual k)
            (method.multiplier k)
            (method.trialMultiplier k)
            (method.sigmaCandidate k)
            (method.direction k)
            (powellYuanHatDirection
              (powellYuanProjector
                (method.constraintJacobianAt (method.iterate k)))
              (method.direction k)) := h_lowerBound k hk hk_small
      _ = method.predictedReductionCandidate k := by
          symm
          exact h_predictedReduction
  rw [method.step3AcceptsAt_iff]
  exact le_trans h_step h_lowerBound'

private theorem sigmaCandidate_eventuallyConst_of_eventualStep3Accepts
    (method : Method)
    (hNoTerminate : ¬ method.finitelyTerminates)
    (h_eventualStep3Accepts : ∀ᶠ k in atTop, method.step3AcceptsAt k) :
    Filter.EventuallyConst method.sigmaCandidate atTop := by
  rw [Filter.eventuallyConst_atTop_nat]
  rcases Filter.eventually_atTop.1 h_eventualStep3Accepts with ⟨k0, hk0⟩
  refine ⟨max k0 1, ?_⟩
  intro k hk
  have hk0_le : k0 ≤ k := le_trans (le_max_left k0 1) hk
  have hk_one : 1 ≤ k := le_trans (le_max_right k0 1) hk
  have h_not_term :=
    not_terminatedAt_of_not_finitelyTerminates method hNoTerminate hk_one
  have h_step3 : method.step3AcceptsAt k := hk0 k hk0_le
  calc
    method.sigmaCandidate (k + 1) = method.sigma k :=
      method.sigmaCandidate_succ_eq hk_one h_not_term
    _ = method.sigmaCandidate k :=
      method.sigma_eq_candidate_of_step3 k hk_one h_not_term h_step3

/-- Chapter13 Lemma 13.6.6: for a Powell-Yuan trust-region run that does not terminate finitely,
if the recorded projected directions are the canonical `d̂_k`, the Corollary 13.6.5 lower bound
holds for explicit constants `δ₃` and nonnegative `δ₄`, and the small-residual tail hypothesis
holds with the
same `δ₃`, then the incoming Step-3 penalty parameters `σ_k`, represented by
`method.sigmaCandidate k`, are eventually constant. By
`Filter.eventuallyConst_atTop_nat`, this is equivalent to the tail identity
`σ_(k+1) = σ_k` for all sufficiently large indices. -/
theorem penaltyParameters_eventuallyConstant
    (method : Method)
    (delta3 delta4 : ℝ)
    (hNoTerminate : ¬ method.finitelyTerminates)
    (h_projectedDirection :
      ∀ k : ℕ, 1 ≤ k →
        method.projectedDirection k =
          powellYuanHatDirection
            (powellYuanProjector (method.constraintJacobian k))
            (method.direction k))
    (h_delta4 : 0 ≤ delta4)
    (h_lowerBound :
      ∀ k : ℕ, 1 ≤ k →
        ‖method.constraintResidual k‖ ≤ delta3 * method.radius k →
          (method.sigmaCandidate k / 2 : ℝ) *
              powellYuanSigmaUpdateDenominator
                (method.constraintResidual k)
                (method.constraintJacobianAt (method.iterate k))
                (method.direction k) +
            delta4 * method.radius k ≤
              powellYuanPredictedReduction
                (method.gradient k)
                (method.hessianApproximation k)
                (method.constraintJacobianAt (method.iterate k))
                (method.constraintResidual k)
                (method.multiplier k)
                (method.trialMultiplier k)
                (method.sigmaCandidate k)
                (method.direction k)
                (powellYuanHatDirection
                  (powellYuanProjector
                    (method.constraintJacobianAt (method.iterate k)))
                  (method.direction k)))
    (h_smallResidual :
      ∀ᶠ k in atTop,
        ‖method.constraintResidual k‖ ≤ delta3 * method.radius k) :
    Filter.EventuallyConst method.sigmaCandidate atTop := by
  exact
    sigmaCandidate_eventuallyConst_of_eventualStep3Accepts
      method
      hNoTerminate
      (step3AcceptsAt_eventually_of_smallConstraintResidual
        method
        delta3
        delta4
        hNoTerminate
        h_projectedDirection
        h_delta4
        h_lowerBound
        h_smallResidual)

end PowellYuanTrustRegionMethod

end
