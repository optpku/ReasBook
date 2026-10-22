/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.Stochastic

public section

open MeasureTheory
open scoped NNReal

namespace LALM.Correction

universe u

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Helper for Corollary 4.2: the corrected stochastic error-step coefficient
is strictly positive. -/
lemma errorStepConstant_pos
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    0 < errorStepConstant h params := by
  -- The positive proximal contribution dominates the nonnegative multiplier term.
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hfirst : 0 < (2 : ℝ) / params.beta := by positivity
  have hsecond :
      0 ≤ LALM.multiplierErrorConstant h / params.rho := by
    rw [LALM.multiplierErrorConstant_def]
    positivity
  have hlyapunov : 0 < lyapunovErrorConstant h params := by
    rw [lyapunovErrorConstant_def]
    exact add_pos_of_pos_of_nonneg hfirst hsecond
  rw [errorStepConstant_def]
  positivity

end LALM.Correction

namespace SPIDER.Correction

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ]
variable {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Helper for Corollary 4.2: the corrected scheduled inner batch absorbs the
SPIDER error coefficient, including the squared corrected displacement factor. -/
lemma scheduledErrorStepCoefficient_le_half
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Correction.Parameters h x₀ multiplier₀) (K : ℕ) :
    LALM.Correction.errorStepConstant h params *
        ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 *
          LALM.Correction.displacementFactor h params.delta ^ 2 /
            (innerBatchSize h oracle params K : ℝ)) ≤
      (1 : ℝ) / 2 := by
  -- The defining ceiling puts the full corrected threshold below the batch size.
  have hthresholdNonneg :
      0 ≤ 2 * LALM.Correction.errorStepConstant h params *
        oracle.meanSquareLipschitz ^ 2 *
          LALM.Correction.displacementFactor h params.delta ^ 2 *
            (SPIDER.refreshPeriod K : ℝ) := by
    positivity [LALM.Correction.errorStepConstant_pos h params]
  have hbatch :
      2 * LALM.Correction.errorStepConstant h params *
          oracle.meanSquareLipschitz ^ 2 *
            LALM.Correction.displacementFactor h params.delta ^ 2 *
              (SPIDER.refreshPeriod K : ℝ) ≤
        (innerBatchSize h oracle params K : ℝ) := by
    rw [innerBatchSize_coe, Nat.cast_max]
    exact (Nat.le_ceil _).trans (le_max_right _ _)
  have hb : 0 < (innerBatchSize h oracle params K : ℝ) := by positivity
  have hdivided :
      (2 * LALM.Correction.errorStepConstant h params *
          oracle.meanSquareLipschitz ^ 2 *
            LALM.Correction.displacementFactor h params.delta ^ 2 *
              (SPIDER.refreshPeriod K : ℝ)) /
          (innerBatchSize h oracle params K : ℝ) ≤ 1 := by
    calc
      (2 * LALM.Correction.errorStepConstant h params *
          oracle.meanSquareLipschitz ^ 2 *
            LALM.Correction.displacementFactor h params.delta ^ 2 *
              (SPIDER.refreshPeriod K : ℝ)) /
          (innerBatchSize h oracle params K : ℝ) ≤
          (innerBatchSize h oracle params K : ℝ) /
            (innerBatchSize h oracle params K : ℝ) :=
        (div_le_div_iff_of_pos_right hb).2 hbatch
      _ = 1 := div_self hb.ne'
  -- Rearrange the threshold quotient into the recursion coefficient.
  calc
    LALM.Correction.errorStepConstant h params *
        ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 *
          LALM.Correction.displacementFactor h params.delta ^ 2 /
            (innerBatchSize h oracle params K : ℝ)) =
        ((2 * LALM.Correction.errorStepConstant h params *
            oracle.meanSquareLipschitz ^ 2 *
              LALM.Correction.displacementFactor h params.delta ^ 2 *
                (SPIDER.refreshPeriod K : ℝ)) /
            (innerBatchSize h oracle params K : ℝ)) / 2 := by
      ring
    _ ≤ (1 : ℝ) / 2 :=
      div_le_div_of_nonneg_right hdivided (by norm_num)

end SPIDER.Correction

end
