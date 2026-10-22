/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Algorithm_13_4_1

-- Domain sampling:
-- * primary domain: Step-3 null-space trust-region predicted-reduction lower bounds in
--   Chapter 13;
-- * inspected project declarations:
--   `nullSpaceReducedGradient`,
--   `nullSpaceStoppingResidual`,
--   `nullSpaceTrialStepCondition`,
--   `TrustRegionSubproblem.predictedReductionLowerBound_of_hasFractionCauchyDecrease`;
-- * best owner abstraction: `nullSpaceTrialStepCondition`;
-- * primitive data: the single-stage null-space trial-step data `c`, `Z`, `g`, `Δ`, `APlus`,
--   `B`, `dHat`, together with `Pred_k`, `ρ₁`, and `ρ₂`;
-- * derived API: the exact `max`-packaged Step-3 lower bound extracted from the owner-level
--   constraint and reduced-gradient bounds, with the scalar `max` lemma itself using only the
--   two lower-bound inequalities it actually consumes.
-- Source/core/bridge triage:
-- * source-facing: `nullSpacePredictedReductionLowerBound`;
-- * core/canonical: `nullSpaceStoppingResidual`, `‖·‖₂`,
--   `nullSpaceTrialStepCondition`;
-- * bridge/view: the scalar Lemma 13.4.2 lower bound built from those owner-level quantities.

noncomputable section

section

open scoped Matrix.Norms.L2Operator

variable {ambientDim constraintDim tangentDim : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin ambientDim)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin constraintDim)
local notation "HessianMatrix" => Matrix (Fin ambientDim) (Fin ambientDim) ℝ
local notation "NullSpaceMatrix" => Matrix (Fin ambientDim) (Fin tangentDim) ℝ
local notation "PseudoInverseMatrix" => Matrix (Fin constraintDim) (Fin ambientDim) ℝ

/-- Chapter13 Lemma 13.4.2: if the predicted reduction dominates the two Step-3 lower bounds,
then it also dominates their maximum. The trust-region guard `‖dHat‖ ≤ Δ` belongs to the
owner-level condition `(13.4.27)`, but this scalar `max` consequence uses only the two lower-bound
inequalities themselves. -/
theorem nullSpacePredictedReductionLowerBound
    (predictedReduction ρ₁ ρ₂ : ℝ)
    (c : ConstraintPoint)
    (Z : NullSpaceMatrix)
    (g : Point)
    (trustRegionRadius : ℝ)
    (APlus : PseudoInverseMatrix)
    (B : HessianMatrix)
    (dHat : Point)
    (h_constraint :
      (if ‖APlus‖₂ = 0 then
        ρ₁ * ‖c‖
      else
        ρ₁ * min ‖c‖ (trustRegionRadius / ‖APlus‖₂)) ≤
        predictedReduction)
    (h_gradient :
      ρ₂ * min ‖nullSpaceReducedGradient Z g‖ 1 *
          min
            (Real.sqrt (trustRegionRadius ^ (2 : ℕ) - ‖dHat‖ ^ (2 : ℕ)))
            (‖nullSpaceReducedGradient Z g‖ / (1 + ‖B‖₂)) ≤
        predictedReduction) :
    max
        (if ‖APlus‖₂ = 0 then
          ρ₁ * ‖c‖
        else
          ρ₁ * min ‖c‖ (trustRegionRadius / ‖APlus‖₂))
        (ρ₂ * min ‖nullSpaceReducedGradient Z g‖ 1 *
          min
            (Real.sqrt (trustRegionRadius ^ (2 : ℕ) - ‖dHat‖ ^ (2 : ℕ)))
            (‖nullSpaceReducedGradient Z g‖ / (1 + ‖B‖₂))) ≤
      predictedReduction := by
  exact max_le h_constraint h_gradient

end
