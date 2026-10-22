/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Lemma_6_1_5

noncomputable section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling for this refine pass:
-- * primary domain: Chapter 6 trust-region predicted-reduction lower bounds;
-- * inspected project declarations:
--   `TrustRegionSubproblem.predictedReduction`,
--   `TrustRegionSubproblem.hasFractionCauchyDecrease`,
--   `TrustRegionSubproblem.cauchyPointPredictedReductionLowerBoundScaled`,
--   `TrustRegionSubproblem.predictedReductionLowerBound_of_hasFractionCauchyDecrease`;
-- * best owner abstraction: `TrustRegionSubproblem`;
-- * primitive data: the quadratic model, trust-region radius, gradient, and Hessian data owned
--   by `TrustRegionSubproblem`, together with the branch predicate
--   `P.hasFractionCauchyDecrease β₂ sk`;
-- * derived API: the source-facing existential constant extracted from the sharper owner-level
--   lower bound.
-- Source/core/bridge triage:
-- * source-facing: the exercise statement asserting existence of a reduction constant;
-- * core/canonical: `TrustRegionSubproblem` and
--   `predictedReductionLowerBound_of_hasFractionCauchyDecrease`;
-- * bridge/view: the existential reformulation proved here from the explicit owner-level bound.

namespace TrustRegionSubproblem

/-- Chapter06 Exercise 6.3: if `s_k` satisfies the fraction-of-Cauchy-decrease condition, then
there exists `β ∈ (0, 1]` such that
`q^(k) 0 - q^(k) (s_k) ≥ β * ‖g_k‖ * min {Δ_k, ‖g_k‖ / ‖B_k‖₂}`.
Here `q^(k)` is the quadratic model `P`, `‖B_k‖₂` is `P.hessianOperatorNorm`, and the source
branch hypothesis is the canonical owner predicate `P.hasFractionCauchyDecrease β₂ sk`. -/
theorem exists_predictedReductionConstant_of_hasFractionCauchyDecrease
    (P : TrustRegionSubproblem n) (β₂ : ℝ) (step : Point)
    (hβ₂ : β₂ ∈ Set.Ioc (0 : ℝ) 1)
    (hstep : P.hasFractionCauchyDecrease β₂ step) :
    ∃ β ∈ Set.Ioc (0 : ℝ) 1,
      β * ‖P.gradient‖ * min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) ≤
        P.predictedReduction step := by
  refine ⟨(1 / 2 : ℝ) * β₂, ?_, ?_⟩
  · constructor
    · nlinarith [hβ₂.1]
    · nlinarith [hβ₂.2]
  · simpa [mul_assoc, mul_left_comm, mul_comm] using
      P.predictedReductionLowerBound_of_hasFractionCauchyDecrease β₂ step hβ₂ hstep

end TrustRegionSubproblem
