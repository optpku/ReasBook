/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Theorem_12_1_4

noncomputable section

open Filter

section

variable {n m : ℕ}

local notation "Point" => LagrangeNewtonPoint n
local notation "Multiplier" => LagrangeNewtonMultiplier m
local notation "Method" => _root_.LagrangeNewtonMethod Point Multiplier

-- Domain sampling:
-- * primary domain: local asymptotic convergence rates for equality-constrained
--   Lagrange-Newton primal-dual iterates;
-- * inspected owner declarations in the minimal semantic closure:
--   - `HasQuadraticConvergenceTo`
--   - `LagrangeNewtonMethod.primalDualIterate`
--   - `lagrangeNewtonMethod_primalDualIterate_hasQuadraticConvergenceTo`
--   - `lagrangeNewtonMethod_primalDualError_isBigO_square`
-- * source/core/bridge triage:
--   - source-facing layer: the textbook scalar error quantity
--     `‖x_k - xStar‖ + ‖λ_k - lambdaStar‖` from Lemma 12.1.5;
--   - core/canonical layer: the Chapter 03 convergence owner
--     `HasQuadraticConvergenceTo method.primalDualIterate (xStar, lambdaStar)`;
--   - bridge/view layer: the source `=O[atTop]` product estimate for that scalar
--     error quantity;
-- * best owner abstraction: the generated sequence is already owned by
--   `LagrangeNewtonMethod.primalDualIterate`, so this file keeps only the source-facing
--   scalar bridge theorem and does not introduce a second local error owner;
-- * primitive data vs. derived API:
--   - primitive data are the fixed `problem`, `method`, `(xStar, lambdaStar)`, and the
--     Theorem 12.1.4 hypotheses;
--   - the scalar sum-of-norms estimate in this file is derived API built on the existing
--     primal-dual convergence owner.

section Lemma1215

variable (problem : EqualityConstrainedProblem n m) (method : Method)
variable (xStar : Point) (lambdaStar : Multiplier)
variable
  (hMethod :
    method.IsFor problem (fun x lam ↦ hessianMatrixAt (fun y ↦ problem.lagrangian y lam) x))
  (hObjectiveContDiffOn :
    ∃ s : Set Point, s ∈ nhds xStar ∧ ContDiffOn ℝ 3 problem.objective s)
  (hConstraintContDiffOn :
    ∃ s : Set Point, s ∈ nhds xStar ∧ ContDiffOn ℝ 3 problem.constraintVector s)
  (hIterateTendsto : Tendsto method.iterate atTop (nhds xStar))
  (hFullColumnRank :
    Function.Injective <| Matrix.toEuclideanLin (problem.constraintGradientMatrix xStar))
  (hSecondOrderSufficient :
    problem.toStandardPenaltyProblem.SecondOrderSufficientCondition xStar lambdaStar)

include problem method xStar lambdaStar hMethod hObjectiveContDiffOn hConstraintContDiffOn
  hIterateTendsto hFullColumnRank hSecondOrderSufficient

/-- Chapter12 Lemma 12.1.5: under the assumptions of Theorem 12.1.4, the source scalar
primal-dual error quantity
`‖x_k - xStar‖ + ‖λ_k - lambdaStar‖`
satisfies
`‖x_(k + 1) - xStar‖ + ‖λ_(k + 1) - lambdaStar‖
  = O(‖x_k - xStar‖ * (‖x_k - xStar‖ + ‖λ_k - lambdaStar‖))`
along `atTop`, matching `(12.1.38)` and `(12.1.39)`. This is a source-facing bridge theorem
above the canonical owner `HasQuadraticConvergenceTo method.primalDualIterate (xStar, lambdaStar)`
from Theorem 12.1.4. -/
theorem lagrangeNewtonMethod_primalDualErrorSum_succ_isBigO_iterateError_mul_primalDualErrorSum
    :
    (fun k ↦
      ‖method.iterate (k + 1) - xStar‖ + ‖method.multiplier (k + 1) - lambdaStar‖) =O[atTop]
      (fun k ↦
        ‖method.iterate k - xStar‖ *
          (‖method.iterate k - xStar‖ + ‖method.multiplier k - lambdaStar‖)) := by
  sorry

end Lemma1215

end
