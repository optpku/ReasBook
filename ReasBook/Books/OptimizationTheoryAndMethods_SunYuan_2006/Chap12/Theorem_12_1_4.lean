/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Theorem_12_1_3

noncomputable section

open Filter

section

variable {n m : ℕ}

local notation "Point" => LagrangeNewtonPoint n
local notation "Multiplier" => LagrangeNewtonMultiplier m
local notation "Method" => _root_.LagrangeNewtonMethod Point Multiplier

-- Domain sampling:
-- * primary domain: local convergence-rate theory for equality-constrained
--   Lagrange-Newton sequences
-- * inspected owner declarations in the minimal semantic closure:
--   - `HasQuadraticConvergenceTo`
--   - `EqualityConstrainedProblem` and `EqualityConstrainedProblem.IsKKTPoint`
--   - `LagrangeNewtonMethod` together with `LagrangeNewtonMethod.IsFor`
--   - `StandardPenaltyProblem.SecondOrderSufficientCondition`
--   - `hessianMatrixAt` from Chapter 3 for the Euclidean matrix Hessian bridge
-- * source/core/bridge triage:
--   - source-facing layer: the textbook local assumptions and primal-dual convergence
--     conclusion for a fixed equality-constrained problem
--   - core/canonical layer: `HasQuadraticConvergenceTo`
--   - bridge/view layer: the source `=O[atTop]` formula `(12.1.34)` and the Chapter 3
--     Hessian-matrix bridge used only to specialize `method.IsFor`
-- * best owner abstraction: the fixed equality-constrained problem data are owned by
--   `EqualityConstrainedProblem`, the generated run is owned by `LagrangeNewtonMethod`, and
--   the canonical convergence owner is `HasQuadraticConvergenceTo`
-- * primitive data vs. derived API:
--   - primitive data here are the explicit source pair `(xStar, lambdaStar)`, the fixed
--     `problem`, the generated `method`, the local `C^3` neighborhood hypotheses, convergence
--     of `method.iterate`, and the rank condition on `problem.constraintGradientMatrix xStar`
-- The matrix field used in `method.IsFor` is derived from the Chapter 3 owner
-- `hessianMatrixAt`; this file keeps no second local Hessian bridge.

section Theorem1214

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

/-- Chapter12 Theorem 12.1.4 (2): under the same hypotheses, the primal-dual iterate sequence
`method.primalDualIterate` converges quadratically to the feasible stationary Lagrange pair
`(xStar, lambdaStar)`, in the canonical Chapter 3 sense that the next primal-dual error is `O`
of the square of the current error. -/
theorem lagrangeNewtonMethod_primalDualIterate_hasQuadraticConvergenceTo
    : HasQuadraticConvergenceTo method.primalDualIterate (xStar, lambdaStar) := sorry

/-- Chapter12 Theorem 12.1.4 (1): under the Theorem 12.1.4 hypotheses, the multiplier sequence
`λ_k` converges to `lambdaStar`. This is the multiplier-component companion to the canonical
quadratic-convergence owner on `method.primalDualIterate`. -/
theorem lagrangeNewtonMethod_multiplier_tendsto :
    Tendsto method.multiplier atTop (nhds lambdaStar) := by
  simpa [LagrangeNewtonMethod.primalDualIterate] using
    (lagrangeNewtonMethod_primalDualIterate_hasQuadraticConvergenceTo
      problem method xStar lambdaStar hMethod hObjectiveContDiffOn hConstraintContDiffOn
      hIterateTendsto hFullColumnRank hSecondOrderSufficient).tendsto.snd

/-- Companion bridge for Theorem 12.1.4 (2): the canonical quadratic-convergence owner on
`method.primalDualIterate` is exactly the source formula `(12.1.34)`, namely
`‖(x_(k + 1), λ_(k + 1)) - (xStar, lambdaStar)‖ =
  O(‖(x_k, λ_k) - (xStar, lambdaStar)‖^2)` along `atTop`. -/
theorem lagrangeNewtonMethod_primalDualError_isBigO_square
    : (fun k ↦ ‖method.primalDualIterate (k + 1) - (xStar, lambdaStar)‖) =O[atTop]
        fun k ↦ ‖method.primalDualIterate k - (xStar, lambdaStar)‖ ^ (2 : ℕ) :=
  (lagrangeNewtonMethod_primalDualIterate_hasQuadraticConvergenceTo
    problem method xStar lambdaStar hMethod hObjectiveContDiffOn hConstraintContDiffOn
    hIterateTendsto hFullColumnRank hSecondOrderSufficient).isBigO

end Theorem1214

end
