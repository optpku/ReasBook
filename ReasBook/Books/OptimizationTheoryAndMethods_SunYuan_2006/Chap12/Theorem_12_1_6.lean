/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Theorem_12_1_4

noncomputable section

open Filter
open scoped BigOperators

section

variable {n m : ℕ}

local notation "Point" => LagrangeNewtonPoint n
local notation "Multiplier" => LagrangeNewtonMultiplier m
local notation "Method" => _root_.LagrangeNewtonMethod Point Multiplier

-- Domain sampling:
-- * primary domain: local asymptotic convergence rates for the equality-constrained
--   Lagrange-Newton iterate sequence
-- * inspected owner declarations in the minimal semantic closure:
--   - `HasSuperlinearConvergenceTo`
--   - `HasQuadraticConvergenceTo`
--   - `lagrangeNewtonMethod_primalDualIterate_hasQuadraticConvergenceTo`
--   - `lagrangeNewtonMethod_primalDualError_isBigO_square`
-- * best owner abstraction:
--   `EqualityConstrainedProblem` owns the fixed optimization data,
--   `LagrangeNewtonMethod` owns the generated sequence, and the Chapter 03 convergence owner
--   `HasSuperlinearConvergenceTo` is the canonical public home for Theorem 12.1.6 (1)
-- * source/core/bridge triage:
--   - source-facing layer: the textbook higher-order error product formula `(12.1.41)`
--   - core/canonical layer: `HasSuperlinearConvergenceTo method.iterate xStar`
--   - bridge/view layer: the raw little-`o` error formula for part `(1)`
-- * primitive data vs derived API:
--   - primitive data here are exactly the Theorem 12.1.4 hypotheses on
--     `problem`, `method`, `xStar`, and `lambdaStar`
--   - derived API here are the superlinear-convergence owner and its source-formula
--     companions; this file keeps no second local convergence package

section Theorem1216

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

/-- Chapter12 Theorem 12.1.6 (1): under the assumptions of Theorem 12.1.4, the primal iterate
sequence `x_k` converges to `xStar` superlinearly in the canonical Chapter 03 sense. -/
theorem lagrangeNewtonMethod_iterate_converges_superlinearly
    : HasSuperlinearConvergenceTo method.iterate xStar := sorry

/-- Bridge form of Theorem 12.1.6 (1): the canonical superlinear-convergence owner on
`method.iterate` recovers the source little-`o` error formula
`‖x_(k + 1) - xStar‖ = o(‖x_k - xStar‖)` along `atTop`. -/
theorem lagrangeNewtonMethod_iterate_error_succ_isLittleO_iterateError
    :
    (fun k ↦ ‖method.iterate (k + 1) - xStar‖) =o[atTop]
      fun k ↦ ‖method.iterate k - xStar‖ :=
  (lagrangeNewtonMethod_iterate_converges_superlinearly
    problem method xStar lambdaStar hMethod hObjectiveContDiffOn hConstraintContDiffOn
    hIterateTendsto hFullColumnRank hSecondOrderSufficient).isLittleO

/-- Chapter12 Theorem 12.1.6 (2): under the assumptions of Theorem 12.1.4, for every natural
number `p`, formula `(12.1.41)` holds in the denominator-safe shifted form
`‖x_(k + p + 1) - xStar‖ = o(∏ j in Finset.range (p + 1), ‖x_(k + j) - xStar‖)` along
`atTop`; this is the same product of `p + 1` consecutive iterate errors as
`‖x_(k + 1) - xStar‖ = o(‖x_k - xStar‖ * ∏_{j = 1}^p ‖x_(k - j) - xStar‖)` after shifting the
index by `p`. The endpoint `p = 0` is exactly the part `(1)` little-`o` formula. -/
theorem lagrangeNewtonMethod_iterate_error_shifted_isLittleO_prod
    (p : ℕ) :
    (fun k ↦ ‖method.iterate (k + (p + 1)) - xStar‖) =o[atTop]
      (fun k ↦ Finset.prod (Finset.range (p + 1))
        (fun j ↦ ‖method.iterate (k + j) - xStar‖)) := sorry

end Theorem1216

#print axioms lagrangeNewtonStepSize
#print axioms lagrangeNewtonTrialPoint
#print axioms lagrangeNewtonTrialMultiplier

end
