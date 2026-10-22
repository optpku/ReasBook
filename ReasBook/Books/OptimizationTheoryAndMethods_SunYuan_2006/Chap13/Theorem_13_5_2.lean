/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.PosDef
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Theorem_13_5_1

-- Semantic recall: Chapter 13 Theorem 13.5.1 already owns the source-facing CDT quadratic
-- model, feasible set, residual threshold, shifted Hessian, and multiplier conditions. This file
-- reuses that owner and adds the positive-semidefinite sufficiency theorem.
--
-- Domain-style sampling for this theorem:
-- * primary domain: quadratic trust-region subproblems with norm constraints and matrix
--   positive-semidefiniteness;
-- * sampled owner declarations:
--   `IsCdtSolution`, `cdtConstraintResidual`, `cdtShiftedHessian`, and `IsCdtOptimalityPair`
--   from `Theorem_13_5_1`,
--   `IsMinOn` from mathlib,
--   `Matrix.PosSemidef` / `Matrix.PosSemidef.dotProduct_mulVec_nonneg` from mathlib;
-- * owner choice:
--   `Theorem_13_5_1` remains the source-facing CDT owner,
--   while `IsMinOn` and `Matrix.PosSemidef` are the core/canonical abstractions used in the
--   proof;
-- * primitive vs derived split:
--   the primitive data stay the CDT step, multipliers, and shifted Hessian,
--   and the global-minimizer conclusion is derived from that owner surface.

noncomputable section

section

variable {m n : ℕ}

local notation "StepVector" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintVector" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "JacobianMatrix" => Matrix (Fin n) (Fin m) ℝ

/-- Chapter13 Theorem 13.5.2: let `dStar` be a feasible point of the CDT subproblem with
objective `cdtObjective B g` and feasible set `cdtFeasibleSet Δ ξ c A`. If there exist
nonnegative multipliers `lambdaStar` and `muStar` satisfying the optimality conditions
`(13.5.11)`-`(13.5.13)`, and the shifted Hessian
`cdtShiftedHessian B A lambdaStar muStar = B + lambdaStar I + muStar A Aᵀ` is positive
semidefinite, then `dStar` is a global solution of the CDT subproblem. -/
theorem cdtGlobalSolution_of_optimalityPair_and_posSemidef
    {B : MatrixN} {g : StepVector} {A : JacobianMatrix} {c : ConstraintVector}
    {Δ ξ : ℝ} {dStar : StepVector} {lambdaStar muStar : ℝ}
    (hFeasible : dStar ∈ cdtFeasibleSet Δ ξ c A)
    (hOptimality : IsCdtOptimalityPair B g A c Δ ξ dStar lambdaStar muStar)
    (hPosSemidef : (cdtShiftedHessian B A lambdaStar muStar).PosSemidef) :
    IsCdtSolution B g A c Δ ξ dStar := by
  sorry

end
