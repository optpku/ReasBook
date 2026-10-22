/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib
import Mathlib.LinearAlgebra.Matrix.PosDef
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Theorem_13_5_2

-- Semantic recall: Chapter 13 Theorem 13.5.1 already owns the source-facing CDT quadratic
-- model, feasible set, residual threshold, shifted Hessian, and multiplier conditions. This file
-- reuses that owner and adds the positive-semidefinite corollary.
--
-- Domain-style sampling for this corollary:
-- * primary domain: CDT quadratic trust-region subproblems with residual constraints;
-- * sampled owner declarations:
--   `IsCdtSolution`, `cdtFeasibleSet`, `existsCdtOptimalityMultipliers`,
--   and `IsCdtOptimalityPair` from `Theorem_13_5_1`,
--   `cdtGlobalSolution_of_optimalityPair_and_posSemidef` from `Theorem_13_5_2`,
--   `Matrix.PosSemidef`, `Matrix.PosSemidef.one`, and
--   `Matrix.posSemidef_self_mul_conjTranspose` from mathlib;
-- * owner choice:
--   `IsCdtSolution` is the source-facing owner,
--   `Matrix.PosSemidef` is the core/canonical PSD owner,
--   and `IsCdtOptimalityPair` remains the bridge/view layer;
-- * primitive vs derived split:
--   primal feasibility is primitive data on the right-hand side,
--   while multiplier existence is derived from a solution and suffices for optimality only
--   together with feasibility.

noncomputable section

section

variable {m n : ℕ}

local notation "StepVector" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintVector" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "JacobianMatrix" => Matrix (Fin n) (Fin m) ℝ

#print axioms cdtObjective
#print axioms cdtConstraintResidual
#print axioms cdtFeasibleSet
#print axioms cdtResidualNormValues
#print axioms cdtXiMin
#print axioms cdtShiftedHessian

/-- Chapter13 Corollary 13.5.3: under the source standing assumption `(13.5.10)`, formalized as
`cdtXiMin Δ c A < ξ`, and assuming that `B` is positive semidefinite, a step `dStar` is a global
solution of the CDT subproblem `(13.5.1)`-`(13.5.3)` if and only if it is feasible and there
exist nonnegative multipliers `lambdaStar` and `muStar` such that the optimality conditions
`(13.5.11)`-`(13.5.13)` hold, formalized by
`IsCdtOptimalityPair B g A c Δ ξ dStar lambdaStar muStar`. In this chapter's owner API, primal
feasibility is part of `IsCdtSolution` and is not bundled into `IsCdtOptimalityPair`. -/
theorem cdtGlobalSolution_iff_exists_optimalityPair_of_posSemidef
    {B : MatrixN} {g : StepVector} {A : JacobianMatrix} {c : ConstraintVector}
    {Δ ξ : ℝ} {dStar : StepVector}
    (hConstraintQualification : cdtXiMin Δ c A < ξ)
    (hB : B.PosSemidef) :
    IsCdtSolution B g A c Δ ξ dStar ↔
      dStar ∈ cdtFeasibleSet Δ ξ c A ∧
        ∃ lambdaStar muStar : ℝ, IsCdtOptimalityPair B g A c Δ ξ dStar lambdaStar muStar := by
  constructor
  · intro hSolution
    refine ⟨hSolution.1, ?_⟩
    exact existsCdtOptimalityMultipliers hB.isHermitian hConstraintQualification hSolution
  · rintro ⟨hFeasible, lambdaStar, muStar, hOptimality⟩
    refine cdtGlobalSolution_of_optimalityPair_and_posSemidef hFeasible hOptimality ?_
    have hI : (1 : MatrixN).PosSemidef := Matrix.PosSemidef.one
    have hAAT : (A * A.transpose).PosSemidef := by
      simpa using Matrix.posSemidef_self_mul_conjTranspose A
    simpa [cdtShiftedHessian, add_assoc] using
      (hB.add (hI.smul hOptimality.lambda_nonneg)).add (hAAT.smul hOptimality.mu_nonneg)

end
