/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Theorem_13_5_1

open Matrix

noncomputable section

-- Semantic recall: `Theorem_13_5_1` already owns the CDT quadratic model, feasible set,
-- residual threshold, and shifted Hessian on the Euclidean `ℓ2` surface. This lemma stays at the
-- bridge/view layer: it adds only the multiplier-generated step `d(λ, μ)` and the source case
-- split used later by Algorithm 13.5.5.
--
-- Domain-style sampling for this lemma:
-- * primary domain: CDT trust-region subproblems with residual constraints and multiplier
--   characterizations of global solutions;
-- * sampled owner declarations:
--   `IsCdtSolution`, `cdtFeasibleSet`, `cdtConstraintResidual`, and `cdtShiftedHessian` from
--   `Theorem_13_5_1`,
--   `cdtGlobalSolution_iff_exists_optimalityPair_of_posSemidef` from `Corollary_13_5_3`,
--   `IsMinOn` from mathlib;
-- * owner choice:
--   `IsCdtSolution` is the source-facing owner for “feasible and globally minimizing,”
--   while this file remains a bridge/view layer for the explicit multiplier step `d(λ, μ)` and
--   the source four-case split;
-- * primitive vs derived split:
--   the primitive data here are only the explicit step formula and the source case predicate,
--   while raw `IsMinOn` plus separate feasibility is derived API and should stay behind
--   `IsCdtSolution`.

section

variable {m n : ℕ}

local notation "StepVector" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintVector" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "JacobianMatrix" => Matrix (Fin n) (Fin m) ℝ

/-- The explicit multiplier-dependent step `d(λ, μ)` from `(13.5.20)`, viewed on the Euclidean
step space. -/
def cdtMultiplierStep
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (lambdaStar muStar : ℝ) : StepVector :=
  -Matrix.toEuclideanLin
      (cdtShiftedHessian B A lambdaStar muStar)⁻¹
      (g + muStar • Matrix.toEuclideanLin A c)

/-- The four source multiplier/activity alternatives in Lemma 13.5.4, expressed with the Euclidean
`ℓ2` norms on the step and residual spaces. -/
def IsCdtMultiplierCase
    (A : JacobianMatrix) (c : ConstraintVector) (Δ ξ : ℝ)
    (d : StepVector) (lambdaStar muStar : ℝ) : Prop :=
  (lambdaStar = 0 ∧ muStar = 0) ∨
    (0 < lambdaStar ∧ muStar = 0 ∧ ‖d‖ = Δ) ∨
    (lambdaStar = 0 ∧ 0 < muStar ∧ ‖cdtConstraintResidual c A d‖ = ξ) ∨
    (0 < lambdaStar ∧ 0 < muStar ∧ ‖d‖ = Δ ∧ ‖cdtConstraintResidual c A d‖ = ξ)

#print axioms cdtObjective
#print axioms cdtConstraintResidual
#print axioms cdtFeasibleSet
#print axioms cdtXiMin
#print axioms cdtShiftedHessian
#print axioms cdtMultiplierStep
#print axioms IsCdtMultiplierCase

/-- Chapter13 Lemma 13.5.4: under the standing assumption `(13.5.10)`, formalized as
`cdtXiMin Δ c A < ξ`, and assuming `B` is positive definite, the Euclidean-space step
`cdtMultiplierStep B g A c lambdaStar muStar`, formalizing `d(λ, μ)` from `(13.5.20)`, is a
solution of the CDT subproblem `(13.5.1)`-`(13.5.3)`, in the canonical owner sense
`IsCdtSolution`, if and only if it is feasible for `(13.5.2)`-`(13.5.3)` and one of the four
source multiplier cases holds. -/
theorem cdtMultiplierStep_isCdtSolution_iff_feasible_and_case_of_posDef
    {B : MatrixN} {g : StepVector} {A : JacobianMatrix} {c : ConstraintVector}
    {Δ ξ : ℝ} {lambdaStar muStar : ℝ}
    (hConstraintQualification : cdtXiMin Δ c A < ξ)
    (hB : B.PosDef) :
    IsCdtSolution
      B
      g
      A
      c
      Δ
      ξ
      (cdtMultiplierStep B g A c lambdaStar muStar) ↔
      cdtMultiplierStep B g A c lambdaStar muStar ∈ cdtFeasibleSet Δ ξ c A ∧
        IsCdtMultiplierCase
          A
          c
          Δ
          ξ
          (cdtMultiplierStep B g A c lambdaStar muStar)
          lambdaStar
          muStar := sorry

end
