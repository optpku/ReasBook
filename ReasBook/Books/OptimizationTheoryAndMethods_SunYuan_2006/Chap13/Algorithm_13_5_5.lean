/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Lemma_13_5_4

open Matrix

noncomputable section

section

variable {m n : ℕ}

local notation "StepVector" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintVector" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "JacobianMatrix" => Matrix (Fin n) (Fin m) ℝ

-- Semantic recall: `Theorem_13_5_1` owns the CDT model, feasible set, residual threshold, and
-- shifted Hessian, while `Lemma_13_5_4` owns the multiplier-generated step `d(λ, μ)`. This file
-- therefore stays at the source-facing algorithm layer and keeps only the branch logic and
-- stopping data explicit.
--
-- Domain-style sampling for this algorithm:
-- * primary domain: CDT trust-region subproblems with linearized-constraint bounds and the
--   multiplier-generated step search of Algorithm 13.5.5;
-- * sampled owner declarations:
--   `cdtFeasibleSet`, `cdtConstraintResidual`, and `cdtXiMin` from `Theorem_13_5_1`,
--   `cdtMultiplierStep` and `IsCdtMultiplierCase` from `Lemma_13_5_4`,
--   `IsCdtSolution` from `Theorem_13_5_1`;
-- * owner choice:
--   `Theorem_13_5_1` remains the source-facing CDT subproblem owner,
--   `Lemma_13_5_4` remains the bridge/view owner for the explicit step `d(λ, μ)`,
--   and this file keeps only the source-facing branch predicates and terminal stop data of
--   Algorithm 13.5.5;
-- * primitive vs derived split:
--   the primitive data here are the Step-3/4/5 branch conditions and the selected terminal
--   multipliers,
--   while feasibility of a candidate step is derived directly from
--   `cdtMultiplierStep B g A c lambdaStar muStar ∈ cdtFeasibleSet Δ ξ c A` and should not be
--   duplicated as a second owner.

/-- The Step-5 equation `(13.5.25)` is the trust-region boundary condition
`‖d(λ, μ)‖ - Δ = 0`. -/
def cdtStep5Eq1
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (Δ : ℝ) (lambdaStar muStar : ℝ) : ℝ :=
  ‖cdtMultiplierStep B g A c lambdaStar muStar‖ - Δ

/-- The Step-5 equation `(13.5.26)` is the linearized-constraint boundary condition
`‖c + Aᵀ d(λ, μ)‖ - ξ = 0`. -/
def cdtStep5Eq2
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (ξ : ℝ) (lambdaStar muStar : ℝ) : ℝ :=
  ‖cdtConstraintResidual c A (cdtMultiplierStep B g A c lambdaStar muStar)‖ - ξ

/-- The scalar Step-3 equation `ψ̄(λ, 0) = 0` from `(13.5.22)` is the restriction of the
trust-region boundary equation to `μ = 0`. -/
def cdtBarPsi
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (Δ : ℝ) (lambdaStar : ℝ) : ℝ :=
  cdtStep5Eq1 B g A c Δ lambdaStar 0

/-- The scalar Step-4 equation `ψ̂(0, μ) = 0` from `(13.5.24)` is the restriction of the
linearized-constraint boundary equation to `λ = 0`. -/
def cdtHatPsi
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (ξ : ℝ) (muStar : ℝ) : ℝ :=
  cdtStep5Eq2 B g A c ξ 0 muStar

/-- `cdtSolvesStep5System B g A c Δ ξ λ μ` means that `(λ, μ)` solves the coupled Step-5
system `(13.5.25)`-`(13.5.26)`, solved in the source by `(13.5.27)`. -/
def cdtSolvesStep5System
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (Δ ξ : ℝ) (lambdaStar muStar : ℝ) : Prop :=
  cdtStep5Eq1 B g A c Δ lambdaStar muStar = 0 ∧
    cdtStep5Eq2 B g A c ξ lambdaStar muStar = 0

/-- Algorithm 13.5.5 enters Step 3 exactly when `d(0, 0)` is infeasible and lies outside the
trust region, so the source Step-2 test does not branch directly to Step 4. -/
def cdtAlgorithm1355EntersStep3
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (Δ ξ : ℝ) : Prop :=
  cdtMultiplierStep B g A c 0 0 ∉ cdtFeasibleSet Δ ξ c A ∧
    Δ < ‖cdtMultiplierStep B g A c 0 0‖

/-- Algorithm 13.5.5 enters Step 4 either directly from Step 2 when `d(0, 0)` is infeasible but
already satisfies `‖d(0, 0)‖ ≤ Δ`, or after a Step-3 root `λ*` yields an infeasible
`d(λ*, 0)` on the positive-multiplier branch singled out by Lemma 13.5.4. -/
def cdtAlgorithm1355EntersStep4
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (Δ ξ : ℝ) : Prop :=
  (cdtMultiplierStep B g A c 0 0 ∉ cdtFeasibleSet Δ ξ c A ∧
      ‖cdtMultiplierStep B g A c 0 0‖ ≤ Δ) ∨
    ∃ lambdaStar : ℝ,
      cdtAlgorithm1355EntersStep3 B g A c Δ ξ ∧
        cdtBarPsi B g A c Δ lambdaStar = 0 ∧
        0 < lambdaStar ∧
        cdtMultiplierStep B g A c lambdaStar 0 ∉ cdtFeasibleSet Δ ξ c A

/-- Algorithm 13.5.5 enters Step 5 exactly when Step 4 has been reached and some Step-4 root
`μ*` on the positive-multiplier branch singled out by Lemma 13.5.4 yields an infeasible
`d(0, μ*)`. -/
def cdtAlgorithm1355EntersStep5
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (Δ ξ : ℝ) : Prop :=
  cdtAlgorithm1355EntersStep4 B g A c Δ ξ ∧
    ∃ muStar : ℝ,
      cdtHatPsi B g A c ξ muStar = 0 ∧
        0 < muStar ∧
        cdtMultiplierStep B g A c 0 muStar ∉ cdtFeasibleSet Δ ξ c A

/-- The terminal branch selected by Algorithm 13.5.5. -/
inductive CdtAlgorithm1355StopCase
  | atOrigin
  | atLambda
  | atMu
  | atLambdaMu
deriving DecidableEq

/-- The source stopping conditions attached to a selected terminal branch and its recorded
multipliers, with the active Step-3/4/5 branches restricted to the positive multipliers singled
out by Lemma 13.5.4. -/
def cdtAlgorithm1355StopCaseSpec
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (Δ ξ : ℝ) (stopCase : CdtAlgorithm1355StopCase) (lambdaStar muStar : ℝ) : Prop :=
  match stopCase with
  | .atOrigin =>
      cdtMultiplierStep B g A c 0 0 ∈ cdtFeasibleSet Δ ξ c A ∧ lambdaStar = 0 ∧ muStar = 0
  | .atLambda =>
      cdtAlgorithm1355EntersStep3 B g A c Δ ξ ∧
        cdtBarPsi B g A c Δ lambdaStar = 0 ∧
        0 < lambdaStar ∧
        cdtMultiplierStep B g A c lambdaStar 0 ∈ cdtFeasibleSet Δ ξ c A ∧
        muStar = 0
  | .atMu =>
      cdtAlgorithm1355EntersStep4 B g A c Δ ξ ∧
        cdtHatPsi B g A c ξ muStar = 0 ∧
        0 < muStar ∧
        cdtMultiplierStep B g A c 0 muStar ∈ cdtFeasibleSet Δ ξ c A ∧
        lambdaStar = 0
  | .atLambdaMu =>
      cdtAlgorithm1355EntersStep5 B g A c Δ ξ ∧
        0 < lambdaStar ∧
        0 < muStar ∧
        cdtSolvesStep5System B g A c Δ ξ lambdaStar muStar

/-- Chapter13 Algorithm 13.5.5: under the source input assumptions that `B` is positive definite,
`Δ > 0`, and `cdtXiMin Δ c A < ξ`, the algorithm computes the Step-2 candidate `d(0, 0)`. If
`d(0, 0)` is feasible, stop. If `d(0, 0)` is infeasible but `‖d(0, 0)‖ ≤ Δ`, go directly to
Step 4. Otherwise solve the specific Step-3 equation `cdtBarPsi B g A c Δ λ = 0`; if the
resulting `d(λ*, 0)` is feasible, stop. Next solve the specific Step-4 equation
`cdtHatPsi B g A c ξ μ = 0`; if the resulting `d(0, μ*)` is feasible, stop. If it is still
infeasible, solve the Step-5 system `cdtStep5Eq1 B g A c Δ λ μ = 0` and
`cdtStep5Eq2 B g A c ξ λ μ = 0`, corresponding to `(13.5.25)`-`(13.5.26)` solved in the source
by `(13.5.27)`. This structure records only the selected terminal branch and multipliers; the
input assumptions belong to later existence/correctness theorems, not to the stop-case data
itself. -/
structure CdtAlgorithm1355
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (Δ ξ : ℝ) : Type where
  stopCase : CdtAlgorithm1355StopCase
  lambdaStar : ℝ
  muStar : ℝ
  stopCaseSpec :
    cdtAlgorithm1355StopCaseSpec B g A c Δ ξ stopCase lambdaStar muStar

namespace CdtAlgorithm1355

variable
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector) (Δ ξ : ℝ)

/-- A `CdtAlgorithm1355` canonically coerces to its selected CDT step `d(λ*, μ*)`. -/
instance : Coe (@_root_.CdtAlgorithm1355 m n B g A c Δ ξ) StepVector where
  coe method := cdtMultiplierStep B g A c method.lambdaStar method.muStar

end CdtAlgorithm1355

#print axioms cdtConstraintResidual
#print axioms cdtFeasibleSet
#print axioms cdtXiMin
#print axioms cdtShiftedHessian
#print axioms cdtMultiplierStep
#print axioms cdtStep5Eq1
#print axioms cdtStep5Eq2
#print axioms cdtBarPsi
#print axioms cdtHatPsi
#print axioms cdtSolvesStep5System
#print axioms cdtAlgorithm1355EntersStep3
#print axioms cdtAlgorithm1355EntersStep4
#print axioms cdtAlgorithm1355EntersStep5
#print axioms cdtAlgorithm1355StopCaseSpec
#print axioms CdtAlgorithm1355

end
