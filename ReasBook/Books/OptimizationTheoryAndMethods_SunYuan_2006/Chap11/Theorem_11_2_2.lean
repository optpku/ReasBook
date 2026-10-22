/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Order.Filter.AtTopBot.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Algorithm_11_2_1

noncomputable section

open Filter
open scoped BigOperators Matrix.Norms.Frobenius

section Chapter11Theorem1122

variable {basicDim nonbasicDim : ℕ}

local notation "BasicPoint" => EuclideanSpace ℝ (Fin basicDim)
local notation "NonbasicPoint" => EuclideanSpace ℝ (Fin nonbasicDim)
local notation "Point" => BasicPoint × NonbasicPoint

namespace VariableEliminationMethod

/-
Algorithm 11.2.1 itself now owns the split-space update, reduced-space objects, Step 2
specification, and the `VariableEliminationMethod` owner. This theorem file reuses those
declarations directly instead of maintaining a parallel local copy.
-/

local notation "Method" => @_root_.VariableEliminationMethod basicDim nonbasicDim

/-- The transpose Jacobian block `∂ c(x)ᵀ / ∂ x_B` at the split point `x = (x_B, x_N)`. -/
abbrev basicConstraintJacobianTransposeAt
    (method : Method) (x : Point) : Matrix (Fin basicDim) (Fin basicDim) ℝ :=
  (constraintJacobianB (fun xB xN ↦ method.constraint (xB, xN)) x.1 x.2).transpose

/-- The transpose Jacobian block `∂ c(x)ᵀ / ∂ x_N` at the split point `x = (x_B, x_N)`. -/
abbrev nonbasicConstraintJacobianTransposeAt
    (method : Method) (x : Point) : Matrix (Fin nonbasicDim) (Fin basicDim) ℝ :=
  (constraintJacobianN (fun xB xN ↦ method.constraint (xB, xN)) x.1 x.2).transpose

/-- The source matrix `((∇ c(x)ᵀ)ᵀ) * ∇ c(x)ᵀ`, written through the basic and nonbasic Step 2
transpose-Jacobian blocks. -/
def constraintGramAt
    (method : Method) (x : Point) : Matrix (Fin basicDim) (Fin basicDim) ℝ :=
  (method.basicConstraintJacobianTransposeAt x).transpose *
      method.basicConstraintJacobianTransposeAt x +
    (method.nonbasicConstraintJacobianTransposeAt x).transpose *
      method.nonbasicConstraintJacobianTransposeAt x

/-- The Step 2 stationarity residual
`∇ f(x_k) - ∇ c(x_k)ᵀ λ_k`, written in split coordinates with the Step 2 multiplier
`λ_k = method.multiplier k` and the recorded transpose Jacobian blocks `A_B(x_k)` and
`A_N(x_k)` from Algorithm 11.2.1. -/
def stationarityResidualAt
    (method : Method) (k : ℕ) : Point :=
  let x := method.iterate k
  ( partialGradientB (fun xB xN ↦ method.objective (xB, xN)) x.1 x.2 -
      Matrix.toEuclideanLin
        (method.basicJacobian k)
        (method.multiplier k)
  , partialGradientN (fun xB xN ↦ method.objective (xB, xN)) x.1 x.2 -
      Matrix.toEuclideanLin
        (method.nonbasicJacobian k)
        (method.multiplier k) )

/-- The normalized cosine factor for the angle between the Step 3 direction `d̄_k` and the
reduced gradient `g̃_k`. The source assumption `(11.2.24)` uses its square, so the sign
convention is immaterial. -/
def reducedDirectionCosine
    (method : Method) (k : ℕ) : ℝ :=
  -inner ℝ (method.direction k) (method.reducedGradient k) /
    (‖method.direction k‖ * ‖method.reducedGradient k‖)

/-- The inverse of `((∇ c(x)ᵀ)ᵀ) * ∇ c(x)ᵀ` is uniformly bounded on the feasible set `X`. -/
def uniformlyBoundedConstraintGramInverse
    (method : Method) : Prop :=
  ∃ C ∈ Set.Ici (0 : ℝ),
    ∀ x : Point, x ∈ method.feasibleSet →
      IsUnit (Matrix.det (method.constraintGramAt x)) ∧
        ‖(method.constraintGramAt x)⁻¹‖ ≤ C

/-- The source condition `(11.2.24)` is formalized by the divergence of the partial sums of
`(cos ⟨d̄_k, g̃_k⟩)^2` to `+∞`. The source indexing starts at `k = 1`, matching
`Finset.Icc 1 N`. -/
def reducedDirectionCosineSqPartialSumsDiverge
    (method : Method) : Prop :=
  Tendsto
    (fun N : ℕ ↦
      Finset.sum (Finset.Icc 1 N) fun k ↦ (method.reducedDirectionCosine k) ^ (2 : ℕ))
    atTop
    atTop

/-- At each active stage, the split stationarity residual has zero `x_B`-block and `g̃_k` as
its `x_N`-block by the Step 2 equations `(11.2.12)` and `(11.2.11)`. -/
theorem stationarityResidualAt_eq_zero_reducedGradient_of_active
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    method.stationarityResidualAt k = (0, method.reducedGradient k) := by
  rcases method.stepTwoSpec_of_active hk hactive with ⟨_, _, hBasic, hReduced⟩
  simp [VariableEliminationMethod.stationarityResidualAt, hBasic, hReduced]

/-- Chapter11 Theorem 11.2.2: assume that the objective `f(x)` and constraint map `c(x)` of a
run of Algorithm 11.2.1 are twice continuously differentiable. If the inverse of
`((∇ c(x)ᵀ)ᵀ) * ∇ c(x)ᵀ` is uniformly bounded on the feasible set `X`, then Algorithm 11.2.1
with exact line searches, the divergence condition `(11.2.24)`, and an infinite-run hypothesis
that every stage `k ≥ 1` remains active ensures that either the Step 2 stationarity residual
`∇ f(x_k) - ∇ c(x_k)ᵀ λ_k` built from the recorded Step 2 multiplier `λ_k = method.multiplier k`
has `liminf` norm equal to `0`, or the objective values satisfy `f(x_k) → -∞`. -/
theorem liminf_stationarityResidualNorm_eq_zero_or_objective_tendsto_atBot
    (method : Method)
    (hC2f : ContDiff ℝ 2 method.objective)
    (hC2c : ContDiff ℝ 2 method.constraint)
    (hBoundedInverse : method.uniformlyBoundedConstraintGramInverse)
    (hActive : ∀ k, 1 ≤ k → method.active k)
    (hCosine : method.reducedDirectionCosineSqPartialSumsDiverge) :
    liminf (fun k : ℕ ↦ ‖method.stationarityResidualAt k‖) atTop = 0 ∨
      Tendsto (fun k : ℕ ↦ method.objective (method.iterate k)) atTop atBot := sorry

#print axioms VariableEliminationMethod.basicConstraintJacobianTransposeAt
#print axioms VariableEliminationMethod.nonbasicConstraintJacobianTransposeAt
#print axioms VariableEliminationMethod.constraintGramAt
#print axioms VariableEliminationMethod.stationarityResidualAt
#print axioms variableEliminationUpdate
#print axioms variableEliminationReducedFeasibleSet
#print axioms variableEliminationReducedObjective
#print axioms variableEliminationLineSearchDomain

end VariableEliminationMethod

end Chapter11Theorem1122
