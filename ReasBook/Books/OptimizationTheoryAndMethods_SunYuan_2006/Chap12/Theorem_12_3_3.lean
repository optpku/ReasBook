/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Assumption_12_3_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Assumption_12_3_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Definition_12_3_extra_1

noncomputable section

open Filter
open scoped BigOperators
open scoped StandardPenaltyProblem

section Chapter12Theorem1233

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Multiplier" => EuclideanSpace ℝ (Fin m)
local notation "∇" => @gradient ℝ Point _ _ _ _

-- This file reuses the canonical Assumption 12.3.1 / 12.3.2 owners together with the Chapter
-- 12 source-facing SQP step owner from `Definition_12_3_extra_1`, and adds only the projection
-- and error-ratio API needed for Theorem 12.3.3.

namespace StandardPenaltyProblem

/-- The Chapter 12 active-constraint value vector `ĉ(x)` with entries `c_i(x)` on
`E ∪ I(xStar)` and `0` on inactive constraints. -/
def activeConstraintValues
    (problem : StandardPenaltyProblem n m) (x xStar : Point) : Multiplier :=
  let _ : DecidablePred (fun i : Fin m ↦ i ∈ problem.activeConstraintSet xStar) :=
    Classical.decPred _
  ∑ i : Fin m,
    EuclideanSpace.single i
      (if i ∈ problem.activeConstraintSet xStar then problem.constraint i x else 0)

/-- On the active set `E ∪ I(xStar)`, `problem.activeConstraintValues x xStar`
recovers the constraint values `c_i(x)`. -/
theorem activeConstraintValues_of_mem_activeConstraintSet
    (problem : StandardPenaltyProblem n m) (x xStar : Point) {i : Fin m}
    (hi : i ∈ problem.activeConstraintSet xStar) :
    problem.activeConstraintValues x xStar i = problem.constraint i x := by
  sorry

/-- Outside `E ∪ I(xStar)`, `problem.activeConstraintValues x xStar` vanishes. -/
theorem activeConstraintValues_of_not_mem_activeConstraintSet
    (problem : StandardPenaltyProblem n m) (x xStar : Point) {i : Fin m}
    (hi : i ∉ problem.activeConstraintSet xStar) :
    problem.activeConstraintValues x xStar i = 0 := by
  sorry

/-- The canonical active Jacobian `A(x)` whose `i`-th active column is
`gradient (problem.constraint i) x` and whose inactive columns are `0`. -/
def activeConstraintJacobian
    (problem : StandardPenaltyProblem n m) (x xStar : Point) : Multiplier →L[ℝ] Point :=
  let _ : DecidablePred (fun i : Fin m ↦ i ∈ problem.activeConstraintSet xStar) :=
    Classical.decPred _
  ∑ i : Fin m,
    ((EuclideanSpace.proj i : Multiplier →L[ℝ] ℝ).smulRight
      (if i ∈ problem.activeConstraintSet xStar then
        ∇ (problem.constraint i) x
      else
        0))

/-- On active indices, the adjoint of `problem.activeConstraintJacobian x xStar` evaluates by the
constraint gradient `gradient (problem.constraint i) x`. -/
theorem activeConstraintJacobian_adjoint_apply_of_mem_activeConstraintSet
    (problem : StandardPenaltyProblem n m) (x xStar p : Point) {i : Fin m}
    (hi : i ∈ problem.activeConstraintSet xStar) :
    ((problem.activeConstraintJacobian x xStar).adjoint p) i =
      dotProduct p (∇ (problem.constraint i) x) := by
  sorry

/-- On inactive indices, the adjoint of `problem.activeConstraintJacobian x xStar` vanishes. -/
theorem activeConstraintJacobian_adjoint_apply_of_not_mem_activeConstraintSet
    (problem : StandardPenaltyProblem n m) (x xStar p : Point) {i : Fin m}
    (hi : i ∉ problem.activeConstraintSet xStar) :
    ((problem.activeConstraintJacobian x xStar).adjoint p) i = 0 := by
  sorry

/-- The canonical Chapter 12 projection `P_k`, viewed as the orthogonal projection onto
`ker ((problem.activeConstraintJacobian x xStar)ᵀ)`. -/
def activeConstraintNullspaceProjection
    (problem : StandardPenaltyProblem n m) (x xStar : Point) : Point →L[ℝ] Point :=
  ((problem.activeConstraintJacobian x xStar).adjoint.toLinearMap.ker).starProjection

/-- `problem.activeConstraintNullspaceProjection x xStar` lands in the nullspace of
`(problem.activeConstraintJacobian x xStar)ᵀ`. -/
theorem activeConstraintNullspaceProjection_mapsToKer
    (problem : StandardPenaltyProblem n m) (x xStar p : Point) :
    (problem.activeConstraintJacobian x xStar).adjoint
        (problem.activeConstraintNullspaceProjection x xStar p) = 0 := by
  sorry

/-- `problem.activeConstraintNullspaceProjection x xStar` fixes vectors already in
`ker ((problem.activeConstraintJacobian x xStar)ᵀ)`. -/
theorem activeConstraintNullspaceProjection_fixesKer
    (problem : StandardPenaltyProblem n m) (x xStar p : Point)
    (hp : (problem.activeConstraintJacobian x xStar).adjoint p = 0) :
    problem.activeConstraintNullspaceProjection x xStar p = p := by
  sorry

end StandardPenaltyProblem

/-- The projected model-error ratio from `(12.3.12)`,
`‖P_k ((B_k - W(x*, λ*)) (d_k))‖ / ‖d_k‖`. -/
def sqpProjectedHessianErrorRatio
    (P : ℕ → Point →L[ℝ] Point)
    (B : ℕ → Point →L[ℝ] Point)
    (WStar : Point →L[ℝ] Point)
    (d : ℕ → Point) : ℕ → ℝ :=
  fun k ↦ ‖P k ((B k - WStar) (d k))‖ / ‖d k‖

/-- Unfolding `sqpProjectedHessianErrorRatio P B WStar d k` gives the displayed quotient from
`(12.3.12)`. -/
theorem sqpProjectedHessianErrorRatio_apply
    (P : ℕ → Point →L[ℝ] Point)
    (B : ℕ → Point →L[ℝ] Point)
    (WStar : Point →L[ℝ] Point)
    (d : ℕ → Point) (k : ℕ) :
    sqpProjectedHessianErrorRatio P B WStar d k =
      ‖P k ((B k - WStar) (d k))‖ / ‖d k‖ :=
  rfl

/-- Chapter12 Theorem 12.3.3: under Assumptions 12.3.1 and 12.3.2 for the canonical active
Jacobian `problem.activeConstraintJacobian (x k) h1231.xStar`, active-constraint values
`problem.activeConstraintValues (x k) h1231.xStar`, and projection
`problem.activeConstraintNullspaceProjection (x k) h1231.xStar`, the SQP step sequence `d_k` is
superlinearly convergent in the sense of `(12.3.11)` if and only if the projected
Hessian-model error ratio `(12.3.12)` tends to `0`, with `W(h1231.xStar, h1231.lamStar)`
represented by the canonical owner
`problem.lagrangianHessianAt h1231.xStar h1231.lamStar`. -/
theorem hasSuperlinearlyConvergentStep_iff_projectedHessianErrorRatio_tendsto_zero
    (problem : StandardPenaltyProblem n m)
    (x g d : ℕ → Point)
    (B : ℕ → Point →L[ℝ] Point)
    (h1231 : HasSqpSuperlinearConvergenceAssumptions problem x)
    (hAssumption1232 :
      satisfiesEventualSqpSubproblemAssumption
        x
        h1231.xStar
        g
        B
        problem.activeConstraintJacobian
        problem.activeConstraintValues
        d) :
    HasSuperlinearlyConvergentStep x d h1231.xStar ↔
      Tendsto
        (sqpProjectedHessianErrorRatio
          (fun k ↦ problem.activeConstraintNullspaceProjection (x k) h1231.xStar)
          B
          (problem.lagrangianHessianAt h1231.xStar h1231.lamStar)
          d)
        atTop
        (nhds (0 : ℝ)) := by
  sorry

end Chapter12Theorem1233
