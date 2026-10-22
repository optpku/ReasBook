/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7

noncomputable section

section Chapter08Theorem8216

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ
local notation "EPoint" => EuclideanSpace ℝ (Fin n)

open scoped BigOperators Gradient

namespace ConstrainedOptimizationProblem

-- Domain sampling:
-- * primary domain: first-order necessary conditions for constrained optimization
-- * sampled owners:
--   `ConstrainedOptimizationProblem.mem_iff` from Chapter 1
--   `ConstrainedOptimizationProblem.mem_feasibleSet_iff` from `Definition_8_1_1`
--   `ConstrainedOptimizationProblem.HasConstraintGradientsAt` from `Definition_8_2_2`
--   `ConstrainedOptimizationProblem.IsKKTPoint` from `Theorem_8_2_7`
--   mathlib's `DifferentiableAt.hasGradientAt`
-- * owner abstraction chosen here:
--   `source-facing`: `problem.IsFritzJohnPoint xStar lambdaZero lambda`
--   `core/canonical`: chapter feasibility `xStar ∈ problem` together with the chapter's
--   pointwise differentiability owners at `xStar`
--   `bridge/view`: derived equality- and inequality-constraint lemmas recovered from feasibility
-- * primitive data vs derived API:
--   feasibility is primitive through the existing constrained-problem owner; the pointwise
--   equality and inequality constraint formulas are derived API and should not be stored as
--   separate fields; likewise the local smoothness input belongs to the existing pointwise
--   differentiability owners rather than to a new neighborhood-level wrapper

/-- `problem.IsFritzJohnPoint xStar lambdaZero lambda` records the Fritz John multiplier
conditions at `xStar`: feasibility via the existing constrained-problem owner, differentiability
of the objective and every constraint at `xStar`, stationarity, dual feasibility on inequality
constraints, complementary slackness on inequality constraints, and nontriviality of the
multiplier pair `(lambdaZero, lambda)`. The equality and inequality constraint formulas are
recovered from `feasible`. -/
@[mk_iff]
class IsFritzJohnPoint
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lambdaZero : ℝ) (lambda : Fin m → ℝ) : Prop where
  feasible : xStar ∈ problem
  objectiveDifferentiableAt : DifferentiableAt ℝ problem.objective xStar
  hasConstraintGradientsAt : problem.HasConstraintGradientsAt xStar
  objectiveMultiplier_nonneg : 0 ≤ lambdaZero
  stationarity :
    lambdaZero • gradient problem.euclideanObjective (WithLp.toLp 2 xStar) -
        ∑ i : Fin m, lambda i • gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar) =
      0
  dualFeasible :
    ∀ i ∈ problem.ineqIndices, 0 ≤ lambda i
  complementarySlackness :
    ∀ i ∈ problem.ineqIndices, lambda i * problem.constraint i xStar = 0
  multipliers_not_all_zero :
    0 < lambdaZero ^ 2 + ∑ i : Fin m, (lambda i) ^ 2

/-- `problem.IsFritzJohnPoint xStar lambdaZero lambda` is a proposition. -/
instance instSubsingletonIsFritzJohnPoint
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lambdaZero : ℝ) (lambda : Fin m → ℝ) :
    Subsingleton (problem.IsFritzJohnPoint xStar lambdaZero lambda) :=
  inferInstance

/-- A Fritz John point satisfies all equality constraints. -/
theorem IsFritzJohnPoint.eq_constraints
    {problem : ConstrainedOptimizationProblem n m E I}
    {xStar : Point} {lambdaZero : ℝ} {lambda : Fin m → ℝ}
    (h : problem.IsFritzJohnPoint xStar lambdaZero lambda) :
    ∀ i ∈ problem.eqIndices, problem.constraint i xStar = 0 := by
  intro i hi
  exact (problem.mem_iff xStar).1 h.feasible |>.1 i hi

/-- A Fritz John point satisfies all inequality constraints. -/
theorem IsFritzJohnPoint.ineq_constraints
    {problem : ConstrainedOptimizationProblem n m E I}
    {xStar : Point} {lambdaZero : ℝ} {lambda : Fin m → ℝ}
    (h : problem.IsFritzJohnPoint xStar lambdaZero lambda) :
    ∀ i ∈ problem.ineqIndices, 0 ≤ problem.constraint i xStar := by
  exact (problem.mem_iff xStar).1 h.feasible |>.2

/-- Under the differentiability hypotheses carried by a Fritz John point, the Euclidean
Lagrangian gradient is the source stationarity expression. This is the bridge from the
source-facing Fritz John stationarity formula to the chapter's canonical KKT owner. -/
theorem gradient_euclideanLagrangian_eq_objective_sub_sum
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lambda : Fin m → ℝ)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar) :
    ∇ (problem.euclideanLagrangian lambda) (WithLp.toLp 2 xStar) =
      gradient problem.euclideanObjective (WithLp.toLp 2 xStar) -
        ∑ i : Fin m, lambda i • gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar) :=
  sorry

/-- A Fritz John multiplier family with strictly positive objective multiplier normalizes to the
canonical Chapter 8 KKT owner. -/
theorem IsFritzJohnPoint.toIsKKTPoint
    {problem : ConstrainedOptimizationProblem n m E I}
    {xStar : Point} {lambdaZero : ℝ} {lambda : Fin m → ℝ}
    (h : problem.IsFritzJohnPoint xStar lambdaZero lambda)
    (hlambdaZero : 0 < lambdaZero) :
    problem.IsKKTPoint xStar (fun i ↦ lambda i / lambdaZero) := by
  have hlambdaZero_ne : lambdaZero ≠ 0 := ne_of_gt hlambdaZero
  refine
    { feasible := h.feasible
      dualFeasible := ?_
      stationarity := ?_
      complementarySlackness := ?_ }
  · intro i hi
    exact div_nonneg (h.dualFeasible i hi) hlambdaZero.le
  · sorry
  · intro i hi
    calc
      (lambda i / lambdaZero) * problem.constraint i xStar
          = (lambda i * problem.constraint i xStar) * lambdaZero⁻¹ := by
              rw [div_eq_mul_inv, mul_assoc, mul_comm lambdaZero⁻¹, ← mul_assoc]
      _ = 0 := by rw [h.complementarySlackness i hi, zero_mul]

/-- If the objective multiplier is already normalized to `1`, the Fritz John conditions are the
canonical Chapter 8 KKT conditions with the same constraint multiplier vector. -/
theorem IsFritzJohnPoint.toIsKKTPoint_of_objectiveMultiplier_eq_one
    {problem : ConstrainedOptimizationProblem n m E I}
    {xStar : Point} {lambdaZero : ℝ} {lambda : Fin m → ℝ}
    (h : problem.IsFritzJohnPoint xStar lambdaZero lambda)
    (hlambdaZero : lambdaZero = 1) :
    problem.IsKKTPoint xStar lambda := by
  simpa [hlambdaZero] using h.toIsKKTPoint (hlambdaZero ▸ zero_lt_one)

end ConstrainedOptimizationProblem

/-- Chapter08 Theorem 8.2.16: if `xStar` is a feasible local minimizer of the constrained
problem `problem`, and the objective and every constraint function are differentiable at `xStar`,
then there exist a scalar multiplier `lambdaZero` and a vector multiplier `lambda` such that
`problem.IsFritzJohnPoint xStar lambdaZero lambda`. -/
theorem exists_fritzJohnMultipliers_of_isLocalMinOn
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar) :
    ∃ lambdaZero : ℝ, ∃ lambda : Fin m → ℝ,
      problem.IsFritzJohnPoint xStar lambdaZero lambda := by
  sorry

end Chapter08Theorem8216
