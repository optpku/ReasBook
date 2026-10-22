/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Remark_13_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_7_1

noncomputable section

open Filter
open scoped CompositeNonsmooth

local notation "Point" => EuclideanSpace ℝ (Fin 2)

-- Domain-style sampling:
-- * primary domain: norm-parametric composite nonsmooth trust-region methods on Euclidean space,
--   specialized here to the `ℓ∞` trust-region constraint from Exercise 14.10;
-- * inspected upstream owners in the minimal closure:
--   `linftyNorm`,
--   `trustRegionPenaltyFeasibleSet`,
--   `CompositeNonsmoothOptimizationProblem`,
--   `compositeNonsmoothJacobianTranspose`,
--   `DF[problem](x, d)`,
--   `compositeNonsmoothTrustRegionModel`,
--   `trustRegionPredictedReduction`,
--   `IsCompositeNonsmoothTrustRegionSolution`,
--   `CompositeNonsmoothTrustRegionMethod`,
--   `IsCompositeNonsmoothAcceptedStepMultiplier`,
--   and mathlib's `IsMinOn`;
-- * source-facing data kept local: the two smooth branches, the outer `max`, the explicit
--   source Hessian matrices, and the initial point/radius;
-- * bridge/view layer in this file: the exercise specializes the Chapter 14.7 method owner to
--   `ρ = linftyNorm`, `problem = exercise1410Problem eps`, and the source initial data;
-- * core/canonical owners reused: the Chapter 14 composite-problem/model/method API, the
--   Chapter 13 trust-region feasible-set owner, and the Chapter 01 `linftyNorm` owner.
-- Primitive data are the branch map, outer `max`, and component Hessians. The Jacobian,
-- directional-value, `DF`, the trust-region subproblem predicate, the trust-region method API,
-- and the `ℓ∞` feasible-set surface are derived from those owners rather than stored as parallel
-- local definitions.

/-- The objective from Chapter14 Exercise 14.10 is
`x ↦ max {1 + x₁ - x₂^2, 1 - x₁ + (1 + eps) * x₂^2}` on `ℝ^2`. -/
def exercise1410Objective (eps : ℝ) (x : Point) : ℝ :=
  max
    (1 + x 0 - (x 1) ^ (2 : ℕ))
    (1 - x 0 + (1 + eps) * (x 1) ^ (2 : ℕ))

/-- Unfolding `exercise1410Objective eps x` gives the source maximum formula. -/
theorem exercise1410Objective_eq
    (eps : ℝ) (x : Point) :
    exercise1410Objective eps x =
      max
        (1 + x 0 - (x 1) ^ (2 : ℕ))
        (1 - x 0 + (1 + eps) * (x 1) ^ (2 : ℕ)) := sorry

/-- At the origin, the objective value from Chapter14 Exercise 14.10 is `1`. -/
theorem exercise1410Objective_zero (eps : ℝ) :
    exercise1410Objective eps (0 : Point) = 1 := sorry

/-- The first smooth branch in Chapter14 Exercise 14.10 is `x ↦ 1 + x₁ - x₂^2`. -/
def exercise1410FirstBranch (x : Point) : ℝ :=
  1 + x 0 - (x 1) ^ (2 : ℕ)

/-- The second smooth branch in Chapter14 Exercise 14.10 is
`x ↦ 1 - x₁ + (1 + eps) * x₂^2`. -/
def exercise1410SecondBranch (eps : ℝ) (x : Point) : ℝ :=
  1 - x 0 + (1 + eps) * (x 1) ^ (2 : ℕ)

/-- The outer function for the Exercise 14.10 composite objective is the coordinatewise maximum
on `ℝ²`. -/
def exercise1410OuterMax (y : Point) : ℝ :=
  max (y 0) (y 1)

/-- The smooth map for Exercise 14.10 packages the two branch functions whose outer maximum is the
objective. -/
def exercise1410SmoothMap (eps : ℝ) (x : Point) : Point :=
  !₂[exercise1410FirstBranch x, exercise1410SecondBranch eps x]

/-- Unfolding `exercise1410Objective eps x` through the explicit two-branch composite data gives
`exercise1410OuterMax (exercise1410SmoothMap eps x)`. -/
theorem exercise1410Objective_eq_outerMax_smoothMap
    (eps : ℝ) (x : Point) :
    exercise1410Objective eps x =
      exercise1410OuterMax (exercise1410SmoothMap eps x) := sorry

/-- Exercise 14.10 as a composite nonsmooth optimization problem with smooth map
`exercise1410SmoothMap eps` and outer function `exercise1410OuterMax`. -/
def exercise1410Problem (eps : ℝ) : CompositeNonsmoothOptimizationProblem 2 2 where
  smoothMap := exercise1410SmoothMap eps
  outerFunction := exercise1410OuterMax
  smoothMap_contDiff := by sorry
  outerFunction_convex := by sorry

/-- Evaluating the canonical composite-problem owner for Exercise 14.10 recovers the source
objective. -/
@[simp] theorem exercise1410Problem_apply
    (eps : ℝ) (x : Point) :
    exercise1410Problem eps x = exercise1410Objective eps x := by
  simpa [exercise1410Problem] using (exercise1410Objective_eq_outerMax_smoothMap eps x).symm

/-- For Exercise 14.10, the canonical Jacobian-transpose owner for
`exercise1410SmoothMap eps` is the explicit source matrix `A(x) = ∇ f(x)ᵀ`. -/
theorem exercise1410JacobianTranspose_eq
    (eps : ℝ) (x : Point) :
    compositeNonsmoothJacobianTranspose (exercise1410SmoothMap eps) x =
      !![(1 : ℝ), -1; -(2 * x 1), 2 * (1 + eps) * x 1] := sorry

/-- The Hessian of the first smooth branch in Exercise 14.10. -/
def exercise1410FirstComponentHessian : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(0 : ℝ), 0; 0, -2]

/-- The Hessian of the second smooth branch in Exercise 14.10. -/
def exercise1410SecondComponentHessian (eps : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(0 : ℝ), 0; 0, 2 * (1 + eps)]

/-- The source matrix `B_k = λ₀ ∇²f₁(x_k) + λ₁ ∇²f₂(x_k)` from `(14.7.7)` specialized to
Exercise 14.10. -/
def exercise1410HessianApproximation (eps : ℝ) (weights : Point) : Matrix (Fin 2) (Fin 2) ℝ :=
  weights 0 • exercise1410FirstComponentHessian +
    weights 1 • exercise1410SecondComponentHessian eps

/-- The source starting point is `(delta, delta^2)`. -/
def exercise1410InitialPoint (delta : ℝ) : Point :=
  !₂[delta, delta ^ (2 : ℕ)]

/-- The source initial trust-region radius is `0.5 * delta`. -/
def exercise1410InitialRadius (delta : ℝ) : ℝ :=
  (1 / 2 : ℝ) * delta

/-- The canonical Chapter 13 `ℓ∞` norm owner on the coordinate realization `d.ofLp`
specializes in `ℝ²` to `max {|d₁|, |d₂|}`. -/
theorem exercise1410LinftyNorm_eq (d : Point) :
    ‖d.ofLp‖∞ = max ‖d 0‖ ‖d 1‖ := sorry

local notation "Method" => CompositeNonsmoothTrustRegionMethod 2 2 linftyNorm

/-- Chapter14 Exercise 14.10: there exist positive smallness thresholds for the objective
parameter `eps` and the initial-point parameter `delta` such that every norm-parametric Chapter
14.7 trust-region run specialized to `ρ = linftyNorm`, to the exact two-branch max objective
`exercise1410Objective eps = max {1 + x₁ - x₂^2, 1 - x₁ + (1 + eps) * x₂^2}`, and to the source
initial data `x₁ = (delta, delta^2)` and `Δ₁ = 0.5 * delta`, where positivity of `delta` is
already forced by the canonical method owner together with `Δ₁ > 0`, and which remains on the Step-2
continuation branch `ε < ‖d_k.ofLp‖∞` at every stage `k ≥ 1`, has iterate sequence
`k ↦ x_(k + 1)` that converges linearly but not superlinearly to the origin. -/
theorem linftyTrustRegionMethod_onlyLinearConvergence_atOrigin_of_smallParameters :
    ∃ eps0 delta0 : ℝ, 0 < min eps0 delta0 ∧
      ∀ {eps delta : ℝ} (method : Method)
        (hε : 0 < eps)
        (hproblem : method.problem = exercise1410Problem eps)
        (hinitialPoint : method.initialPoint = exercise1410InitialPoint delta)
        (hinitialRadius : method.initialRadius = exercise1410InitialRadius delta)
        (hContinue : ∀ k : ℕ, 1 ≤ k → method.continuesAt k)
        (hsmallε : eps < eps0)
        (hsmallδ : delta < delta0),
        rLinearConvergenceTo
          (fun k : ℕ ↦ method (k + 1))
          (0 : Point) ∧
        ¬ rSuperlinearConvergenceTo
          (fun k : ℕ ↦ method (k + 1))
          (0 : Point) := sorry

#print axioms exercise1410Objective
#print axioms exercise1410Problem
#print axioms exercise1410SmoothMap
#print axioms exercise1410JacobianTranspose_eq
#print axioms exercise1410HessianApproximation
#print axioms exercise1410InitialPoint
#print axioms exercise1410LinftyNorm_eq
#print axioms rRate
