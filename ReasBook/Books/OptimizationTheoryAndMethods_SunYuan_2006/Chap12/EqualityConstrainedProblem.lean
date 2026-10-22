/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Algorithm_12_1_1

noncomputable section

open scoped BigOperators

section

variable {n m : ℕ}

local notation "Point" => LagrangeNewtonPoint n
local notation "Multiplier" => LagrangeNewtonMultiplier m
local notation "HessianMatrix" => Matrix (Fin n) (Fin n) ℝ
local notation "ConstraintMatrix" => Matrix (Fin n) (Fin m) ℝ
local notation "KKTIndex" => Sum (Fin n) (Fin m)
local notation "KKTMatrix" => Matrix KKTIndex KKTIndex ℝ

/-- An equality-constrained nonlinear optimization problem with objective `f : ℝ^n → ℝ` and
constraint map `c : ℝ^n → ℝ^m`, written componentwise as `constraint i x = c_i(x)`. -/
structure EqualityConstrainedProblem (n m : ℕ) where
  objective : LagrangeNewtonPoint n → ℝ
  constraint : Fin m → LagrangeNewtonPoint n → ℝ

namespace EqualityConstrainedProblem

/-- The constraint vector `c(x)` with coordinates `c_i(x)`. -/
def constraintVector
    (problem : EqualityConstrainedProblem n m) (x : LagrangeNewtonPoint n) :
    LagrangeNewtonMultiplier m :=
  WithLp.toLp 2 (fun i ↦ problem.constraint i x)

/-- The `i`-th coordinate of `problem.constraintVector x` is `problem.constraint i x`. -/
@[simp] theorem constraintVector_apply
    (problem : EqualityConstrainedProblem n m) (x : LagrangeNewtonPoint n) (i : Fin m) :
    problem.constraintVector x i = problem.constraint i x := rfl

/-- The feasible set of an equality-constrained problem consists of the points where the
constraint vector vanishes. -/
def feasibleSet (problem : EqualityConstrainedProblem n m) : Set (LagrangeNewtonPoint n) :=
  {x | problem.constraintVector x = 0}

/-- Equality-constrained feasibility is membership in `problem.feasibleSet`. -/
instance : Membership (LagrangeNewtonPoint n) (EqualityConstrainedProblem n m) where
  mem problem x := x ∈ problem.feasibleSet

/-- Membership in `problem.feasibleSet` is exactly the vanishing of every constraint
component. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : EqualityConstrainedProblem n m) (x : LagrangeNewtonPoint n) :
    x ∈ problem.feasibleSet ↔
      ∀ i : Fin m, problem.constraint i x = 0 := by
  constructor
  · intro hx i
    have hxi : problem.constraintVector x i = 0 := by
      exact congrArg (fun v : Multiplier ↦ v i) hx
    simpa [constraintVector_apply] using hxi
  · intro hx
    ext i
    simpa [constraintVector_apply] using hx i

/-- The fixed equality-constrained problem viewed as the Chapter 10 mixed-constraint owner with
only equality constraints. -/
def toStandardPenaltyProblem
    (problem : EqualityConstrainedProblem n m) : StandardPenaltyProblem n m where
  eqCount := m
  eqCount_le := le_rfl
  objective := problem.objective
  constraint := problem.constraint

/-- The Chapter 10 constraint map of `problem.toStandardPenaltyProblem` is exactly the canonical
constraint vector of the equality-constrained owner. -/
@[simp] theorem toStandardPenaltyProblem_constraintMap
    (problem : EqualityConstrainedProblem n m) (x : Point) :
    problem.toStandardPenaltyProblem.constraintMap x = problem.constraintVector x :=
  rfl

/-- Because `problem.toStandardPenaltyProblem` has only equality constraints, its Chapter 10
violation vector is exactly `problem.constraintVector x`. -/
@[simp] theorem toStandardPenaltyProblem_constraintViolation
    (problem : EqualityConstrainedProblem n m) (x : Point) :
    c⁽-⁾[problem.toStandardPenaltyProblem] x = problem.constraintVector x := by
  ext i
  simp [StandardPenaltyProblem.constraintViolation,
    EqualityConstrainedProblem.toStandardPenaltyProblem]

/-- Feasibility for the equality-constrained owner agrees with feasibility for its Chapter 10
equality-only bridge. -/
@[simp] theorem mem_toStandardPenaltyProblem_iff
    (problem : EqualityConstrainedProblem n m) (x : Point) :
    x ∈ problem.toStandardPenaltyProblem ↔ x ∈ problem := by
  constructor
  · intro hx
    have hEq :
        ∀ i : Fin m,
          problem.toStandardPenaltyProblem.constraint i x = 0 := by
      have hx' :=
        (StandardPenaltyProblem.mem_feasibleSet_iff problem.toStandardPenaltyProblem x).1 hx
      intro i
      exact hx'.1 i i.2
    exact (problem.mem_feasibleSet_iff x).2 fun i ↦ by
      simpa [EqualityConstrainedProblem.toStandardPenaltyProblem] using hEq i
  · intro hx
    refine (StandardPenaltyProblem.mem_feasibleSet_iff problem.toStandardPenaltyProblem x).2 ?_
    refine ⟨?_, ?_⟩
    · intro i hi
      simpa [EqualityConstrainedProblem.toStandardPenaltyProblem] using
        (problem.mem_feasibleSet_iff x).1 hx i
    · intro i hi
      exact (Nat.not_lt_of_ge hi i.2).elim

/-- The Lagrangian `L(x, λ) = f(x) - ∑ i, λ_i c_i(x)` attached to `problem`. -/
def lagrangian
    (problem : EqualityConstrainedProblem n m) (x : LagrangeNewtonPoint n)
    (lam : LagrangeNewtonMultiplier m) : ℝ :=
  problem.objective x - ∑ i : Fin m, lam i * problem.constraint i x

/-- Unfolding `problem.lagrangian x lam` gives the finite-sum Lagrangian formula
`f(x) - ∑ i, λ_i c_i(x)`. -/
theorem lagrangian_eq
    (problem : EqualityConstrainedProblem n m) (x : LagrangeNewtonPoint n)
    (lam : LagrangeNewtonMultiplier m) :
    problem.lagrangian x lam =
      problem.objective x - ∑ i : Fin m, lam i * problem.constraint i x := rfl

/-- The linearized `i`-th equality constraint `c_i(x) + ∇ c_i(x)ᵀ d`. -/
def constraintLinearization
    (problem : EqualityConstrainedProblem n m) (x d : LagrangeNewtonPoint n) (i : Fin m) : ℝ :=
  problem.constraint i x +
    dotProduct d (@gradient ℝ Point _ _ _ _ (problem.constraint i) x)

/-- Unfolding `problem.constraintLinearization x d i` gives the source linearized equality
constraint formula `c_i(x) + ∇ c_i(x)ᵀ d`. -/
theorem constraintLinearization_eq
    (problem : EqualityConstrainedProblem n m) (x d : LagrangeNewtonPoint n) (i : Fin m) :
    problem.constraintLinearization x d i =
      problem.constraint i x +
        dotProduct d (@gradient ℝ Point _ _ _ _ (problem.constraint i) x) := rfl

/-- The multiplier-weighted constraint-gradient combination
`∑ i, λ_i • ∇ c_i(x)`. -/
def constraintGradientCombination
    (problem : EqualityConstrainedProblem n m) (x : LagrangeNewtonPoint n)
    (lam : LagrangeNewtonMultiplier m) : LagrangeNewtonPoint n :=
  ∑ i : Fin m, lam i • (@gradient ℝ Point _ _ _ _ (problem.constraint i) x)

/-- Unfolding `problem.constraintGradientCombination x lam` gives the finite-sum gradient
combination `∑ i, λ_i • ∇ c_i(x)`. -/
theorem constraintGradientCombination_eq
    (problem : EqualityConstrainedProblem n m) (x : LagrangeNewtonPoint n)
    (lam : LagrangeNewtonMultiplier m) :
    problem.constraintGradientCombination x lam =
      ∑ i : Fin m, lam i • (@gradient ℝ Point _ _ _ _ (problem.constraint i) x) := rfl

/-- The matrix `A(x)` whose `j`-th column is `∇ c_j(x)`. -/
def constraintGradientMatrix
    (problem : EqualityConstrainedProblem n m) (x : LagrangeNewtonPoint n) :
    Matrix (Fin n) (Fin m) ℝ :=
  fun row col ↦ (@gradient ℝ Point _ _ _ _ (problem.constraint col) x) row

/-- The `(row, col)` entry of `problem.constraintGradientMatrix x` is the `row`-th coordinate
of `∇ c_col(x)`. -/
theorem constraintGradientMatrix_apply
    (problem : EqualityConstrainedProblem n m) (x : LagrangeNewtonPoint n)
    (row : Fin n) (col : Fin m) :
    problem.constraintGradientMatrix x row col =
      (@gradient ℝ Point _ _ _ _ (problem.constraint col) x) row := rfl

/-- The KKT matrix `(12.1.12)` at `x` with Hessian approximation `W`, namely
`[[W, -A(x)], [-(A(x))ᵀ, 0]]`. -/
def lagrangeNewtonKKTMatrix
    (problem : EqualityConstrainedProblem n m) (x : LagrangeNewtonPoint n)
    (hessianApprox : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Sum (Fin n) (Fin m)) (Sum (Fin n) (Fin m)) ℝ :=
  Matrix.fromBlocks
    hessianApprox
    (-problem.constraintGradientMatrix x)
    (-(problem.constraintGradientMatrix x).transpose)
    0

/-- Unfolding `problem.lagrangeNewtonKKTMatrix x hessianApprox` gives the block matrix
`[[W, -A(x)], [-(A(x))ᵀ, 0]]`. -/
theorem lagrangeNewtonKKTMatrix_eq
    (problem : EqualityConstrainedProblem n m) (x : LagrangeNewtonPoint n)
    (hessianApprox : Matrix (Fin n) (Fin n) ℝ) :
    problem.lagrangeNewtonKKTMatrix x hessianApprox =
      Matrix.fromBlocks
        hessianApprox
        (-problem.constraintGradientMatrix x)
        (-(problem.constraintGradientMatrix x).transpose)
        0 := rfl

/-- A point `xStar` with multiplier `lamStar` is a KKT point of the equality-constrained problem
when `xStar` is feasible and the Lagrangian is stationary at `xStar`. -/
class IsKKTPoint
    (problem : EqualityConstrainedProblem n m) (xStar : LagrangeNewtonPoint n)
    (lamStar : LagrangeNewtonMultiplier m) :
    Prop where
  feasible : xStar ∈ problem
  stationarity :
    gradient (fun x : Point ↦ problem.lagrangian x lamStar) xStar = 0

/-- Unfolding `problem.IsKKTPoint xStar lamStar` gives feasibility together with Lagrangian
stationarity at `xStar`. -/
theorem isKKTPoint_iff
    (problem : EqualityConstrainedProblem n m) (xStar : LagrangeNewtonPoint n)
    (lamStar : LagrangeNewtonMultiplier m) :
    EqualityConstrainedProblem.IsKKTPoint problem xStar lamStar ↔
      xStar ∈ problem ∧
        gradient (fun x : Point ↦ problem.lagrangian x lamStar) xStar = 0 := by
  constructor
  · intro h
    exact ⟨h.feasible, h.stationarity⟩
  · rintro ⟨h_feasible, h_stationarity⟩
    exact ⟨h_feasible, h_stationarity⟩

end EqualityConstrainedProblem

end
