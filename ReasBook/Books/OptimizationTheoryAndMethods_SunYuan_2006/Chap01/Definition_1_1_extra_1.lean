/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Pi

-- Semantic recall: no dedicated mathlib owner for introductory optimization problems was found.
-- Analogue checked while repairing the Prop API: `IsVectorNorm` in Chapter01/Definition_1_2_1.lean.
-- This file uses the canonical Lean surface of an objective function and its feasible set.
-- The finite family of constraints from the source is modeled by one family on `Fin m`
-- together with equality and inequality index sets `E`, `I`.

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

/-- Chapter01 Definition 1.1-extra-1 (1). An optimization problem on `ℝ^n` consists of an objective
function and a feasible set of decision variables. -/
structure OptimizationProblem (n : ℕ) where
  objective : (Fin n → ℝ) → ℝ
  feasibleSet : Set (Fin n → ℝ)

namespace OptimizationProblem

/-- An optimization problem can be evaluated at a decision variable via its objective function. -/
instance : CoeFun (OptimizationProblem n) (fun _ ↦ Point → ℝ) where
  coe problem := problem.objective

/-- Evaluating `problem` as a function returns its objective value. -/
theorem coeFn_apply (problem : OptimizationProblem n) (x : Point) :
    problem x = problem.objective x :=
  rfl

/-- Feasibility in `OptimizationProblem` is membership in its feasible set. -/
instance : Membership Point (OptimizationProblem n) where
  mem problem x := x ∈ problem.feasibleSet

/-- Membership in an optimization problem is equivalent to belonging to its feasible set. -/
theorem mem_iff (problem : OptimizationProblem n) (x : Point) :
    x ∈ problem ↔ x ∈ problem.feasibleSet :=
  Iff.rfl

/-- Chapter01 Definition 1.1-extra-1 (2). An optimization problem is unconstrained exactly when its
feasible set is all of `ℝ^n`. -/
def IsUnconstrained (problem : OptimizationProblem n) : Prop :=
  problem.feasibleSet = Set.univ

/-- The unconstrained condition is equality with the full decision space. -/
theorem isUnconstrained_iff (problem : OptimizationProblem n) :
    problem.IsUnconstrained ↔ problem.feasibleSet = Set.univ :=
  Iff.rfl

/-- `OptimizationProblem.IsUnconstrained` unfolds to equality with `Set.univ`. -/
theorem isUnconstrained_def (problem : OptimizationProblem n) :
    problem.IsUnconstrained = (problem.feasibleSet = Set.univ) :=
  rfl

end OptimizationProblem

/-- Chapter01 Definition 1.1-extra-1 (3). A constrained optimization problem on `ℝ^n` is given by an
objective function, a single finite family of constraint functions indexed by `Fin m`, and a
partition of the indices into equality and inequality constraints. -/
structure ConstrainedOptimizationProblem (n m : ℕ) (E I : Set (Fin m)) where
  objective : (Fin n → ℝ) → ℝ
  constraint : Fin m → (Fin n → ℝ) → ℝ
  eqIndices_union_ineqIndices : E ∪ I = Set.univ
  eqIndices_disjoint_ineqIndices : Disjoint E I

namespace ConstrainedOptimizationProblem

/-- A constrained optimization problem can be evaluated at a decision variable via its objective
function. -/
instance : CoeFun (ConstrainedOptimizationProblem n m E I) (fun _ ↦ Point → ℝ) where
  coe problem := problem.objective

/-- Evaluating `problem` as a function returns its objective value. -/
theorem coeFn_apply (problem : ConstrainedOptimizationProblem n m E I) (x : Point) :
    problem x = problem.objective x :=
  rfl

/-- The feasible set of a constrained optimization problem consists of the points satisfying every
equality constraint and every inequality constraint. -/
def feasibleSet (problem : ConstrainedOptimizationProblem n m E I) : Set Point :=
  {x | (∀ i ∈ E, problem.constraint i x = 0) ∧ ∀ i ∈ I, 0 ≤ problem.constraint i x}

/-- Feasibility in `ConstrainedOptimizationProblem` means satisfying all defining constraints. -/
instance : Membership Point (ConstrainedOptimizationProblem n m E I) where
  mem problem x := x ∈ problem.feasibleSet

/-- Membership in a constrained optimization problem is equivalent to satisfying all defining
constraints. -/
theorem mem_iff (problem : ConstrainedOptimizationProblem n m E I) (x : Point) :
    x ∈ problem ↔
      (∀ i ∈ E, problem.constraint i x = 0) ∧ ∀ i ∈ I, 0 ≤ problem.constraint i x :=
  Iff.rfl

/-- Forgetting the constraint presentation turns a constrained problem into an ordinary
optimization problem with the same objective and feasible set. -/
def toOptimizationProblem (problem : ConstrainedOptimizationProblem n m E I) :
    OptimizationProblem n where
  objective := problem.objective
  feasibleSet := problem.feasibleSet

/-- Forgetting the constraints preserves the objective function exactly. -/
theorem toOptimizationProblem_objective (problem : ConstrainedOptimizationProblem n m E I) :
    problem.toOptimizationProblem.objective = problem.objective :=
  rfl

/-- Forgetting the constraints preserves the feasible set exactly. -/
theorem toOptimizationProblem_feasibleSet (problem : ConstrainedOptimizationProblem n m E I) :
    problem.toOptimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- The underlying optimization problem has the same feasible points as the constrained problem. -/
theorem mem_toOptimizationProblem_iff
    (problem : ConstrainedOptimizationProblem n m E I) (x : Point) :
    x ∈ problem.toOptimizationProblem ↔ x ∈ problem :=
  Iff.rfl

/-- Chapter01 Definition 1.1-extra-1 (4). A constrained optimization problem is a linear programming
problem when the objective and every constraint function are linear. -/
class IsLinearProgramming (problem : ConstrainedOptimizationProblem n m E I) : Prop where
  objective_eq_linearMap : ∃ f : (Fin n → ℝ) →ₗ[ℝ] ℝ, problem.objective = f
  constraint_eq_linearMap :
    ∀ i, ∃ c : (Fin n → ℝ) →ₗ[ℝ] ℝ, problem.constraint i = c

/-- Linear programming means that the objective and all constraints come from linear maps. -/
theorem isLinearProgramming_iff (problem : ConstrainedOptimizationProblem n m E I) :
    problem.IsLinearProgramming ↔
      (∃ f : (Fin n → ℝ) →ₗ[ℝ] ℝ, problem.objective = f) ∧
        ∀ i, ∃ c : (Fin n → ℝ) →ₗ[ℝ] ℝ, problem.constraint i = c :=
  ⟨fun h ↦ ⟨h.objective_eq_linearMap, h.constraint_eq_linearMap⟩, fun h ↦
    ⟨h.1, h.2⟩⟩

/-- `IsLinearProgramming` exposes the linearity of the objective and the common
constraint family. -/
theorem isLinearProgramming_spec
    {problem : ConstrainedOptimizationProblem n m E I} [h : problem.IsLinearProgramming] :
    (∃ f : (Fin n → ℝ) →ₗ[ℝ] ℝ, problem.objective = f) ∧
      ∀ i, ∃ c : (Fin n → ℝ) →ₗ[ℝ] ℝ, problem.constraint i = c :=
  ⟨h.objective_eq_linearMap, h.constraint_eq_linearMap⟩

/-- Chapter01 Definition 1.1-extra-1 (5). A constrained optimization problem is nonlinear
programming when it is not linear programming. -/
def IsNonlinearProgramming (problem : ConstrainedOptimizationProblem n m E I) : Prop :=
  ¬problem.IsLinearProgramming

/-- Nonlinear programming is the negation of linear programming. -/
theorem isNonlinearProgramming_iff (problem : ConstrainedOptimizationProblem n m E I) :
    problem.IsNonlinearProgramming ↔ ¬problem.IsLinearProgramming :=
  Iff.rfl

/-- `IsNonlinearProgramming` unfolds to the negation of `IsLinearProgramming`. -/
theorem isNonlinearProgramming_def (problem : ConstrainedOptimizationProblem n m E I) :
    problem.IsNonlinearProgramming = ¬problem.IsLinearProgramming :=
  rfl

end ConstrainedOptimizationProblem
