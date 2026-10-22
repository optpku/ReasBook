/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_1_extra_1

-- Domain sampling:
-- * core/canonical owner available upstream: `Chapter01.ConstrainedOptimizationProblem`
-- * Chapter 8 source-facing owner surface: the same constrained problem together with reusable
--   `eqIndices`/`ineqIndices` accessors and feasible-set lemmas stated in chapter vocabulary
-- * primitive data remain in the Chapter 1 owner (`objective`, `constraint`, equality/inequality
--   partition proofs); Chapter 8 adds only derived owner API

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

open scoped BigOperators

namespace ConstrainedOptimizationProblem

/-- The Chapter 8 equality-constraint index set carried by `problem`. -/
def eqIndices (_ : _root_.ConstrainedOptimizationProblem n m E I) : Set (Fin m) :=
  E

/-- The Chapter 8 inequality-constraint index set carried by `problem`. -/
def ineqIndices (_ : _root_.ConstrainedOptimizationProblem n m E I) : Set (Fin m) :=
  I

/-- Chapter08 Definition 8.1.1 (1). Membership in the feasible set is equivalent to satisfying
every equality constraint and every inequality constraint. -/
theorem mem_feasibleSet_iff (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (x : Point) :
    x ∈ problem.feasibleSet ↔
      (∀ i ∈ problem.eqIndices, problem.constraint i x = 0) ∧
        ∀ i ∈ problem.ineqIndices, 0 ≤ problem.constraint i x :=
  Iff.rfl

/-- Chapter08 Definition 8.1.1 (2). The feasible set of a constrained optimization problem is the
set of all feasible points. -/
theorem feasibleSet_eq_setOf_mem (problem : _root_.ConstrainedOptimizationProblem n m E I) :
    problem.feasibleSet = {x : Point | x ∈ problem} :=
  rfl

/-- The Chapter 8 Lagrangian associated to `problem` and multiplier vector `lam`. -/
def lagrangian
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (x : Point) (lam : Fin m → ℝ) : ℝ :=
  problem.objective x - ∑ i : Fin m, lam i * problem.constraint i x

/-- The defining formula for `problem.lagrangian x lam`. -/
theorem lagrangian_eq
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (x : Point) (lam : Fin m → ℝ) :
    problem.lagrangian x lam =
      problem.objective x - ∑ i : Fin m, lam i * problem.constraint i x :=
  rfl

/-- The active inequality indices at `x` are the inequality constraints of `problem` whose value
is `0` at `x`. -/
def activeIneqIndexSet
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (x : Point) : Set (Fin m) :=
  {i | i ∈ problem.ineqIndices ∧ problem.constraint i x = 0}

/-- Membership in `problem.activeIneqIndexSet x` means being an inequality index with vanishing
constraint value at `x`. -/
theorem mem_activeIneqIndexSet_iff
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (x : Point) (i : Fin m) :
    i ∈ problem.activeIneqIndexSet x ↔
      i ∈ problem.ineqIndices ∧ problem.constraint i x = 0 :=
  Iff.rfl

/-- Chapter08 Definition 8.1.5: the active constraint index set of `problem` at `x` is the union
of all equality-constraint indices with the active inequality indices at `x`. -/
def activeConstraintIndexSet
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (x : Point) : Set (Fin m) :=
  problem.eqIndices ∪ problem.activeIneqIndexSet x

/-- The defining formula for `problem.activeConstraintIndexSet x`. -/
theorem activeConstraintIndexSet_def
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (x : Point) :
    problem.activeConstraintIndexSet x =
      problem.eqIndices ∪ problem.activeIneqIndexSet x :=
  rfl

/-- A constraint index is active at `x` exactly when it is an equality-constraint index or an
inequality-constraint index whose constraint value is `0` at `x`. -/
theorem mem_activeConstraintIndexSet_iff
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (x : Point) (i : Fin m) :
    i ∈ problem.activeConstraintIndexSet x ↔
      i ∈ problem.eqIndices ∨
        (i ∈ problem.ineqIndices ∧ problem.constraint i x = 0) := by
  simp [activeConstraintIndexSet, activeIneqIndexSet]

/-- At a feasible point, a constraint index is inactive exactly when it is an inequality index
whose constraint value is strictly positive. -/
theorem not_mem_activeConstraintIndexSet_iff
    (problem : _root_.ConstrainedOptimizationProblem n m E I) {x : Point} (hx : x ∈ problem)
    (i : Fin m) :
    i ∉ problem.activeConstraintIndexSet x ↔
      i ∈ problem.ineqIndices ∧ 0 < problem.constraint i x := by
  have hx' := (problem.mem_feasibleSet_iff x).mp hx
  rw [mem_activeConstraintIndexSet_iff]
  constructor
  · intro hi_not_active
    rcases not_or.mp hi_not_active with ⟨hi_not_eq, hi_not_activeIneq⟩
    have hi_mem : i ∈ problem.eqIndices ∪ problem.ineqIndices := by
      simpa [ConstrainedOptimizationProblem.eqIndices, ConstrainedOptimizationProblem.ineqIndices]
        using (show i ∈ E ∪ I from by
          rw [problem.eqIndices_union_ineqIndices]
          exact Set.mem_univ i)
    have hi_ineq : i ∈ problem.ineqIndices := by
      rcases hi_mem with hi_eq | hi_ineq
      · exact False.elim (hi_not_eq hi_eq)
      · exact hi_ineq
    have hne_zero : problem.constraint i x ≠ 0 := fun hzero ↦
      hi_not_activeIneq ⟨hi_ineq, hzero⟩
    have hnonneg : 0 ≤ problem.constraint i x := hx'.2 i <| by
      simpa [ConstrainedOptimizationProblem.ineqIndices] using hi_ineq
    refine ⟨hi_ineq, lt_of_le_of_ne hnonneg ?_⟩
    simpa using hne_zero.symm
  · rintro ⟨hi_ineq, hpos⟩
    intro hi_active
    rcases hi_active with hi_eq | ⟨_, hzero⟩
    · have hdisj : Disjoint problem.eqIndices problem.ineqIndices := by
        simpa [ConstrainedOptimizationProblem.eqIndices, ConstrainedOptimizationProblem.ineqIndices]
          using problem.eqIndices_disjoint_ineqIndices
      exact Set.disjoint_left.mp hdisj hi_eq hi_ineq
    · exact (lt_irrefl 0) <| hzero ▸ hpos

end ConstrainedOptimizationProblem
