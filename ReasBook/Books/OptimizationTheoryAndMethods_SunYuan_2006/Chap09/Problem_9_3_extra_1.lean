/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Rank
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_2_1

noncomputable section

open Matrix

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain-style sampling in Chapter 9:
-- * source-facing layer here: equality-constrained quadratic programs with the column-oriented
--   matrix presentation `A = [a₁, ..., a_m]`.
-- * core/canonical owner upstream: `QuadraticProgram n me mi` from
--   `Definition_9_1_extra_1`, together with `QuadraticProgram.objective_eq` and
--   `QuadraticProgram.mem_feasibleSet_iff`.
-- * bridge/view used here: `toQuadraticProgram`, specializing the canonical owner to `mi = 0`
--   and replacing the source constraint `Aᵀ x = b` by the owner's equality block
--   `Aeq.mulVec x = beq` with `Aeq = Aᵀ`.
--
-- Primitive data in this file are therefore only the source vectors and matrices; the
-- full-column-rank hypothesis from the textbook is a separate property, while the objective and
-- feasible-set APIs are derived from the Chapter 9 owner.

/-- Chapter09 Problem 9.3-extra-1: an equality-constrained quadratic programming problem on
`ℝ^n` is specified by vectors `g : ℝ^n` and `b : ℝ^m`, a matrix
`A = [a₁, ..., a_m] : ℝ^(n × m)`, and a symmetric matrix `G : ℝ^(n × n)`. The textbook's
full-column-rank assumption `Matrix.rank A = m` is recorded separately as
`problem.HasFullColumnRank`, since it is not primitive data for the canonical Chapter 9 bridge. -/
structure EqualityConstrainedQuadraticProgram (n m : ℕ) where
  g : EuclideanSpace ℝ (Fin n)
  G : Matrix (Fin n) (Fin n) ℝ
  A : Matrix (Fin n) (Fin m) ℝ
  b : EuclideanSpace ℝ (Fin m)
  hG_symm : G.IsSymm

namespace EqualityConstrainedQuadraticProgram

/-- The source full-column-rank hypothesis for the equality-constraint matrix. This is a
property of the problem data, not primitive data of the problem owner. -/
def HasFullColumnRank (problem : EqualityConstrainedQuadraticProgram n m) : Prop :=
  Matrix.rank problem.A = m

/-- The canonical Chapter 9 owner view of an equality-constrained quadratic program. -/
abbrev toQuadraticProgram (problem : EqualityConstrainedQuadraticProgram n m) :
    QuadraticProgram n m 0 where
  G := problem.G
  hG_symm := problem.hG_symm
  g := problem.g
  Aeq := (problem.A)ᵀ
  beq := problem.b
  Aineq := 0
  bineq := 0

/-- The canonical owner coercion for equality-constrained quadratic programs. -/
instance : Coe (EqualityConstrainedQuadraticProgram n m) (QuadraticProgram n m 0) where
  coe problem := problem.toQuadraticProgram

/-- The source objective is the quadratic objective of the associated canonical quadratic
program. -/
abbrev objective (problem : EqualityConstrainedQuadraticProgram n m) : Point → ℝ :=
  problem.toQuadraticProgram.objective

/-- An equality-constrained quadratic program can be evaluated as its quadratic objective. -/
instance : CoeFun (EqualityConstrainedQuadraticProgram n m) (fun _ ↦ Point → ℝ) where
  coe problem := problem.objective

/-- Evaluating `problem` as a function returns the canonical quadratic-program objective. -/
@[simp] theorem coe_apply (problem : EqualityConstrainedQuadraticProgram n m) (x : Point) :
    problem x = problem.objective x :=
  rfl

/-- Evaluating `problem` expands to the source quadratic formula
`x ↦ gᵀ x + (1 / 2) * xᵀ G x`. -/
theorem objective_eq (problem : EqualityConstrainedQuadraticProgram n m) (x : Point) :
    problem.objective x =
      (1 / 2 : ℝ) * dotProduct x (problem.G.mulVec x) + dotProduct problem.g x := by
  rw [objective, toQuadraticProgram]

/-- The feasible set is the equality-only feasible set of the associated canonical quadratic
program. -/
abbrev feasibleSet (problem : EqualityConstrainedQuadraticProgram n m) : Set Point :=
  problem.toQuadraticProgram.feasibleSet

/-- Feasibility in an equality-constrained quadratic program means satisfying `Aᵀ x = b`. -/
instance : Membership Point (EqualityConstrainedQuadraticProgram n m) where
  mem problem x := x ∈ problem.feasibleSet

/-- Membership in an equality-constrained quadratic program is exactly the equality constraint
`Aᵀ x = b`. -/
@[simp] theorem mem_iff (problem : EqualityConstrainedQuadraticProgram n m) (x : Point) :
    x ∈ problem ↔ (problem.Aᵀ).mulVec x = problem.b := by
  change x ∈ problem.feasibleSet ↔ ((problem.A)ᵀ).mulVec x = problem.b
  simpa [feasibleSet, toQuadraticProgram] using
    QuadraticProgram.mem_feasibleSet_iff problem.toQuadraticProgram x

/-- Membership in `problem.feasibleSet` is exactly the equality constraint `Aᵀ x = b`. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : EqualityConstrainedQuadraticProgram n m) (x : Point) :
    x ∈ problem.feasibleSet ↔ (problem.Aᵀ).mulVec x = problem.b :=
  problem.mem_iff x

/-- The equality multiplier `λ` determines the canonical Chapter 9 dual variable of the associated
quadratic program with zero inequality multiplier and auxiliary vector `A λ - g`. This is the
source-facing bridge from the textbook equality-multiplier formula to the chapter's dual owner. -/
def toDualVariable (problem : EqualityConstrainedQuadraticProgram n m)
    (lam : EuclideanSpace ℝ (Fin m)) :
    QuadraticProgram.DualVariable problem.toQuadraticProgram where
  eqMultiplier := lam
  ineqMultiplier := 0
  y := WithLp.toLp 2 (problem.A.mulVec lam.ofLp) - problem.g

/-- The canonical dual variable attached to an equality multiplier automatically satisfies the
Chapter 9 stationarity relation. -/
theorem satisfiesDualStationarity_toDualVariable
    (problem : EqualityConstrainedQuadraticProgram n m) (lam : EuclideanSpace ℝ (Fin m)) :
    problem.toQuadraticProgram.SatisfiesDualStationarity (problem.toDualVariable lam) := by
  ext i
  simp [toDualVariable, EqualityConstrainedQuadraticProgram.toQuadraticProgram,
    sub_eq_add_neg, add_assoc]

end EqualityConstrainedQuadraticProgram

end
