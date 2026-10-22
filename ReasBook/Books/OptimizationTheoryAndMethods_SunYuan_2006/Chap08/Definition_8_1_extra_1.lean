/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_1_extra_1
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Pi

-- Source/core/bridge triage for this file:
-- * source-facing: `StandardConstrainedOptimizationProblem` with the source contiguous
--   equality/inequality split.
-- * core/canonical: Chapter 1 `ConstrainedOptimizationProblem`.
-- * bridge/view: `eqIndices`, `ineqIndices`, `toConstrainedOptimizationProblem`, and the
--   derived classification predicates. The source nonlinearity clause is modeled as a predicate
--   on the standard owner rather than as primitive data, so affine/linear and quadratic
--   subclasses remain instances of the same ambient notion.

section

variable {n m : ℕ}

/-- Chapter08 Definition 8.1-extra-1 (1). A standard constrained optimization problem on `ℝ^n`
consists of an objective `f`, a finite family of constraint functions `c_i`, a number
`eqCount ≤ m` splitting the first `eqCount` constraints into equalities and the remaining
constraints into inequalities. The source nonlinearity clause is treated below as a derived
classification predicate rather than as primitive owner data, so linear and quadratic subclasses
share the same ambient owner. Smoothness assumptions belong to later theorem hypotheses rather
than to this source-facing owner. -/
structure StandardConstrainedOptimizationProblem (n m : ℕ) where
  eqCount : ℕ
  eqCount_le : eqCount ≤ m
  objective : (Fin n → ℝ) → ℝ
  constraint : Fin m → (Fin n → ℝ) → ℝ

namespace StandardConstrainedOptimizationProblem

local notation "Point" => Fin n → ℝ
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- The equality-constraint index set `E` is the initial segment `0, ..., eqCount - 1` of
`Fin m`, corresponding to the book's `1, ..., m_e` in zero-based indexing. -/
def eqIndices (P : StandardConstrainedOptimizationProblem n m) : Set (Fin m) :=
  {i | i.1 < P.eqCount}

/-- The inequality-constraint index set `I` is the final segment `eqCount, ..., m - 1` of
`Fin m`, corresponding to the book's `m_e + 1, ..., m` in zero-based indexing. -/
def ineqIndices (P : StandardConstrainedOptimizationProblem n m) : Set (Fin m) :=
  {i | P.eqCount ≤ i.1}

/-- Membership in `eqIndices` means that the zero-based index lies before `eqCount`. -/
theorem mem_eqIndices_iff (P : StandardConstrainedOptimizationProblem n m) (i : Fin m) :
    i ∈ P.eqIndices ↔ i.1 < P.eqCount :=
  Iff.rfl

/-- Membership in `ineqIndices` means that the zero-based index lies at or after `eqCount`. -/
theorem mem_ineqIndices_iff (P : StandardConstrainedOptimizationProblem n m) (i : Fin m) :
    i ∈ P.ineqIndices ↔ P.eqCount ≤ i.1 :=
  Iff.rfl

/-- The source index sets `E` and `I` partition all constraints. -/
theorem eqIndices_union_ineqIndices (P : StandardConstrainedOptimizationProblem n m) :
    P.eqIndices ∪ P.ineqIndices = Set.univ := by
  ext i
  simp [eqIndices, ineqIndices, Nat.lt_or_ge]

/-- The equality and inequality index sets are disjoint. -/
theorem eqIndices_disjoint_ineqIndices (P : StandardConstrainedOptimizationProblem n m) :
    Disjoint P.eqIndices P.ineqIndices := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext i
  simp [eqIndices, ineqIndices]

/-- Forgetting the contiguous split data produces the generic Chapter 1 constrained optimization
problem with equality index set `eqIndices` and inequality index set `ineqIndices`. -/
def toConstrainedOptimizationProblem (P : StandardConstrainedOptimizationProblem n m) :
    ConstrainedOptimizationProblem n m P.eqIndices P.ineqIndices where
  objective := P.objective
  constraint := P.constraint
  eqIndices_union_ineqIndices := P.eqIndices_union_ineqIndices
  eqIndices_disjoint_ineqIndices := P.eqIndices_disjoint_ineqIndices

/-- The feasible set consists of the points satisfying every equality constraint exactly and every
inequality constraint weakly. -/
abbrev feasibleSet (P : StandardConstrainedOptimizationProblem n m) : Set Point :=
  P.toConstrainedOptimizationProblem.feasibleSet

/-- Feasibility in a standard constrained optimization problem is membership in its feasible set. -/
instance : Membership Point (StandardConstrainedOptimizationProblem n m) where
  mem P x := x ∈ P.feasibleSet

/-- Membership in the feasible set is equivalent to satisfying the defining equality and
inequality constraints. -/
theorem mem_feasibleSet_iff (P : StandardConstrainedOptimizationProblem n m) (x : Point) :
    x ∈ P.feasibleSet ↔
      (∀ i ∈ P.eqIndices, P.constraint i x = 0) ∧
        ∀ i ∈ P.ineqIndices, 0 ≤ P.constraint i x :=
  Iff.rfl

/-- Forgetting to the generic constrained problem does not change the feasible set. -/
theorem toConstrainedOptimizationProblem_feasibleSet
    (P : StandardConstrainedOptimizationProblem n m) :
    P.toConstrainedOptimizationProblem.feasibleSet = P.feasibleSet :=
  rfl

/-- Chapter08 Definition 8.1-extra-1 (2). The source formulation is unconstrained exactly when
there are no constraints, i.e. `m = 0`. -/
def IsUnconstrained (_ : StandardConstrainedOptimizationProblem n m) : Prop :=
  m = 0

/-- `IsUnconstrained` unfolds to the condition `m = 0`. -/
theorem isUnconstrained_iff (P : StandardConstrainedOptimizationProblem n m) :
    P.IsUnconstrained ↔ m = 0 :=
  Iff.rfl

/-- A standard constrained optimization problem has an affine objective when its objective is of
the form `x ↦ aᵀ x + b`. -/
def HasAffineObjective (P : StandardConstrainedOptimizationProblem n m) : Prop :=
  ∃ f : Point →ᵃ[ℝ] ℝ, P.objective = f

/-- `HasAffineObjective` means that the objective is represented by an affine map. -/
theorem hasAffineObjective_iff (P : StandardConstrainedOptimizationProblem n m) :
    P.HasAffineObjective ↔ ∃ f : Point →ᵃ[ℝ] ℝ, P.objective = f :=
  Iff.rfl

/-- Chapter08 Definition 8.1-extra-1 (3). The source formulation is equality constrained when
every constraint is an equality and there is at least one constraint. -/
class IsEqualityConstrained (P : StandardConstrainedOptimizationProblem n m) : Prop where
  /-- All source constraints are equality constraints. -/
  eqCount_eq : P.eqCount = m
  /-- The source formulation has at least one constraint. -/
  constraints_nonempty : m ≠ 0

/-- The predicate `IsEqualityConstrained` is proof-irrelevant. -/
instance isEqualityConstrained_subsingleton (P : StandardConstrainedOptimizationProblem n m) :
    Subsingleton P.IsEqualityConstrained := inferInstance

/-- `IsEqualityConstrained` means `eqCount = m` together with `m ≠ 0`. -/
theorem isEqualityConstrained_iff (P : StandardConstrainedOptimizationProblem n m) :
    P.IsEqualityConstrained ↔ P.eqCount = m ∧ m ≠ 0 :=
  ⟨fun h ↦ ⟨h.eqCount_eq, h.constraints_nonempty⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Chapter08 Definition 8.1-extra-1 (4). The source formulation is linearly constrained when
every constraint function is affine, i.e. of the form `x ↦ aᵀ x + b`. -/
def IsLinearlyConstrained (P : StandardConstrainedOptimizationProblem n m) : Prop :=
  ∀ i, ∃ c : Point →ᵃ[ℝ] ℝ, P.constraint i = c

/-- `IsLinearlyConstrained` means that each constraint function is represented by an affine map. -/
theorem isLinearlyConstrained_iff (P : StandardConstrainedOptimizationProblem n m) :
    P.IsLinearlyConstrained ↔ ∀ i, ∃ c : Point →ᵃ[ℝ] ℝ, P.constraint i = c :=
  Iff.rfl

/-- The source nonlinear-programming clause is that the objective and all constraints are not
simultaneously affine. This remains a classification predicate on the standard constrained owner,
so linearly constrained and quadratic programs are still standard constrained problems. -/
def IsNonlinearProgramming (P : StandardConstrainedOptimizationProblem n m) : Prop :=
  ¬ (P.HasAffineObjective ∧ P.IsLinearlyConstrained)

/-- `IsNonlinearProgramming` unfolds to the negation of simultaneous affine objective and affine
constraint representations. -/
theorem isNonlinearProgramming_iff (P : StandardConstrainedOptimizationProblem n m) :
    P.IsNonlinearProgramming ↔
      ¬ ((∃ f : Point →ᵃ[ℝ] ℝ, P.objective = f) ∧
          ∀ i, ∃ c : Point →ᵃ[ℝ] ℝ, P.constraint i = c) := by
  simp [IsNonlinearProgramming, HasAffineObjective, IsLinearlyConstrained]

/-- A problem has a quadratic objective when its objective is represented by a matrix quadratic
expression `x ↦ (1 / 2) * xᵀ G x + bᵀ x + c`. -/
def HasQuadraticObjective (P : StandardConstrainedOptimizationProblem n m) : Prop :=
  ∃ G : MatrixN, ∃ b : Point, ∃ c : ℝ,
    P.objective = fun x ↦ (1 / 2 : ℝ) * dotProduct x (G.mulVec x) + dotProduct b x + c

/-- `HasQuadraticObjective` unfolds to the existence of a matrix/vector/scalar quadratic model. -/
theorem hasQuadraticObjective_iff (P : StandardConstrainedOptimizationProblem n m) :
    P.HasQuadraticObjective ↔
      ∃ G : MatrixN, ∃ b : Point, ∃ c : ℝ,
        P.objective = fun x ↦ (1 / 2 : ℝ) * dotProduct x (G.mulVec x) + dotProduct b x + c :=
  Iff.rfl

/-- Chapter08 Definition 8.1-extra-1 (5). A quadratic programming problem is a linearly
constrained problem with a quadratic objective. -/
class IsQuadraticProgramming (P : StandardConstrainedOptimizationProblem n m) : Prop where
  /-- Every source constraint is affine in the textbook linear-constraint sense. -/
  isLinearlyConstrained : P.IsLinearlyConstrained
  /-- The source objective is quadratic. -/
  hasQuadraticObjective : P.HasQuadraticObjective

/-- The predicate `IsQuadraticProgramming` is proof-irrelevant. -/
instance isQuadraticProgramming_subsingleton (P : StandardConstrainedOptimizationProblem n m) :
    Subsingleton P.IsQuadraticProgramming := inferInstance

/-- `IsQuadraticProgramming` means linear constraints together with a quadratic objective. -/
theorem isQuadraticProgramming_iff (P : StandardConstrainedOptimizationProblem n m) :
    P.IsQuadraticProgramming ↔ P.IsLinearlyConstrained ∧ P.HasQuadraticObjective :=
  ⟨fun h ↦ ⟨h.isLinearlyConstrained, h.hasQuadraticObjective⟩, fun h ↦ ⟨h.1, h.2⟩⟩

end StandardConstrainedOptimizationProblem

end
