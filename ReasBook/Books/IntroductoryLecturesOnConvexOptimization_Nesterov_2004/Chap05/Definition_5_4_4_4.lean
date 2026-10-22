/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped RealSymmetricMatrixSpace

variable {m n : ℕ}

/- Definition 5.4.4.4 lies in the semidefinite optimization domain.

Sampled owner-style declarations:
* `𝕊^n` in `Chap05/Definition_5_4_4_1`, the chapter owner for real symmetric matrices;
* `RealSymmetricMatrixSpace.frobeniusInner` in `Chap05/Definition_5_4_4_2`, the chapter owner
  for the Frobenius pairing on `𝕊^n`;
* `PrimalEqualityConstrainedProblem` and `PrimalEqualityConstrainedProblem.equalityFeasibleSet`
  in `Chap02/Definition_2_30`, the project owners for linear equality-constrained minimization;
* `realSymmetricMatrixConstraintMap` in `Chap05/Definition_5_4_4_6`, the chapter owner for the
  linear map encoding the SDP Frobenius equality constraints;
* `realSymmetricMatrixAssociatedAffineSubspace` in `Chap05/Definition_5_4_4_6`, the chapter
  owner for the affine slice cut out by the same equality constraints.

Best owner abstraction:
* source-facing: `SemidefiniteOptimizationProblem n m`, which stores exactly the SDP-specific
  primitive data `C ∈ 𝕊^n`, `A₁, …, Aₘ ∈ 𝕊^n`, and `b`;
* core/canonical: `PrimalEqualityConstrainedProblem (𝕊^n) (EuclideanSpace ℝ (Fin m))`;
* bridge/view:
  `toPrimalEqualityConstrainedProblem`, with the Chapter 1 owner recovered as `primalProblem`.

Primitive data:
* `costMatrix : 𝕊^n`;
* `constraintMatrices : Fin m → 𝕊^n`;
* `rhs : EuclideanSpace ℝ (Fin m)`.

Derived API:
* the linear objective `problem.objective`, equivalently the trace pairing with `C`;
* the canonical equality-constrained owner
  `problem.toPrimalEqualityConstrainedProblem`;
* the SDP feasible set `problem.feasibleSet`, canonically identified with
  `problem.toPrimalEqualityConstrainedProblem.equalityFeasibleSet`;
* the affine slice
  `realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs`;
* the derived Chapter 1 optimization owner
  `problem.toSetConstrainedMinimizationProblem`;
* coercion of `problem` to its intrinsic objective function on `𝕊^n`.

Source/core/bridge triage:
* source-facing: the SDP data `(C, A, b)`;
* core/canonical:
  `PrimalEqualityConstrainedProblem (𝕊^n) (EuclideanSpace ℝ (Fin m))`;
* bridge/view:
  `toPrimalEqualityConstrainedProblem`, `affineSlice`, and the derived `primalProblem`.

The file therefore keeps the textbook SDP data as the public source-facing owner, but it no
longer carries a parallel coordinate-model owner on `EuclideanSpace ℝ (Fin n × Fin n)`;
its canonical constraint owner is now `toPrimalEqualityConstrainedProblem`, and the Chapter 1
optimization owner is only the derived `primalProblem` view. -/

/-- Definition 5.4.4.4: a semidefinite optimization problem is determined by a cost matrix
`C ∈ 𝕊^n`, a finite family of constraint matrices `A₁, …, Aₘ ∈ 𝕊^n`, and a right-hand side
vector `b`. Its canonical owner bridge is the equality-constrained problem
`toPrimalEqualityConstrainedProblem`, whose `primalProblem` recovers the Chapter 1 set-constrained
optimization view. -/
structure SemidefiniteOptimizationProblem (n m : ℕ) where
  /-- The cost matrix `C ∈ 𝕊^n`. -/
  costMatrix : 𝕊^n
  /-- The family of constraint matrices `A₁, …, Aₘ ∈ 𝕊^n`. -/
  constraintMatrices : Fin m → 𝕊^n
  /-- The right-hand side vector `b ∈ ℝᵐ`. -/
  rhs : EuclideanSpace ℝ (Fin m)

namespace SemidefiniteOptimizationProblem

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/-- The affine slice cut out by the Frobenius equality constraints of an SDP. -/
abbrev affineSlice
    (problem : SemidefiniteOptimizationProblem n m) :
    AffineSubspace ℝ SymmMat :=
  realSymmetricMatrixAssociatedAffineSubspace
    problem.constraintMatrices
    problem.rhs

/-- The objective of a semidefinite optimization problem is the Frobenius pairing with the cost
matrix `C`. For symmetric matrices this is the same as `X ↦ trace (C * X)`. -/
def objective (problem : SemidefiniteOptimizationProblem n m) :
    SymmMat → ℝ :=
  fun X ↦ ⟪problem.costMatrix, X⟫_F

private def ambientProblem
    (problem : SemidefiniteOptimizationProblem n m) :
    SetConstrainedMinimizationProblem SymmMat where
  feasibleSet := (𝕊^n₊ : Set SymmMat)
  objective := problem.objective

/-- The canonical equality-constrained owner attached to an SDP. Its ambient feasible set is the
positive-semidefinite cone `𝕊ⁿ₊`, while the equality data are carried by the Frobenius
constraint map `realSymmetricMatrixConstraintMap problem.constraintMatrices` and the vector
`problem.rhs`. -/
def toPrimalEqualityConstrainedProblem
    (problem : SemidefiniteOptimizationProblem n m) :
    PrimalEqualityConstrainedProblem SymmMat Eₘ :=
  problem.ambientProblem.toPrimalEqualityConstrainedProblem
    (realSymmetricMatrixConstraintMap problem.constraintMatrices)
    problem.rhs

/-- The feasible set of a semidefinite optimization problem is the equality-feasible region of
its canonical equality-constrained owner. -/
def feasibleSet (problem : SemidefiniteOptimizationProblem n m) :
    Set SymmMat :=
  problem.toPrimalEqualityConstrainedProblem.equalityFeasibleSet

/-- The canonical Chapter 1 owner attached to an SDP is the `primalProblem` of its equality owner.
-/
def toSetConstrainedMinimizationProblem
    (problem : SemidefiniteOptimizationProblem n m) :
    SetConstrainedMinimizationProblem SymmMat :=
  problem.toPrimalEqualityConstrainedProblem.primalProblem

/-- The equality-owner bridge preserves the ambient positive-semidefinite cone. -/
@[simp] theorem toPrimalEqualityConstrainedProblem_feasibleSet
    (problem : SemidefiniteOptimizationProblem n m) :
    problem.toPrimalEqualityConstrainedProblem.feasibleSet = (𝕊^n₊ : Set SymmMat) :=
  rfl

/-- The equality-owner bridge records the SDP Frobenius constraint map. -/
@[simp] theorem toPrimalEqualityConstrainedProblem_A
    (problem : SemidefiniteOptimizationProblem n m) :
    problem.toPrimalEqualityConstrainedProblem.A =
      realSymmetricMatrixConstraintMap problem.constraintMatrices :=
  rfl

/-- The equality-owner bridge records the SDP right-hand side. -/
@[simp] theorem toPrimalEqualityConstrainedProblem_b
    (problem : SemidefiniteOptimizationProblem n m) :
    problem.toPrimalEqualityConstrainedProblem.b = problem.rhs :=
  rfl

/-- The equality-owner bridge evaluates to the SDP trace objective. -/
@[simp] theorem toPrimalEqualityConstrainedProblem_apply
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    problem.toPrimalEqualityConstrainedProblem X = problem.objective X :=
  rfl

/-- The SDP feasible set is definitionally the equality-feasible set of the canonical owner. -/
@[simp] theorem toPrimalEqualityConstrainedProblem_equalityFeasibleSet
    (problem : SemidefiniteOptimizationProblem n m) :
    problem.toPrimalEqualityConstrainedProblem.equalityFeasibleSet = problem.feasibleSet :=
  rfl

/-- The owner bridge preserves the SDP feasible set. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : SemidefiniteOptimizationProblem n m) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- The owner bridge evaluates to the SDP trace objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    problem.toSetConstrainedMinimizationProblem X = problem.objective X :=
  rfl

/-- A semidefinite optimization problem can be used as its ambient objective function. -/
instance : CoeFun (SemidefiniteOptimizationProblem n m) (fun _ ↦ SymmMat → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Membership in the canonical affine slice is exactly the family of Frobenius equality
constraints. -/
@[simp] theorem mem_affineSlice_iff
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    X ∈ problem.affineSlice ↔
      ∀ i : Fin m, ⟪problem.constraintMatrices i, X⟫_F = problem.rhs i := by
  simpa [affineSlice] using
    (mem_realSymmetricMatrixAssociatedAffineSubspace_iff :
      X ∈ realSymmetricMatrixAssociatedAffineSubspace
            problem.constraintMatrices
            problem.rhs ↔
          ∀ i : Fin m, ⟪problem.constraintMatrices i, X⟫_F = problem.rhs i)

/-- The SDP affine slice is exactly the level set where the canonical equality-constraint map
takes the value `problem.rhs`. -/
@[simp] theorem constraintMap_eq_rhs_iff_mem_affineSlice
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    realSymmetricMatrixConstraintMap problem.constraintMatrices X = problem.rhs ↔
      X ∈ problem.affineSlice := by
  rw [problem.mem_affineSlice_iff]
  constructor
  · intro h i
    simpa using congrArg (fun v : Eₘ ↦ v i) h
  · intro h
    apply PiLp.ext
    intro i
    simpa using h i

/-- Membership in the feasible set is exactly positive semidefiniteness together with membership
in the canonical affine slice defined by the equality constraints. -/
@[simp] theorem mem_feasibleSet_iff_mem_affineSlice
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    X ∈ problem.feasibleSet ↔
      X ∈ 𝕊^n₊ ∧ X ∈ problem.affineSlice :=
  by
    rw [feasibleSet, PrimalEqualityConstrainedProblem.mem_equalityFeasibleSet_iff,
      problem.toPrimalEqualityConstrainedProblem_feasibleSet,
      problem.toPrimalEqualityConstrainedProblem_A,
      problem.toPrimalEqualityConstrainedProblem_b,
      problem.constraintMap_eq_rhs_iff_mem_affineSlice]

-- Proof sketch: rewrite `problem.feasibleSet` through
-- `problem.toPrimalEqualityConstrainedProblem.equalityFeasibleSet`, then expand the chapter
-- equality-owner membership lemma and the affine-slice characterization.
/-- Membership in the feasible set of a semidefinite optimization problem is exactly
positive-semidefiniteness together with the Frobenius constraints. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    X ∈ problem.feasibleSet ↔
      X ∈ 𝕊^n₊ ∧
        ∀ i : Fin m, ⟪problem.constraintMatrices i, X⟫_F = problem.rhs i :=
  by
    rw [mem_feasibleSet_iff_mem_affineSlice, problem.mem_affineSlice_iff]

/-- Expanding feasibility through the chapter cone owner `𝕊ⁿ₊` recovers the canonical matrix
predicate `Matrix.PosSemidef`. -/
theorem mem_feasibleSet_iff_posSemidef
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    X ∈ problem.feasibleSet ↔
      (X : Mat).PosSemidef ∧
        ∀ i : Fin m, ⟪problem.constraintMatrices i, X⟫_F = problem.rhs i := by
  rw [mem_feasibleSet_iff, mem_positiveSemidefiniteCone_iff]

-- Proof sketch: unfold `objective`; the value at `X` is definitionally `⟪C, X⟫_F`.
/-- Evaluating the objective of a semidefinite optimization problem returns the Frobenius pairing
with the cost matrix. -/
@[simp] theorem objective_apply
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    problem.objective X = ⟪problem.costMatrix, X⟫_F :=
  rfl

/-- Evaluating the objective also recovers the textbook trace formula `trace (C * X)`. -/
theorem objective_eq_trace
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    problem.objective X = trace ((problem.costMatrix : Mat) * (X : Mat)) := by
  have hC : (problem.costMatrix : Mat).IsSymm :=
    RealSymmetricMatrixSpace.isSymm problem.costMatrix
  rw [objective_apply, RealSymmetricMatrixSpace.frobeniusInner_def]
  simp [hC.eq]

/-- Evaluating an SDP as a function returns its trace objective value. -/
@[simp] theorem coe_apply
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    problem X = ⟪problem.costMatrix, X⟫_F :=
  rfl

end SemidefiniteOptimizationProblem

end
