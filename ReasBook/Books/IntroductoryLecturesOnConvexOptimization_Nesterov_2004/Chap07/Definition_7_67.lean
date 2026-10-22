/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Theorem_7_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (nonnegativeOrthant positiveOrthant)
open Matrix
open scoped Matrix

variable {m : ℕ} {n : ℕ+}

/- Definition 7.67 lies in Chapter 7's fractional-covering / finite-dimensional constrained-
optimization domain.

Sampled owner-style declarations:
- `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.positiveOrthant` in
  `Chap01/Definition_1_10_2`, the project owners for coordinatewise sign constraints;
- `orthantHalfspacePolyhedron` and `mem_orthantHalfspacePolyhedron_iff` in `Chap07/Theorem_7_9`,
  the chapter owner and membership API for orthant-constrained finite halfspace systems;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  owner optimal-value layer for real objectives on explicit feasible sets;
- `Finset.inf'` in mathlib, the canonical owner for minima over nonempty finite families;
- `LinearPackingProblem` in `Chap07/Definition_7_41`, the nearby Chapter 7 pattern for keeping
  the source-facing LP data while delegating sign conditions and optimization value to those
  owners.

Best owner abstraction:
- source-facing: `FractionalCoveringProblem m n`;
- core/canonical: `nonnegativeOrthant`, `positiveOrthant`, `orthantHalfspacePolyhedron`,
  `SetConstrainedMinimizationProblem`, and `Finset.inf'`;
- bridge/view: the sign-flipped column family of `A` realizing the covering inequalities as an
  orthant-halfspace system, together with `problem.toSetConstrainedMinimizationProblem` and the
  `sInf` expansions of `problem.optimalValue` and `problem.concaveFunctional`.

Primitive data:
- the covering matrix `A : Matrix (Fin m) (Fin n) ℝ`;
- the right-hand side `b : EuclideanSpace ℝ (Fin m)`;
- the cost vector `c : EuclideanSpace ℝ (Fin n)`;
- the coordinatewise nonnegativity of `A`, and positivity of `b` and `c`.

Derived API:
- coordinatewise sign lemmas for `A`, `b`, and `c`;
- the canonical nonemptiness of the column family coming from the ambient positive dimension
  `n : ℕ+`;
- the feasible set, through the chapter owner `orthantHalfspacePolyhedron`, and the covering
  objective;
- the canonical constrained-minimization owner and its `EReal` optimal value;
- the source-facing normalized-coverage functional `ψ`, together with its finite-minimum and
  `sInf` expansion theorems.

This refinement keeps the textbook covering owner, but removes the duplicate raw-real optimal-value
wheel in favor of the Chapter 1 constrained-minimization owner. It also expresses the feasible
region through the chapter's orthant-halfspace owner instead of a duplicate raw set, and the `ψ`
functional reuses mathlib's nonempty finite-family owner `Finset.inf'` with nonemptiness coming
from the ambient positive column count `n : ℕ+` instead of public proof baggage.
-/

/-- Definition 7.67: a fractional covering problem is specified by a nonnegative matrix
`A ∈ ℝ_+^{m × n}`, a strictly positive right-hand side `b ∈ ℝ_{++}^m`, and a strictly positive
cost vector `c ∈ ℝ_{++}^n`; the column dimension is part of the ambient parameter `n : ℕ+`, so
the textbook `ψ(y) = min_j (Aᵀ y)_j / c_j` is a genuine finite minimum without extra witness
fields. The associated feasible set, optimal value `φ_*`, and concave functional `ψ` are defined
below. -/
structure FractionalCoveringProblem (m : ℕ) (n : ℕ+) where
  /-- The nonnegative covering matrix `A`. -/
  matrix : Matrix (Fin m) (Fin (n : ℕ)) ℝ
  /-- The strictly positive right-hand side vector `b`. -/
  rhs : EuclideanSpace ℝ (Fin m)
  /-- The strictly positive cost vector `c`. -/
  cost : EuclideanSpace ℝ (Fin (n : ℕ))
  /-- Every entry of `A` is nonnegative. -/
  matrix_nonneg (i : Fin m) (j : Fin (n : ℕ)) : 0 ≤ matrix i j
  /-- The right-hand side lies in the positive orthant. -/
  rhs_pos : rhs ∈ positiveOrthant m
  /-- The cost vector lies in the positive orthant. -/
  cost_pos : cost ∈ positiveOrthant n

namespace FractionalCoveringProblem

/-- Coordinatewise nonnegativity of the covering matrix. -/
@[simp] theorem matrix_nonneg_apply
    (problem : FractionalCoveringProblem m n) (i : Fin m) (j : Fin (n : ℕ)) :
    0 ≤ problem.matrix i j := by
  exact problem.matrix_nonneg i j

/-- Coordinatewise positivity of the right-hand side vector. -/
@[simp] theorem rhs_pos_apply
    (problem : FractionalCoveringProblem m n) (i : Fin m) :
    0 < problem.rhs i := by
  exact (show ∀ k : Fin m, 0 < problem.rhs k by simpa using problem.rhs_pos) i

/-- Coordinatewise positivity of the cost vector. -/
@[simp] theorem cost_pos_apply
    (problem : FractionalCoveringProblem m n) (j : Fin (n : ℕ)) :
    0 < problem.cost j := by
  exact (show ∀ k : Fin (n : ℕ), 0 < problem.cost k by simpa using problem.cost_pos) j

private def column
    (problem : FractionalCoveringProblem m n) (j : Fin (n : ℕ)) :
    EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦ problem.matrix i j

@[simp] private theorem column_apply
    (problem : FractionalCoveringProblem m n) (j : Fin (n : ℕ)) (i : Fin m) :
    problem.column j i = problem.matrix i j := by
  simp [column]

@[simp] private theorem inner_column_eq_transpose_mulVec
    (problem : FractionalCoveringProblem m n) (j : Fin (n : ℕ))
    (y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (problem.column j) y = (problem.matrixᵀ.mulVec y) j := by
  simpa [column, EuclideanSpace.equiv, Matrix.mulVec, dotProduct, dotProduct_comm, mul_comm] using
    (EuclideanSpace.inner_eq_star_dotProduct (problem.column j) y)

/-- The feasible set of covering vectors `y`, realized as the chapter orthant-halfspace owner for
the sign-flipped column family of `A`; this is exactly the textbook system `Aᵀ y ≥ c`, `y ≥ 0`.
-/
abbrev feasibleSet (problem : FractionalCoveringProblem m n) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  orthantHalfspacePolyhedron
    (fun j ↦ -(problem.column j))
    (fun j ↦ -problem.cost j)

/-- Membership in the feasible set means `y ≥ 0` and `Aᵀ y ≥ c` coordinatewise. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : FractionalCoveringProblem m n) (y : EuclideanSpace ℝ (Fin m)) :
    y ∈ problem.feasibleSet ↔
      y ∈ nonnegativeOrthant m ∧
        ∀ j : Fin (n : ℕ), problem.cost j ≤ (problem.matrixᵀ.mulVec y) j := by
  rw [feasibleSet, mem_orthantHalfspacePolyhedron_iff]
  constructor
  · rintro ⟨hy_nonneg, hy_cover⟩
    refine ⟨hy_nonneg, fun j ↦ ?_⟩
    exact neg_le_neg_iff.mp <| by simpa using hy_cover j
  · rintro ⟨hy_nonneg, hy_cover⟩
    refine ⟨hy_nonneg, fun j ↦ ?_⟩
    simpa using neg_le_neg (hy_cover j)

/-- The covering objective `y ↦ ⟪b, y⟫`. -/
abbrev objective (problem : FractionalCoveringProblem m n) :
    EuclideanSpace ℝ (Fin m) → ℝ :=
  inner ℝ problem.rhs

/-- Evaluating the covering objective gives the inner product with the vector `b`. -/
@[simp] theorem objective_apply
    (problem : FractionalCoveringProblem m n) (y : EuclideanSpace ℝ (Fin m)) :
    problem.objective y = inner ℝ problem.rhs y :=
  rfl

/-- The canonical Chapter 1 constrained minimization owner attached to the fractional covering
problem. -/
def toSetConstrainedMinimizationProblem
    (problem : FractionalCoveringProblem m n) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin m)) where
  feasibleSet := problem.feasibleSet
  objective := problem.objective

@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : FractionalCoveringProblem m n) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : FractionalCoveringProblem m n) (y : EuclideanSpace ℝ (Fin m)) :
    problem.toSetConstrainedMinimizationProblem y = problem.objective y :=
  rfl

/-- A fractional covering problem can be used as its covering objective function. -/
instance : CoeFun (FractionalCoveringProblem m n)
    (fun _ ↦ EuclideanSpace ℝ (Fin m) → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

@[simp] theorem coe_apply
    (problem : FractionalCoveringProblem m n) (y : EuclideanSpace ℝ (Fin m)) :
    problem y = problem.objective y :=
  rfl

/-- The fractional covering optimal value `φ_*`, viewed through the canonical Chapter 1
constrained-minimization owner. -/
def optimalValue (problem : FractionalCoveringProblem m n) : EReal :=
  problem.toSetConstrainedMinimizationProblem.optimalValue

/-- The optimal value `φ_*` is the infimum of the objective over the feasible set, viewed in
`EReal`. -/
theorem optimalValue_eq_sInf_image
    (problem : FractionalCoveringProblem m n) :
    problem.optimalValue =
      sInf ((fun y ↦ (problem.objective y : EReal)) '' problem.feasibleSet) := by
  simpa [optimalValue] using
    problem.toSetConstrainedMinimizationProblem.optimalValue_eq_sInf_image

/-- The associated function `ψ(y) = min_i (Aᵀ y)_i / c_i`, written as the infimum of the finite
family of normalized column pairings. -/
def concaveFunctional (problem : FractionalCoveringProblem m n) :
    EuclideanSpace ℝ (Fin m) → ℝ :=
  fun y ↦ Finset.univ.inf' Finset.univ_nonempty
    (fun j : Fin (n : ℕ) ↦ (problem.matrixᵀ.mulVec y) j / problem.cost j)

/-- Evaluating `ψ` gives the finite minimum of the normalized coverages `(Aᵀ y)_j / c_j`. -/
@[simp] theorem concaveFunctional_apply
    (problem : FractionalCoveringProblem m n) (y : EuclideanSpace ℝ (Fin m)) :
    problem.concaveFunctional y =
      Finset.univ.inf' Finset.univ_nonempty
        (fun j : Fin (n : ℕ) ↦ (problem.matrixᵀ.mulVec y) j / problem.cost j) :=
  rfl

/-- The finite minimum defining `ψ` is the infimum of the same nonempty finite family viewed as a
set. -/
theorem concaveFunctional_eq_sInf_range
    (problem : FractionalCoveringProblem m n) (y : EuclideanSpace ℝ (Fin m)) :
    problem.concaveFunctional y =
      sInf (Set.range fun j : Fin (n : ℕ) ↦ (problem.matrixᵀ.mulVec y) j / problem.cost j) := by
  simp [concaveFunctional, Finset.inf'_eq_csInf_image]

end FractionalCoveringProblem

end
