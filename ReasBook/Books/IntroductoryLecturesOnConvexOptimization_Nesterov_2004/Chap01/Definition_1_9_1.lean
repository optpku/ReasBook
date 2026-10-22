/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_8_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

/- Definition 1.9.1 lies in the finite-dimensional quadratic optimization domain.

Sampled owner-style declarations:
* `Matrix.PosDef`, which canonically packages symmetry together with positive definiteness;
* `Matrix.PosDef.inv`, which supplies the inverse positive-definite matrix used in `A⁻¹`;
* `SetConstrainedMinimizationProblem`, the Chapter 1 owner of an ambient feasible set and
  objective function;
* `SetConstrainedMinimizationProblem.toGeneralMinimizationProblem`, the canonical bridge to the
  earlier minimization-problem owner.

Best owner abstractions:
* `Matrix.PosDef` for the Hessian-side linear-algebra data;
* `SetConstrainedMinimizationProblem` for the ambient unconstrained minimization problem.

Primitive data:
* `α`, `a`, `A : Mat`, and `posDef : A.PosDef`

Derived API:
* `A`
* `posDef`
* `objective`
* `minimizer`
* `toSetConstrainedMinimizationProblem`
* the coercion to the ambient objective function through
  `toSetConstrainedMinimizationProblem`

Source/core/bridge triage:
* source-facing: `UnconstrainedQuadraticMinimizationProblem`
* core/canonical: `Matrix.PosDef`, `SetConstrainedMinimizationProblem`
* bridge/view: `toSetConstrainedMinimizationProblem`
-/

/-- The quadratic objective `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪Ax, x⟫` on `ℝⁿ`. -/
def quadraticObjective {n : ℕ} (α : ℝ) (a : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x ↦ α + inner ℝ a x + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x

/-- Definition 1.9.1: An unconstrained quadratic minimization problem on `ℝⁿ` is determined by a
constant term `α`, a linear coefficient `a`, and a symmetric positive-definite matrix `A`, with
objective function `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪Ax, x⟫`, minimized over all `x ∈ ℝⁿ`. The symmetry
is carried canonically by `Matrix.PosDef`, while the ambient unconstrained minimization problem is
recovered through `toSetConstrainedMinimizationProblem`. -/
structure UnconstrainedQuadraticMinimizationProblem (n : ℕ) where
  α : ℝ
  a : EuclideanSpace ℝ (Fin n)
  A : Matrix (Fin n) (Fin n) ℝ
  posDef : A.PosDef

namespace UnconstrainedQuadraticMinimizationProblem

variable {n : ℕ}

/-- The objective function attached to an unconstrained quadratic minimization problem. -/
def objective (problem : UnconstrainedQuadraticMinimizationProblem n) :=
  quadraticObjective problem.α problem.a problem.A

/-- The canonical critical point `-A⁻¹ a` of an unconstrained quadratic minimization problem. -/
def minimizer (problem : UnconstrainedQuadraticMinimizationProblem n) :=
  -((problem.A⁻¹).toEuclideanLin problem.a)

/-- The ambient Chapter 1 owner attached to an unconstrained quadratic minimization problem. -/
def toSetConstrainedMinimizationProblem
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n)) where
  feasibleSet := Set.univ
  objective := problem.objective

/-- The ambient feasible set of an unconstrained quadratic minimization problem is all of `ℝⁿ`. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = Set.univ :=
  rfl

/-- The owner bridge evaluates to the quadratic objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : EuclideanSpace ℝ (Fin n)) :
    problem.toSetConstrainedMinimizationProblem x = problem.objective x :=
  rfl

/-- An unconstrained quadratic minimization problem coerces to its objective through the canonical
ambient Chapter 1 owner. -/
instance : CoeFun (UnconstrainedQuadraticMinimizationProblem n)
    (fun _ : UnconstrainedQuadraticMinimizationProblem n ↦ EuclideanSpace ℝ (Fin n) → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating an unconstrained quadratic minimization problem returns its objective value. -/
@[simp] theorem coe_apply (problem : UnconstrainedQuadraticMinimizationProblem n)
    (x : EuclideanSpace ℝ (Fin n)) :
    problem x = problem.objective x :=
  rfl

end UnconstrainedQuadraticMinimizationProblem
