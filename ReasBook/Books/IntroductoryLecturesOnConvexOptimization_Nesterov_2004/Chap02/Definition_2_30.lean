/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.LinearEqualityFeasibleSet

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin

universe u v

/- Primary domain: equality-constrained minimization and its Lagrangian dual layer.

Owner declarations sampled before refining this file:
* `SetConstrainedMinimizationProblem` and
  `SetConstrainedMinimizationProblem.optimalValue` in `Nesterov/Chap01/Definition_1_3_7.lean`;
* `LagrangianProblem.lagrangian`, `LagrangianProblem.dualFunction`, and
  `LagrangianProblem.lagrangianMinimizers` in `Nesterov/Chap01/Definition_1_10_2.lean`;
* `linearEqualityFeasibleSet` and `mem_linearEqualityFeasibleSet_iff` in
  `Nesterov/Chap03/LinearEqualityFeasibleSet.lean`;
* `LinearEqualityConstrainedConvexProblem` in `Nesterov/Chap03/Definition_3_27.lean`, which uses
  the same intrinsic linear-map owner for equality constraints.

Best owner abstractions:
* source-facing: `PrimalEqualityConstrainedProblem E Λ`;
* core/canonical: `SetConstrainedMinimizationProblem E` together with
  `linearEqualityFeasibleSet Q A b`;
* bridge/view: the Euclidean matrix presentation obtained by specializing `E`, `Λ`, and using
  `Matrix.toEuclideanLin`.

Primitive data:
* the ambient feasible set / objective owner `SetConstrainedMinimizationProblem E`;
* the linear map `A : E →ₗ[ℝ] Λ`;
* the right-hand side `b : Λ`.

Derived API:
* `equalityFeasibleSet`;
* `primalProblem` and `primalOptimalValue`;
* `constraintResidual` on the additive codomain layer;
* `lagrangianSubproblem`, `lagrangian`, `dualFunction`, and `lagrangianMinimizers`.

This refinement deletes the matrix-specific primitive owner layer from Definition 2.30 itself.
The textbook matrix realization remains available by passing `A.toEuclideanLin` to the intrinsic
owner. -/

/-- Definition 2.30: a primal equality-constrained problem consists of an ambient feasible set
`Q`, an objective `f`, a linear map `A`, and a right-hand side `b`, encoding
`f^* = min {f(x) | x ∈ Q, A x = b}`. In the textbook Euclidean presentation, the linear map is
represented by a matrix via `Matrix.toEuclideanLin`. -/
structure PrimalEqualityConstrainedProblem
    (E : Type u) (Λ : Type v) [AddCommMonoid E] [Module ℝ E] [AddCommMonoid Λ] [Module ℝ Λ]
    extends SetConstrainedMinimizationProblem E where
  /-- The linear equality map. -/
  A : E →ₗ[ℝ] Λ
  /-- The right-hand side of the equality constraint. -/
  b : Λ

/-- A primal equality-constrained problem can be used as its ambient objective function. -/
instance {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid Λ] [Module ℝ Λ] :
    CoeFun (PrimalEqualityConstrainedProblem E Λ) (fun _ ↦ E → ℝ) where
  coe problem := problem.objective

namespace SetConstrainedMinimizationProblem

variable {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid Λ] [Module ℝ Λ]

/-- The Chapter 2 equality-constrained owner attached to an ambient feasible set and objective,
together with linear equality data `A x = b`. -/
def toPrimalEqualityConstrainedProblem (problem : SetConstrainedMinimizationProblem E)
    (A : E →ₗ[ℝ] Λ) (b : Λ) : PrimalEqualityConstrainedProblem E Λ where
  toSetConstrainedMinimizationProblem := problem
  A := A
  b := b

@[simp] theorem toPrimalEqualityConstrainedProblem_feasibleSet
    (problem : SetConstrainedMinimizationProblem E) (A : E →ₗ[ℝ] Λ) (b : Λ) :
    (problem.toPrimalEqualityConstrainedProblem A b).feasibleSet = problem.feasibleSet :=
  rfl

@[simp] theorem toPrimalEqualityConstrainedProblem_apply
    (problem : SetConstrainedMinimizationProblem E) (A : E →ₗ[ℝ] Λ) (b : Λ) (x : E) :
    problem.toPrimalEqualityConstrainedProblem A b x = problem x :=
  rfl

@[simp] theorem toPrimalEqualityConstrainedProblem_A
    (problem : SetConstrainedMinimizationProblem E) (A : E →ₗ[ℝ] Λ) (b : Λ) :
    (problem.toPrimalEqualityConstrainedProblem A b).A = A :=
  rfl

@[simp] theorem toPrimalEqualityConstrainedProblem_b
    (problem : SetConstrainedMinimizationProblem E) (A : E →ₗ[ℝ] Λ) (b : Λ) :
    (problem.toPrimalEqualityConstrainedProblem A b).b = b :=
  rfl

end SetConstrainedMinimizationProblem

namespace PrimalEqualityConstrainedProblem

variable {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid Λ] [Module ℝ Λ]

/-- The equality-feasible region `Q ∩ {x | A x = b}` attached to the ambient problem. -/
def equalityFeasibleSet (problem : PrimalEqualityConstrainedProblem E Λ) : Set E :=
  linearEqualityFeasibleSet problem.feasibleSet problem.A problem.b

/-- Membership in the equality-feasible region means ambient feasibility together with
`A x = b`. -/
@[simp] theorem mem_equalityFeasibleSet_iff
    {problem : PrimalEqualityConstrainedProblem E Λ} {x : E} :
    x ∈ problem.equalityFeasibleSet ↔ x ∈ problem.feasibleSet ∧ problem.A x = problem.b := by
  rw [equalityFeasibleSet, mem_linearEqualityFeasibleSet_iff]

/-- The set-constrained minimization problem obtained by restricting the ambient feasible region
to the equality-feasible points. -/
def primalProblem (problem : PrimalEqualityConstrainedProblem E Λ) :
    SetConstrainedMinimizationProblem E where
  feasibleSet := problem.equalityFeasibleSet
  objective := problem

/-- The primal optimal value `f^*`, interpreted as the extended-real infimum of the objective
over the equality-feasible set. -/
def primalOptimalValue (problem : PrimalEqualityConstrainedProblem E Λ) : EReal :=
  problem.primalProblem.optimalValue

section AdditiveCodomain

variable [AddCommGroup Λ]

/-- The equality-constraint residual `b - A x`. -/
def constraintResidual (problem : PrimalEqualityConstrainedProblem E Λ) (x : E) : Λ :=
  problem.b - problem.A x

/-- Vanishing of the equality-constraint residual is exactly the linear equation `A x = b`. -/
theorem constraintResidual_eq_zero_iff
    {problem : PrimalEqualityConstrainedProblem E Λ} {x : E} :
    problem.constraintResidual x = 0 ↔ problem.A x = problem.b := by
  constructor
  · intro hx
    simpa [constraintResidual] using (sub_eq_zero.mp (by simpa [constraintResidual] using hx)).symm
  · intro hx
    simpa [constraintResidual] using sub_eq_zero.mpr hx.symm

/-- Membership in the equality-feasible region is equivalent to ambient feasibility together with
vanishing equality residual. -/
@[simp] theorem mem_equalityFeasibleSet_iff_constraintResidual_eq_zero
    {problem : PrimalEqualityConstrainedProblem E Λ} {x : E} :
    x ∈ problem.equalityFeasibleSet ↔
      x ∈ problem.feasibleSet ∧ problem.constraintResidual x = 0 := by
  rw [problem.mem_equalityFeasibleSet_iff, problem.constraintResidual_eq_zero_iff]

end AdditiveCodomain

section LagrangianDuality

variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]

/-- The equality-problem Lagrangian `𝓛(x, u) = f(x) + ⟪u, b - A x⟫`. -/
def lagrangian (problem : PrimalEqualityConstrainedProblem E Λ) (x : E) (u : Λ) : ℝ :=
  problem x + inner ℝ u (problem.constraintResidual x)

/-- The set-constrained subproblem obtained by minimizing the Lagrangian over the ambient feasible
set `Q`. -/
def lagrangianSubproblem (problem : PrimalEqualityConstrainedProblem E Λ)
    (u : Λ) : SetConstrainedMinimizationProblem E where
  feasibleSet := problem.feasibleSet
  objective := fun x ↦ problem.lagrangian x u

/-- The equality-problem dual function `φ(u) = inf_{x ∈ Q} 𝓛(x, u)`. -/
def dualFunction (problem : PrimalEqualityConstrainedProblem E Λ) (u : Λ) : EReal :=
  (problem.lagrangianSubproblem u).optimalValue

/-- The Lagrangian minimizer set `X*(u) = argmin_{x ∈ Q} 𝓛(x, u)`. -/
def lagrangianMinimizers (problem : PrimalEqualityConstrainedProblem E Λ)
    (u : Λ) : Set E :=
  argmin[problem.feasibleSet] fun x ↦ problem.lagrangian x u

/-- Membership in `X*(u)` means minimizing the equality-problem Lagrangian on the ambient set
`Q`. -/
@[simp] theorem mem_lagrangianMinimizers_iff
    {problem : PrimalEqualityConstrainedProblem E Λ} {u : Λ} {x : E} :
    x ∈ problem.lagrangianMinimizers u ↔
      x ∈ problem.feasibleSet ∧
        IsMinOn (fun y ↦ problem.lagrangian y u) problem.feasibleSet x := by
  rw [lagrangianMinimizers, mem_constrainedArgmin_iff]

/-- A point of `X*(u)` realizes the equality-problem dual value by evaluating the Lagrangian. -/
theorem dualFunction_eq_lagrangian
    (problem : PrimalEqualityConstrainedProblem E Λ) {u : Λ} {x : E}
    (hx : x ∈ problem.lagrangianMinimizers u) :
    problem.dualFunction u = (problem.lagrangian x u : EReal) := by
  simpa [dualFunction, lagrangianSubproblem, lagrangianMinimizers] using
    (problem.lagrangianSubproblem u).optimalValue_eq_of_mem_argmin hx

end LagrangianDuality

end PrimalEqualityConstrainedProblem
