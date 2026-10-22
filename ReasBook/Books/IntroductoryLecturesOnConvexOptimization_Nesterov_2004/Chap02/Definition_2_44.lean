/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped StrongConvexSmooth

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

/- Definition 2.44 lies in the domain of smooth inequality-constrained minimization on a real
Hilbert space.

Sampled owner-style declarations:
* `LagrangianProblem E m` in `Chap01/Definition_1_10_2`, which already owns the primitive
  objective-and-constraint data `f₀, fᵢ`;
* `FunctionalConstraintsMinimizationProblem E m` in `Chap01/Definition_1_1_3`, which owns the
  feasible-set predicate and `IsMinOn` surface for finite scalar constraints on an ambient set;
* `𝓢[μ, L]¹¹`, `IsStrongConvexSmoothObjective μ L`, and `mem_S11_iff` in `Definition_2_17`,
  which own the source-facing and canonical regularity interfaces for `f₀` and each `fᵢ`.

Best owner abstraction:
* the primitive objective-and-constraint owner is `LagrangianProblem E m`;
* the feasible-set/optimality bridge is `FunctionalConstraintsMinimizationProblem E m`.

Primitive data:
* the ambient set `Q ⊆ E` together with its nonemptiness, closedness, and convexity;
* the inherited `LagrangianProblem E m` data `objective` and `constraints`;
* the regularity fields `objective_mem` and `constraints_mem`, stated in the chapter notation
  `𝓢[μ, L]¹¹`.

Derived API:
* the canonical parent projection `problem.toLagrangianProblem`;
* the owner feasible-set bridge `problem.toFunctionalConstraintsMinimizationProblem`;
* the feasible-set rewrite `problem.mem_feasibleSet_iff`.

Source/core/bridge triage:
* source-facing: `SmoothFunctionalConstraintsMinimizationProblem`;
* core/canonical: `LagrangianProblem E m` and `FunctionalConstraintsMinimizationProblem E m`;
* bridge/view: `toFunctionalConstraintsMinimizationProblem`.

Accordingly this file keeps only the ambient-set and regularity data specific to Definition 2.44
and reuses the Chapter 1 Lagrangian owner for the primitive functional data. The textbook
`ℝⁿ` presentation is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/

/-- Definition 2.44: a smooth convex constrained minimization problem with parameters `μ` and `L`
consists of a nonempty simple closed convex set `Q ⊆ E`, an objective `f₀ : E → ℝ`, and
constraint functions `fᵢ : E → ℝ` for `i = 1, …, m`, where every component belongs to
`𝓢[μ, L]¹¹`; the associated problem is to minimize `f₀` over points `x ∈ Q` satisfying
`fᵢ(x) ≤ 0` for all constraints. The textbook `ℝⁿ` case is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
structure SmoothFunctionalConstraintsMinimizationProblem
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (m : ℕ) (μ L : ℝ)
    extends LagrangianProblem E m where
  /-- The ambient closed convex set `Q ⊆ E` on which the constrained problem is posed. -/
  ambientSet : Set E
  /-- The ambient set `Q` is nonempty. -/
  ambient_nonempty : ambientSet.Nonempty
  /-- The ambient set `Q` is closed. -/
  ambient_closed : IsClosed ambientSet
  /-- The ambient set `Q` is convex. -/
  ambient_convex : Convex ℝ ambientSet
  /-- The objective belongs to the smooth strongly convex class `𝓢[μ, L]¹¹`. -/
  objective_mem : objective ∈ 𝓢[μ, L]¹¹
  /-- Every constraint component belongs to the same smooth strongly convex class `𝓢[μ, L]¹¹`. -/
  constraints_mem : ∀ i : Fin m, constraints i ∈ 𝓢[μ, L]¹¹

/-- A smooth constrained minimization problem can be used as its ambient objective function. -/
instance : CoeFun (SmoothFunctionalConstraintsMinimizationProblem E m μ L) (fun _ ↦ E → ℝ) where
  coe problem := problem.objective

namespace SmoothFunctionalConstraintsMinimizationProblem

@[simp] theorem coe_apply
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (x : E) :
    problem x = problem.objective x :=
  rfl

/- The Chapter 1 owner abstraction attached to the ambient functional-constraint data, with all
constraint senses equal to `≤`. -/
def toFunctionalConstraintsMinimizationProblem
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) :
    FunctionalConstraintsMinimizationProblem E m where
  basicFeasibleSet := problem.ambientSet
  objective := fun x ↦ problem.objective x
  constraints := fun i x ↦ problem.constraints i x
  senses := fun _ ↦ .le

/-- The owner bridge has only inequality constraints. -/
@[simp] theorem toFunctionalConstraintsMinimizationProblem_hasLeConstraints
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) :
    problem.toFunctionalConstraintsMinimizationProblem.HasLeConstraints :=
  fun _ ↦ rfl

/-- Membership in the owner feasible set is exactly satisfaction of the inequality constraints on
the ambient set `Q`. -/
@[simp]
theorem mem_feasibleSet_iff
    {problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L}
    {x : problem.ambientSet} :
    x ∈ problem.toFunctionalConstraintsMinimizationProblem.feasibleSet ↔
      ∀ i : Fin m, problem.constraints i x ≤ 0 := by
  simpa [toFunctionalConstraintsMinimizationProblem] using
    (problem.toFunctionalConstraintsMinimizationProblem.mem_feasibleSet_iff
      problem.toFunctionalConstraintsMinimizationProblem_hasLeConstraints)

/- A global minimizer of Definition 2.44 is expressed directly by the Chapter 1 owner predicate
`IsMinOn
    problem.toFunctionalConstraintsMinimizationProblem.objective
    problem.toFunctionalConstraintsMinimizationProblem.feasibleSet
    xStar`
for `xStar : problem.toFunctionalConstraintsMinimizationProblem.feasibleSet`.

No additional wrapper declaration is needed here. -/

end SmoothFunctionalConstraintsMinimizationProblem
