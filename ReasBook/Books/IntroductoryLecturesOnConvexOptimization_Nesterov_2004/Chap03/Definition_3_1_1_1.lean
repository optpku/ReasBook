/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped WithTopConvexAnalysis

/-
Definition 3.1.1.1 lies in the convex constrained minimization domain.

Sampled owner-style declarations:
- `withTopEffectiveDomain`, `withTopRealPart`, and `constrainedEpigraph` in `Definition_3_3`, the
  earlier chapter owner layer for `WithTop`-valued convex-analysis data and its canonical
  epigraph bridge;
- `GeneralMinimizationProblem` in `Chap01/Definition_1_1_3`, the earlier project owner for a
  feasible set together with finitely many scalar constraints on a subtype;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the earlier project owner for
  the ambient feasible set and real-valued objective layer of a constrained problem;
- `ConvexInequalityConstrainedMinimizationProblem` in `Chap05/Definition_5_0_1`, the later
  whole-space real-valued convex inequality owner.

Best owner abstraction:
- `GeneralConvexMinimizationProblem X m` for the source-facing constrained minimization problem on
  a real ambient space `X`;
- `Definition_3_3` remains the owner for the ambient `WithTop` epigraph bridge;
- the textbook `ℝⁿ` formulation is a specialization of this owner, not its primitive core.

Primitive data:
- `feasibleSet`
- `objective`
- `constraints`
- the closedness and convexity witnesses.

Derived API:
- the coercion to the ambient objective function;
- the real-valued bridge `ofReal`, which reuses the Chapter 1 owner
  `SetConstrainedMinimizationProblem` for the feasible-set / objective layer;
- `GeneralConvexMinimizationProblem.IsFeasible` and its atomic consequence lemmas.

Source/core/bridge triage:
- source-facing: the textbook general convex minimization problem with convex inequality
  constraints;
- core/canonical: `GeneralConvexMinimizationProblem X m`;
- bridge/view: the textbook Euclidean specialization `X = EuclideanSpace ℝ (Fin n)`, together
  with the coercion to the ambient objective function and the feasibility lemmas; the ambient
  epigraph bridge is reused from `Definition_3_3`.

This file therefore keeps the chapter owner abstraction and does not collapse it to the earlier
Chapter 1 owners, whose objective and constraint data live on a subtype and in `ℝ` rather than as
ambient `WithTop ℝ` convex functions.
-/

/-- Definition 3.1.1.1, generalized from the textbook `ℝⁿ` setting: a general convex
minimization problem consists of minimizing an ambient extended-real-valued convex objective
function over a closed convex set `Q ⊆ X`, subject to finitely many ambient extended-real-valued
convex inequality constraints `fᵢ(x) ≤ 0`; no differentiability is assumed for the objective or
constraint functions. -/
structure GeneralConvexMinimizationProblem
    (X : Type u) [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] (m : ℕ) where
  /-- The ambient feasible set `Q ⊆ X`. -/
  feasibleSet : Set X
  /-- The ambient extended-real-valued objective function. -/
  objective : X → WithTop ℝ
  /-- The finitely many ambient extended-real-valued inequality constraints. -/
  constraints : Fin m → X → WithTop ℝ
  /-- The ambient feasible set `Q` is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The ambient feasible set `Q` is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The objective is convex in the Chapter 3 `WithTop` sense. -/
  objective_convex : ConvexOn ℝ (dom objective) (withTopRealPart objective)
  /-- Each inequality constraint is convex in the Chapter 3 `WithTop` sense. -/
  constraints_convex (i : Fin m) :
      ConvexOn ℝ (dom (constraints i)) (withTopRealPart (constraints i))

namespace GeneralConvexMinimizationProblem

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] {m : ℕ}

/-- A general convex minimization problem can be used as its ambient objective function. -/
instance : CoeFun (GeneralConvexMinimizationProblem X m) (fun _ ↦ X → WithTop ℝ) where
  coe := objective

/-- A real-valued constrained convex minimization problem with whole-space convex objective and
constraint functions canonically yields the Chapter 3 extended-valued owner by reusing the
Chapter 1 owner for the feasible-set / objective layer and coercing the functions to `WithTop ℝ`.
-/
def ofReal
    (problem : SetConstrainedMinimizationProblem X) (constraints : Fin m → X → ℝ)
    (feasibleSet_closed : IsClosed problem.feasibleSet)
    (feasibleSet_convex : Convex ℝ problem.feasibleSet)
    (objective_convex : ConvexOn ℝ Set.univ problem.objective)
    (constraints_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (constraints i)) :
    GeneralConvexMinimizationProblem X m where
  feasibleSet := problem.feasibleSet
  objective := fun x ↦ (problem x : WithTop ℝ)
  constraints := fun i x ↦ (constraints i x : WithTop ℝ)
  feasibleSet_closed := feasibleSet_closed
  feasibleSet_convex := feasibleSet_convex
  objective_convex := by
    simpa [withTopEffectiveDomain, withTopRealPart] using
      objective_convex
  constraints_convex i := by
    simpa [withTopEffectiveDomain, withTopRealPart] using
      constraints_convex i

/-- Evaluating a convex minimization problem as a function means evaluating its objective. -/
@[simp] theorem coe_apply (problem : GeneralConvexMinimizationProblem X m) (x : X) :
    problem x = problem.objective x :=
  rfl

/-- A point is feasible for a general convex minimization problem when it belongs to `Q` and
satisfies every inequality constraint `fᵢ(x) ≤ 0`. -/
def IsFeasible (problem : GeneralConvexMinimizationProblem X m) (x : X) : Prop :=
  x ∈ problem.feasibleSet ∧ ∀ i : Fin m, problem.constraints i x ≤ 0

/-- A point is feasible exactly when it lies in `Q` and satisfies every inequality constraint. -/
@[simp] theorem isFeasible_iff {problem : GeneralConvexMinimizationProblem X m} {x : X} :
    problem.IsFeasible x ↔ x ∈ problem.feasibleSet ∧ ∀ i : Fin m, problem.constraints i x ≤ 0 :=
  Iff.rfl

/-- A feasible point lies in the ambient feasible set `Q`. -/
theorem IsFeasible.mem_feasibleSet {problem : GeneralConvexMinimizationProblem X m} {x : X}
    (hx : problem.IsFeasible x) :
    x ∈ problem.feasibleSet :=
  hx.1

/-- A feasible point satisfies each inequality constraint `fᵢ(x) ≤ 0`. -/
theorem IsFeasible.constraint_nonpos {problem : GeneralConvexMinimizationProblem X m} {x : X}
    (hx : problem.IsFeasible x) (i : Fin m) :
    problem.constraints i x ≤ 0 :=
  hx.2 i

end GeneralConvexMinimizationProblem
