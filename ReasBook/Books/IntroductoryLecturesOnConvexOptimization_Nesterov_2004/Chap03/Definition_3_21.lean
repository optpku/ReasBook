/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

/- Definition 3.21 lies in the source-facing domain of composite convex minimization.

Primary domain:
- composite convex minimization with a smooth real-valued term and an extended-valued closed
  convex regularizer on a common feasible set, generalized from the textbook `ℝⁿ` model to the
  intrinsic ambient-space owner level.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` from `Chap01/Definition_1_3_3`, the Chapter 1 owner of a
  feasible set together with one real-valued objective;
- `ConvexC1On` from `Chap02/Definition_2_4`, the chapter owner for a real-valued smooth convex
  term on a feasible set;
- `ClosedConvexOn` from `Definition_3_1_1_5`, the chapter owner predicate for an
  `ℝ ∪ {+∞}`-valued term on a feasible set;
- `CompositeLipschitzGradientModel` from `Chap06/Definition_6_8`, which reuses the same helper
  `compositeObjective` for the full composite objective once the smooth term and regularizer are
  fixed.

Best owner abstraction:
- source-facing owner: `CompositeConvexMinimizationProblem`;
- core/canonical ambient owner: `SetConstrainedMinimizationProblem`;
- canonical chapter owner for the smooth term: `ConvexC1On`;
- canonical chapter predicate for the nonsmooth term: `ClosedConvexOn`;
- derived source-facing objective: the full extended-valued composite objective `x ↦ f x + Ψ x`.

Primitive data:
- the ambient feasible set `Q` and smooth term `f : E → ℝ`, owned canonically by
  `SetConstrainedMinimizationProblem`;
- the closedness of `Q`;
- the canonical smooth-owner witness `ConvexC1On Q f`;
- the nonsmooth term `Ψ` together with its `ClosedConvexOn Q Ψ` witness.

Derived API:
- the source-facing view `smoothPart`, recovered from the inherited owner objective;
- the smooth convexity and `C¹` regularity projections recovered from `ConvexC1On`;
- the convexity of `Q`, derived from `ClosedConvexOn.convex`;
- the coercion to the full composite objective `x ↦ f x + Ψ x`;
- the coercion from a problem to that composite objective.

Source/core/bridge triage:
- source-facing: `CompositeConvexMinimizationProblem`
- core/canonical: `SetConstrainedMinimizationProblem`, `ClosedConvexOn`
- bridge/view: the inherited ambient owner projection is available when only the smooth subproblem
  is needed, but it is not the public mathematical content of Definition 3.21. -/

variable {X : Type u}

/-- The extended composite objective `x ↦ f x + Ψ x` built from a real-valued smooth term and an
extended-valued regularizer on the same ambient space. -/
def compositeObjective (f : X → ℝ) (Ψ : X → WithTop ℝ) : X → WithTop ℝ :=
  fun x ↦ (f x : WithTop ℝ) + Ψ x

/-- Evaluating the extended composite objective recovers the defining sum `f x + Ψ x`. -/
@[simp] theorem compositeObjective_apply (f : X → ℝ) (Ψ : X → WithTop ℝ) (x : X) :
    compositeObjective f Ψ x = (f x : WithTop ℝ) + Ψ x :=
  rfl

/-- Definition 3.21, generalized from the textbook `ℝⁿ` setting: a composite convex
minimization problem consists of a closed feasible set `Q`, a smooth convex part `f` that
belongs to `ConvexC1On Q`, and a closed convex term `Ψ` on `Q`, representing the objective
`x ↦ f x + Ψ x` minimized over `Q`. The ambient smooth pair `(Q, f)` is owned canonically by
`SetConstrainedMinimizationProblem`, the smooth regularity/convexity package by `ConvexC1On`,
and the nonsmooth term by `ClosedConvexOn`. The textbook `ℝⁿ` case is the specialization
`CompositeConvexMinimizationProblem (EuclideanSpace ℝ (Fin n))`. -/
structure CompositeConvexMinimizationProblem (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    extends SetConstrainedMinimizationProblem E where
  /-- The feasible set `Q` is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The smooth term belongs to the canonical Chapter 2 owner `ConvexC1On Q`. -/
  smoothPart_convexC1 : ConvexC1On feasibleSet objective
  /-- The closed convex term `Ψ : ℝⁿ → ℝ ∪ {+∞}`. -/
  nonsmoothPart : E → WithTop ℝ
  /-- The nonsmooth term is closed and convex on `Q`. -/
  nonsmoothPart_closedConvex : ClosedConvexOn feasibleSet nonsmoothPart

namespace CompositeConvexMinimizationProblem

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The source-facing smooth term `f` is the inherited Chapter 1 objective. -/
abbrev smoothPart (problem : CompositeConvexMinimizationProblem E) : E → ℝ :=
  problem.objective

/-- The smooth term is convex on the feasible set `Q`. -/
theorem smoothPart_convex (problem : CompositeConvexMinimizationProblem E) :
    ConvexOn ℝ problem.feasibleSet problem.smoothPart :=
  convexC1On_convexOn problem.smoothPart_convexC1

/-- The smooth term is `C¹` on the feasible set `Q`. -/
theorem smoothPart_contDiff (problem : CompositeConvexMinimizationProblem E) :
    ContDiffOn ℝ 1 problem.smoothPart problem.feasibleSet :=
  convexC1On_contDiffOn problem.smoothPart_convexC1

/-- The feasible set of a composite convex minimization problem is convex. -/
theorem feasibleSet_convex (problem : CompositeConvexMinimizationProblem E) :
    Convex ℝ problem.feasibleSet :=
  problem.nonsmoothPart_closedConvex.convex

/-- A composite convex minimization problem can be used as its extended-valued objective
`x ↦ f(x) + Ψ(x)`. -/
instance : CoeFun (CompositeConvexMinimizationProblem E)
    (fun _ ↦ E → WithTop ℝ) where
  coe problem := _root_.compositeObjective problem.smoothPart problem.nonsmoothPart

/-- Evaluating a composite convex minimization problem gives its composite objective value. -/
@[simp] theorem coe_apply
    (problem : CompositeConvexMinimizationProblem E) (x : E) :
    problem x = (problem.smoothPart x : WithTop ℝ) + problem.nonsmoothPart x :=
  rfl

end CompositeConvexMinimizationProblem

end
