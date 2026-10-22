/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped WithTopConvexAnalysis

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 6.50 lies in the chapter's composite convex minimization / closed extended-valued
regularizer domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the base owner for a feasible
  set together with a real-valued objective;
- `PrimalConvexMinimizationProblem` in `Chap06/Definition_6_4`, the Chapter 6 owner obtained once
  nonemptiness, boundedness, closedness, continuity, and convexity are available for the smooth
  feasible-set problem;
- `withTopEffectiveDomain` / `dom` and `constrainedEpigraph` in `Chap03/Definition_3_3`, the
  Chapter 3 owners for effective domains and epigraphs of `WithTop ℝ`-valued functions;
- `ClosedConvexFunction` in `Chap03/Definition_3_1_1_5`, the chapter owner for a proper closed
  convex extended-valued term on its own effective domain;
- `_root_.compositeObjective` in `Chap03/Definition_3_21`, the canonical composite objective
  `x ↦ f x + Ψ x`.

Best owner abstraction:
- source-facing: `CompositeBoundedConvexMinimizationProblem`;
- core/canonical: `SetConstrainedMinimizationProblem`, `PrimalConvexMinimizationProblem`,
  `ClosedConvexFunction`, and `_root_.compositeObjective`;
- bridge/view: the domain inclusion `dom Ψ ⊆ Q`, which forces the composite objective to take the
  value `⊤` outside `Q`, together with the derived bridge to
  `PrimalConvexMinimizationProblem`.

Primitive data:
- the ambient feasible set and smooth term, owned canonically by
  `SetConstrainedMinimizationProblem`;
- boundedness and closedness of `Q`;
- convexity of the smooth term on `Q`;
- differentiability of the inherited smooth part on `Q`;
- the extended-valued regularizer `Ψ`;
- properness of `Ψ`;
- the canonical closed-convex-function owner for `Ψ`;
- the source-facing inclusion `dom Ψ ⊆ Q`.

Derived API:
- the source-facing name `smoothPart` for the inherited real objective;
- nonemptiness of `Q`, obtained from `nonsmoothPart_proper` and `dom Ψ ⊆ Q`;
- continuity of `f` on `Q`, obtained from differentiability;
- the canonical Chapter 6 bridge `toPrimalConvexMinimizationProblem`;
- convexity and differentiability of `smoothPart` on `Q`;
- the extended composite objective `x ↦ f x + Ψ x`;
- the fact that `Ψ x = ⊤` and hence the composite objective is `⊤` outside `Q`.

Source/core/bridge triage:
- source-facing: `CompositeBoundedConvexMinimizationProblem`;
- core/canonical: `SetConstrainedMinimizationProblem`, `PrimalConvexMinimizationProblem`,
  `ClosedConvexFunction`, `_root_.compositeObjective`;
- bridge/view: `nonsmoothPart_domain_subset_feasibleSet`.

The previous version duplicated the Chapter 3 effective-domain, epigraph, and composite-objective
owners locally. This refinement keeps Definition 6.50 as its own source-facing owner, but moves
its primitive data onto the existing project owners, derives the ambient Chapter 6 feasible-set
owner instead of storing its redundant fields primitively, and deletes exact-interface aliases for
canonical notions. -/

/-- Definition 6.50: a composite bounded convex minimization problem consists of a nonempty
bounded closed convex feasible set `Q`, a convex differentiable smooth term `f` on `Q`, and a
proper closed convex extended-valued term `Ψ` whose effective domain is contained in `Q`. The
ambient smooth pair `(Q, f)` is owned canonically by `SetConstrainedMinimizationProblem`; the
nonemptiness of `Q` is derived from properness of `Ψ` together with `dom Ψ ⊆ Q`, and the ambient
Chapter 6 feasible-set owner is recovered by the bridge
`toPrimalConvexMinimizationProblem`. The regularizer uses the Chapter 3 owner
`ClosedConvexFunction`. -/
structure CompositeBoundedConvexMinimizationProblem (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] extends SetConstrainedMinimizationProblem E where
  /-- The feasible set is bounded. -/
  feasibleSet_bounded : Bornology.IsBounded feasibleSet
  /-- The feasible set is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The inherited smooth term is convex on `Q`. -/
  objective_convex : ConvexOn ℝ feasibleSet objective
  /-- The inherited smooth term is differentiable on `Q`. -/
  objective_differentiable : DifferentiableOn ℝ objective feasibleSet
  /-- The extended-valued nonsmooth term `Ψ : E → ℝ ∪ {+∞}`. -/
  nonsmoothPart : E → WithTop ℝ
  /-- The effective domain of `Ψ` is nonempty. -/
  nonsmoothPart_proper : (dom nonsmoothPart).Nonempty
  /-- The nonsmooth term is a closed convex function in the Chapter 3 owner sense. -/
  nonsmoothPart_closedConvex : ClosedConvexFunction nonsmoothPart
  /-- The effective domain of `Ψ` is contained in the feasible set `Q`. -/
  nonsmoothPart_domain_subset_feasibleSet : dom nonsmoothPart ⊆ feasibleSet

namespace CompositeBoundedConvexMinimizationProblem

/-- The source-facing smooth term `f` is the inherited primal objective. -/
abbrev smoothPart (problem : CompositeBoundedConvexMinimizationProblem E) : E → ℝ :=
  problem.objective

/-- The feasible set `Q` is nonempty because any point of `dom Ψ` is feasible. -/
theorem feasibleSet_nonempty (problem : CompositeBoundedConvexMinimizationProblem E) :
    problem.feasibleSet.Nonempty := by
  rcases problem.nonsmoothPart_proper with ⟨x, hx⟩
  exact ⟨x, problem.nonsmoothPart_domain_subset_feasibleSet hx⟩

/-- Differentiability of the smooth term on `Q` implies continuity there. -/
theorem objective_continuous (problem : CompositeBoundedConvexMinimizationProblem E) :
    ContinuousOn problem.objective problem.feasibleSet :=
  problem.objective_differentiable.continuousOn

/-- Forgetting the nonsmooth term recovers the Chapter 6 primal convex minimization problem. -/
def toPrimalConvexMinimizationProblem
    (problem : CompositeBoundedConvexMinimizationProblem E) :
    PrimalConvexMinimizationProblem E where
  toSetConstrainedMinimizationProblem := problem.toSetConstrainedMinimizationProblem
  feasibleSet_nonempty := problem.feasibleSet_nonempty
  feasibleSet_bounded := problem.feasibleSet_bounded
  feasibleSet_closed := problem.feasibleSet_closed
  objective_continuous := problem.objective_continuous
  objective_convex := problem.objective_convex

/-- The smooth term is convex on the feasible set `Q`. -/
theorem smoothPart_convex (problem : CompositeBoundedConvexMinimizationProblem E) :
    ConvexOn ℝ problem.feasibleSet problem.smoothPart :=
  problem.objective_convex

/-- The smooth term is differentiable on the feasible set `Q`. -/
theorem smoothPart_differentiable (problem : CompositeBoundedConvexMinimizationProblem E) :
    DifferentiableOn ℝ problem.smoothPart problem.feasibleSet :=
  problem.objective_differentiable

/-- The extended-valued composite objective `\bar f = f + Ψ`. -/
abbrev compositeObjective (problem : CompositeBoundedConvexMinimizationProblem E) :
    E → WithTop ℝ :=
  _root_.compositeObjective problem.smoothPart problem.nonsmoothPart

/-- Evaluating the composite objective recovers the defining sum `f(x) + Ψ(x)`. -/
@[simp] theorem compositeObjective_apply
    (problem : CompositeBoundedConvexMinimizationProblem E) (x : E) :
    problem.compositeObjective x = (problem.smoothPart x : WithTop ℝ) + problem.nonsmoothPart x :=
  rfl

/-- A composite bounded convex minimization problem can be used as its extended-valued composite
objective `x ↦ f(x) + Ψ(x)`. -/
instance : CoeFun (CompositeBoundedConvexMinimizationProblem E) (fun _ ↦ E → WithTop ℝ) where
  coe problem := problem.compositeObjective

/-- Evaluating a composite bounded convex minimization problem returns its composite objective
value. -/
@[simp] theorem coe_apply
    (problem : CompositeBoundedConvexMinimizationProblem E) (x : E) :
    problem x = (problem.smoothPart x : WithTop ℝ) + problem.nonsmoothPart x :=
  rfl

/-- Outside the feasible set `Q`, the nonsmooth term must take the value `+∞`. -/
theorem nonsmoothPart_apply_of_not_mem
    (problem : CompositeBoundedConvexMinimizationProblem E) {x : E}
    (hx : x ∉ problem.feasibleSet) :
    problem.nonsmoothPart x = ⊤ := by
  by_contra hx_top
  have hx_dom : x ∈ dom problem.nonsmoothPart :=
    lt_top_iff_ne_top.mpr hx_top
  exact hx (problem.nonsmoothPart_domain_subset_feasibleSet hx_dom)

/-- Outside the feasible set, the composite objective takes the value `+∞`. -/
theorem compositeObjective_apply_of_not_mem
    (problem : CompositeBoundedConvexMinimizationProblem E) {x : E}
    (hx : x ∉ problem.feasibleSet) :
    problem.compositeObjective x = ⊤ := by
  rw [compositeObjective_apply, problem.nonsmoothPart_apply_of_not_mem hx]
  simp

end CompositeBoundedConvexMinimizationProblem

end
