/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Definition 5.0.23 lies in the chapter's self-concordant minimization domain.

Sampled owner declarations:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued objective;
* `IsSelfConcordantOnWith` and `IsSelfConcordantOn` in `Chap05/Definition_5_1_1`, the chapter
  owners for quantitative and existential self-concordance on a domain;
* `ContinuousLinearMap.IsPositive` in mathlib, the canonical pointwise positivity owner for
  symmetric continuous linear operators on real inner-product spaces;
* `hessian` in `Chap01/Definition_1_4_16`, reused upstream by the self-concordance owner as the
  canonical Hessian operator.

Best owner abstraction:
* source-facing: `UnconstrainedSelfConcordantMinimizationProblem E`;
* core/canonical ambient owner: `SetConstrainedMinimizationProblem E`;
* core/canonical regularity owner:
  `IsSelfConcordantOnWith feasibleSet selfConcordanceConstant objective`;
* auxiliary reusable property: `HasPositiveDefiniteHessianOn feasibleSet objective`.

Primitive data:
* the feasible set and objective, owned by `SetConstrainedMinimizationProblem E`;
* a self-concordance constant for the objective on the feasible set;
* quantitative self-concordance of the objective on the feasible set;
* pointwise positivity and strict positive definiteness of the Hessian on the feasible set.

Derived API:
* openness and convexity of the feasible set, recovered from self-concordance;
* the qualitative self-concordance view `IsSelfConcordantOn feasibleSet objective`;
* the coercion to the ambient objective function;
* the inherited ambient owner projection `toSetConstrainedMinimizationProblem`.

Source/core/bridge triage:
* source-facing: `UnconstrainedSelfConcordantMinimizationProblem E`;
* core/canonical:
  `SetConstrainedMinimizationProblem E`,
  `IsSelfConcordantOnWith feasibleSet selfConcordanceConstant objective`;
* bridge/view: the inherited parent projection when only the ambient minimization owner is
  needed. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Hessian of `f` is positive definite on `dom` when, at each point of the domain, the
Hessian operator is positive in the canonical mathlib sense and every nonzero direction has
strictly positive Hessian quadratic form. -/
class HasPositiveDefiniteHessianOn (dom : Set E) (f : E → ℝ) : Prop where
  /-- At each point of the domain, the Hessian operator is positive. -/
  isPositive {x : E} (hx : x ∈ dom) :
    (hessian f x).IsPositive
  /-- Every nonzero direction has strictly positive Hessian quadratic form on the domain. -/
  posdef {x : E} (hx : x ∈ dom) {u : E} (hu : u ≠ 0) :
    0 < inner ℝ u (hessian f x u)

namespace HasPositiveDefiniteHessianOn

/-- Positive definiteness of the Hessian on `dom` canonically supplies Hessian positivity at each
point of the domain. -/
theorem hessian_isPositive_of_mem {dom : Set E} {f : E → ℝ}
    [h : HasPositiveDefiniteHessianOn dom f] {x : E} (hx : x ∈ dom) :
    (hessian f x).IsPositive :=
  h.isPositive hx

/-- Positive definiteness of the Hessian on `dom` forces Hessian nondegeneracy at every point of
the domain. -/
theorem hessian_det_ne_zero_of_mem {dom : Set E} {f : E → ℝ}
    [FiniteDimensional ℝ E] [h : HasPositiveDefiniteHessianOn dom f] {x : E} (hx : x ∈ dom) :
    (hessian f x).det ≠ 0 := by
  rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot]
  intro hker
  obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hu_zero : hessian f x u = 0 := hu_mem
  have : ¬ 0 < (0 : ℝ) := not_lt_of_ge le_rfl
  exact this <| by
    simpa [hu_zero] using h.posdef hx hu_ne

end HasPositiveDefiniteHessianOn

/-- Definition 5.0.23, generalized from the textbook Euclidean setting: an unconstrained
self-concordant minimization problem consists of a domain and an objective to be minimized over
that domain, where the objective is self-concordant on the domain and has positive definite
Hessian there. The ambient problem data are owned canonically by
`SetConstrainedMinimizationProblem`, while self-concordance is expressed through the chapter owner
`IsSelfConcordantOnWith`. -/
structure UnconstrainedSelfConcordantMinimizationProblem (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    extends SetConstrainedMinimizationProblem E where
  /-- The self-concordance constant of the objective on the feasible set. -/
  selfConcordanceConstant : NNReal
  /-- The problem canonically supplies the quantitative self-concordance owner for its objective
  on its feasible set. -/
  toIsSelfConcordantOnWith :
    IsSelfConcordantOnWith feasibleSet selfConcordanceConstant objective
  /-- The problem canonically supplies positive-definite Hessian data for its objective on its
  feasible set. -/
  toHasPositiveDefiniteHessianOn : HasPositiveDefiniteHessianOn feasibleSet objective

attribute [instance] UnconstrainedSelfConcordantMinimizationProblem.toIsSelfConcordantOnWith
attribute [instance] UnconstrainedSelfConcordantMinimizationProblem.toHasPositiveDefiniteHessianOn

namespace UnconstrainedSelfConcordantMinimizationProblem

/-- The objective of an unconstrained self-concordant minimization problem is self-concordant on
its feasible set. -/
theorem isSelfConcordantOn
    (problem : UnconstrainedSelfConcordantMinimizationProblem E) :
    IsSelfConcordantOn problem.feasibleSet problem.objective :=
  ⟨problem.selfConcordanceConstant, problem.toIsSelfConcordantOnWith⟩

/-- The feasible set of an unconstrained self-concordant minimization problem is open. -/
theorem feasibleSet_open (problem : UnconstrainedSelfConcordantMinimizationProblem E) :
    IsOpen problem.feasibleSet :=
  problem.toIsSelfConcordantOnWith.isOpen_domain

/-- The feasible set of an unconstrained self-concordant minimization problem is convex. -/
theorem feasibleSet_convex (problem : UnconstrainedSelfConcordantMinimizationProblem E) :
    Convex ℝ problem.feasibleSet :=
  problem.toIsSelfConcordantOnWith.convex_domain

/-- An unconstrained self-concordant minimization problem can be used as its objective function.
-/
instance : CoeFun (UnconstrainedSelfConcordantMinimizationProblem E) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating an unconstrained self-concordant minimization problem returns its objective value.
-/
@[simp] theorem coe_apply
    (problem : UnconstrainedSelfConcordantMinimizationProblem E) (x : E) :
    problem x = problem.objective x :=
  rfl

end UnconstrainedSelfConcordantMinimizationProblem

end
