/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 6.9 lies in the constrained smoothing / set-constrained minimization domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical
  owner of feasible minimizers on a set;
- the derivative/Lipschitz theorem in `Chap06/Proposition_6_10`, which should talk directly about
  the present owner instead of introducing a second pointwise-sum wrapper.

Best owner abstraction:
- source-facing: the explicit-model smoothed optimization problem over `Q₁`;
- core/canonical: `SetConstrainedMinimizationProblem X`, with `argmin[Q₁] f` as derived API;
- bridge/view: the pointwise evaluation formula for the inherited objective.

Primitive data:
- a feasible set `Q₁ : Set X`;
- a model objective `hatf : X → ℝ`;
- a smoothing term `fμ : X → ℝ`.

Derived API:
- the objective coercion of `explicitModelSmoothedProblem Q₁ hatf fμ`;
- the canonical optimal set
  `argmin[(explicitModelSmoothedProblem Q₁ hatf fμ).feasibleSet]
    (explicitModelSmoothedProblem Q₁ hatf fμ)`;
- the standard membership bridge `mem_constrainedArgmin_iff`.

Source/core/bridge triage:
- source-facing: `explicitModelSmoothedProblem`;
- core/canonical: `SetConstrainedMinimizationProblem`;
- bridge/view: the evaluation lemma below.

The previous file stored the argmin set as a second public definition, but that data is already
owned upstream by `constrainedArgmin`. This refinement keeps only the source-facing problem owner
and lets minimizer sets be derived canonically.
-/

variable {X : Type u}

/-- Definition 6.9: for a model objective `\hat f` and smoothing term `f_μ`, the explicit-model
smoothed optimization problem on `Q₁` minimizes the sum `x ↦ \hat f(x) + f_μ(x)` over `Q₁`. -/
def explicitModelSmoothedProblem (Q₁ : Set X) (hatf fμ : X → ℝ) :
    SetConstrainedMinimizationProblem X where
  feasibleSet := Q₁
  objective := fun x ↦ hatf x + fμ x

/-- Unfolding `explicitModelSmoothedProblem Q₁ hatf fμ` recovers the feasible set `Q₁` together
with the summed objective `x ↦ \hat f(x) + f_μ(x)`. -/
-- Proof sketch: unfold `explicitModelSmoothedProblem`.
@[simp] theorem explicitModelSmoothedProblem_def
    (Q₁ : Set X) (hatf fμ : X → ℝ) :
    explicitModelSmoothedProblem Q₁ hatf fμ =
      { feasibleSet := Q₁, objective := fun x ↦ hatf x + fμ x } := by
  -- Unfold the source-facing owner to recover its canonical feasible set and objective fields.
  rfl

/-- The feasible set of the explicit-model smoothed problem is exactly `Q₁`. -/
@[simp] theorem explicitModelSmoothedProblem_feasibleSet
    (Q₁ : Set X) (hatf fμ : X → ℝ) :
    (explicitModelSmoothedProblem Q₁ hatf fμ).feasibleSet = Q₁ :=
  rfl

/-- The objective field of the explicit-model smoothed problem is the sum
`x ↦ \hat f(x) + f_μ(x)`. -/
@[simp] theorem explicitModelSmoothedProblem_objective
    (Q₁ : Set X) (hatf fμ : X → ℝ) :
    (explicitModelSmoothedProblem Q₁ hatf fμ).objective = fun x ↦ hatf x + fμ x :=
  rfl

/-- The explicit-model smoothed problem evaluates to the summed objective
`\hat f(x) + f_μ(x)` at each point `x`. -/
theorem explicitModelSmoothedProblem_spec
    (Q₁ : Set X) (hatf fμ : X → ℝ) (x : X) :
    explicitModelSmoothedProblem Q₁ hatf fμ x = hatf x + fμ x :=
  rfl

/-- Evaluating the explicit-model smoothed problem gives the defining sum
`\hat f(x) + f_μ(x)`. -/
@[simp] theorem explicitModelSmoothedProblem_apply
    (Q₁ : Set X) (hatf fμ : X → ℝ) (x : X) :
    explicitModelSmoothedProblem Q₁ hatf fμ x = hatf x + fμ x :=
  explicitModelSmoothedProblem_spec Q₁ hatf fμ x

/-- The canonical argmin set of the explicit-model smoothed problem is exactly the argmin set of
the summed objective `x ↦ \hat f(x) + f_μ(x)` on `Q₁`. -/
-- Proof sketch: extensionality on points, then rewrite membership with
-- `mem_constrainedArgmin_iff`, `explicitModelSmoothedProblem_feasibleSet`, and
-- `explicitModelSmoothedProblem_isMinOn_iff`.
@[simp] theorem explicitModelSmoothedProblem_argmin
    (Q₁ : Set X) (hatf fμ : X → ℝ) :
    constrainedArgmin
        (explicitModelSmoothedProblem Q₁ hatf fμ).feasibleSet
        (explicitModelSmoothedProblem Q₁ hatf fμ) =
      constrainedArgmin Q₁ (fun y ↦ hatf y + fμ y) := by
  -- Compare the two argmin sets pointwise and simplify both memberships definitionally.
  ext x
  simp

/-- Minimizing the explicit-model smoothed problem on its feasible set is exactly minimizing the
summed objective `x ↦ \hat f(x) + f_μ(x)` on `Q₁`. -/
-- Proof sketch: unfold the feasible set and objective of `explicitModelSmoothedProblem`.
@[simp] theorem explicitModelSmoothedProblem_isMinOn_iff
    (Q₁ : Set X) (hatf fμ : X → ℝ) {x : X} :
    IsMinOn (explicitModelSmoothedProblem Q₁ hatf fμ)
        (explicitModelSmoothedProblem Q₁ hatf fμ).feasibleSet x ↔
      IsMinOn (fun y ↦ hatf y + fμ y) Q₁ x := by
  -- Unfold the source-facing problem: both the feasible set and the objective are definitionally
  -- the canonical constrained minimization data.
  rfl

/-- Membership in the canonical argmin set of the explicit-model smoothed problem means belonging
to `Q₁` and minimizing `x ↦ \hat f(x) + f_μ(x)` there. -/
-- Proof sketch: rewrite membership with `mem_constrainedArgmin_iff`, then use
-- `explicitModelSmoothedProblem_feasibleSet` and
-- `explicitModelSmoothedProblem_isMinOn_iff`.
@[simp] theorem mem_explicitModelSmoothedProblem_argmin_iff
    (Q₁ : Set X) (hatf fμ : X → ℝ) {x : X} :
    x ∈ constrainedArgmin
        (explicitModelSmoothedProblem Q₁ hatf fμ).feasibleSet
        (explicitModelSmoothedProblem Q₁ hatf fμ) ↔
      x ∈ Q₁ ∧ IsMinOn (fun y ↦ hatf y + fμ y) Q₁ x := by
  -- Unfold argmin membership and identify the feasible set and objective definitionally.
  simp
