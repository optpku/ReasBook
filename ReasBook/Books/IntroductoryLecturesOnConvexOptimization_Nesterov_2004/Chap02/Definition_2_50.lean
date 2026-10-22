/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_35_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_44

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

namespace SmoothFunctionalConstraintsMinimizationProblem

section

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
variable (xBar : E) (γ : ℝ)

/-
Definition 2.50 lies in the local-model domain for smooth inequality-constrained minimization on
a real Hilbert space.

Sampled owner declarations:
* `FunctionalConstraintsMinimizationProblem` in `Chap01/Definition_1_1_1`, the project owner for
  an ambient feasible set together with a finite family of scalar constraints;
* `SmoothFunctionalConstraintsMinimizationProblem` in `Definition_2_44.lean`, the chapter owner
  carrying the ambient set `Q`, the objective `f₀`, and the finite constraint family `fᵢ`;
* `firstOrderTaylorModelAt` and `quadraticallyRegularizedObjective` in
  `Chap01/Definition_1_4_17.lean`, the canonical owners of the affine local model and its
  quadratic regularization;
* `problem.regularizedModelValue` in `Definition_2_47.lean`, the later owner value API attached
  to the same chapter-level constrained problem family.

Best owner abstraction:
* source-facing: the inequality-constrained local subproblem itself;
* core/canonical: `FunctionalConstraintsMinimizationProblem E m`;
* bridge/view: the feasible-set characterization obtained by unfolding the regularized affine
  constraints.

Primitive data:
* the ambient constrained problem `problem`;
* the base point `xBar`;
* the regularization parameter `γ`.

Derived API:
* the regularized first-order objective model;
* the regularized first-order constraint family;
* the inherited inequality-only feasible-set predicate.

The public owner for this numbered item is therefore the constrained local subproblem, not a raw
set-comprehension encoding of its feasible set and not its optimal value viewed as an `EReal`.
The finite constraint structure stays explicit through `m`, and the later value-level APIs are
derived from this owner layer rather than replacing it.
-/

local notation "regularizedAt" =>
  fun f : E → ℝ ↦
    quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) γ xBar

/-- Definition 2.50: the quadratically regularized first-order local subproblem at `xBar`
minimizes the regularized affine model of the objective over `Q`, subject to the regularized
affine inequality constraints. -/
def regularizedLocalSubproblem : FunctionalConstraintsMinimizationProblem E m where
  basicFeasibleSet := problem.ambientSet
  objective := fun x ↦ regularizedAt problem.objective x
  constraints := fun i x ↦ regularizedAt (problem.constraints i) x
  senses := fun _ ↦ .le

@[simp] theorem regularizedLocalSubproblem_basicFeasibleSet :
    (problem.regularizedLocalSubproblem xBar γ).basicFeasibleSet = problem.ambientSet :=
  rfl

@[simp] theorem regularizedLocalSubproblem_objective
    (x : (problem.regularizedLocalSubproblem xBar γ).basicFeasibleSet) :
    (problem.regularizedLocalSubproblem xBar γ).objective x =
      quadraticallyRegularizedObjective
        (firstOrderTaylorModelAt problem.objective xBar)
        γ
        xBar
        x :=
  rfl

@[simp] theorem regularizedLocalSubproblem_constraints
    (i : Fin m) (x : (problem.regularizedLocalSubproblem xBar γ).basicFeasibleSet) :
    (problem.regularizedLocalSubproblem xBar γ).constraints i x =
      quadraticallyRegularizedObjective
        (firstOrderTaylorModelAt (problem.constraints i) xBar)
        γ
        xBar
        x :=
  rfl

@[simp] theorem regularizedLocalSubproblem_hasLeConstraints :
    (problem.regularizedLocalSubproblem xBar γ).HasLeConstraints :=
  fun _ ↦ rfl

/-- Feasibility in the local subproblem means belonging to the ambient set `Q` and satisfying all
regularized affine inequality constraints. -/
theorem mem_regularizedLocalSubproblem_feasibleSet_iff
    {x : (problem.regularizedLocalSubproblem xBar γ).basicFeasibleSet} :
    x ∈ (problem.regularizedLocalSubproblem xBar γ).feasibleSet ↔
      ∀ i : Fin m,
        quadraticallyRegularizedObjective
          (firstOrderTaylorModelAt (problem.constraints i) xBar)
          γ
          xBar
          x ≤ 0 := by
  simpa using
    (problem.regularizedLocalSubproblem xBar γ).mem_feasibleSet_iff
      (problem.regularizedLocalSubproblem_hasLeConstraints xBar γ)

end

end SmoothFunctionalConstraintsMinimizationProblem
