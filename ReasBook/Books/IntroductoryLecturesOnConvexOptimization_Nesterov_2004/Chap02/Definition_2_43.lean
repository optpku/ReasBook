/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_40

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- Definition 2.43 is a recall-only item in the epigraph reformulation domain for constrained
quadratically regularized max-type affine minimization on a real Hilbert space.

Primary domain:
* the auxiliary-variable epigraph presentation of the Chapter 2 regularized minimax subproblem on
  `E × ℝ`

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued ambient objective;
* `SetConstrainedMinimizationProblem.coe_apply`, the canonical coercion view of that owner as its
  objective function;
* `maxTypeAffineApproximation` in `Definition_2_39`, the owner affine max-type model at `xBar`;
* `quadraticallyRegularizedObjective` in `Chap01/FirstOrderTaylorModel.lean`, the owner quadratic
  regularization of an objective on `E`.

Best owner abstraction:
* source-facing/core:
  `SetConstrainedMinimizationProblem (E × ℝ)`, built from the epigraph feasible set and its
  auxiliary-variable objective;
* bridge/view:
  the displayed feasible-set and objective expressions, together with the tight-slack
  specialization back to the Chapter 2 owner
  `quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar`.

Primitive data:
* a feasible set `Q : Set E`;
* a nonempty finite component family `fi : ι → E → ℝ`;
* a base point `xBar : E`;
* a regularization parameter `γ : ℝ`.

Derived API:
* the epigraph problem
  `SetConstrainedMinimizationProblem.mk
    {xt : E × ℝ | xt.1 ∈ Q ∧ maxTypeAffineApproximation fi xBar xt.1 ≤ xt.2}
    (fun xt ↦ xt.2 + (γ / 2) * ‖xt.1 - xBar‖ ^ (2 : ℕ))`;
* the coercion of that problem to its objective on `E × ℝ`;
* the constrained minimizer predicate `IsMinOn problem problem.feasibleSet xtStar`;
* the tight-slack specialization `xt.2 = maxTypeAffineApproximation fi xBar xt.1`.

Source/core/bridge triage:
* source-facing: the epigraph minimization problem on `E × ℝ`;
* core/canonical: `SetConstrainedMinimizationProblem (E × ℝ)`;
* bridge/view: the displayed feasible-set and objective formulas for that owner, and the
  projection back to the regularized max-type model on `E`.

This recall file therefore presents the epigraph reformulation through the Chapter 1 owner object,
not as a parallel collection of standalone feasible-set, objective, and minimizer displays.
Downstream Chapter 2 files should package the epigraph problem with
`SetConstrainedMinimizationProblem.mk ...` and use `problem.feasibleSet`, coercion to the
objective, and `IsMinOn problem problem.feasibleSet ...` as the derived API. The textbook states
the item on `ℝⁿ`, but the owner declarations sampled above already live on the canonical abstract
real-Hilbert-space / finite-index layer, so this recall file keeps that generality instead of
re-specializing it to `EuclideanSpace ℝ (Fin n)` and `Fin m`. -/

recall SetConstrainedMinimizationProblem
recall maxTypeAffineApproximation
recall quadraticallyRegularizedObjective
recall IsMinOn

private abbrev epigraphProblem
    (Q : Set E) (fi : ι → E → ℝ) (γ : ℝ) (xBar : E) :
    SetConstrainedMinimizationProblem (E × ℝ) :=
  .mk
    {xt : E × ℝ | xt.1 ∈ Q ∧ maxTypeAffineApproximation fi xBar xt.1 ≤ xt.2}
    (fun xt ↦ xt.2 + (γ / 2) * ‖xt.1 - xBar‖ ^ (2 : ℕ))

section

variable (Q : Set E) (fi : ι → E → ℝ) (γ : ℝ) (xBar : E) (xtStar : E × ℝ)

set_option linter.hashCommand false in
#check
  (show SetConstrainedMinimizationProblem (E × ℝ) from epigraphProblem Q fi γ xBar)

set_option linter.hashCommand false in
#check
  (show
    (epigraphProblem Q fi γ xBar).feasibleSet =
      {xt : E × ℝ | xt.1 ∈ Q ∧ maxTypeAffineApproximation fi xBar xt.1 ≤ xt.2} from
    rfl)

set_option linter.hashCommand false in
#check
  (show
    (epigraphProblem Q fi γ xBar : E × ℝ → ℝ) =
      (fun xt ↦ xt.2 + (γ / 2) * ‖xt.1 - xBar‖ ^ (2 : ℕ)) from
    rfl)

example (x : E) :
    epigraphProblem Q fi γ xBar (x, maxTypeAffineApproximation fi xBar x) =
      quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar x := by
  rfl

#check
  IsMinOn (epigraphProblem Q fi γ xBar) (epigraphProblem Q fi γ xBar).feasibleSet xtStar

end
