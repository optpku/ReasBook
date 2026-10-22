/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_42

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MaxTypeStep

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι] {μ L : ℝ}

namespace SmoothMinimaxProblem

/- Definition 2.42 is source-facing in the smooth minimax estimating-sequence domain.

Mandatory domain-style sampling for this refinement:
* `quadraticallyRegularizedObjective` and `quadraticallyRegularizedObjective_apply`, the owner
  centered quadratic regularization of a real-valued model;
* `maxTypeGradientMapping` and `maxTypeReducedGradient` in `Remark_2_41_1`, the chapter owner
  exact step and reduced gradient for the regularized affine max-type model;
* `SmoothMinimaxProblem.objective_lower_bound_of_isMinOn_regularizedAffineApproximation` in
  `Theorem_2_42`, the canonical lower-bound theorem for an arbitrary exact minimizer of that
  owner regularized affine model.

Best owner abstraction:
* source-facing: the initial quadratic model and the lower model built from the exact step
  `x_f(problem.components; γ)` and reduced gradient `g_f(problem.components; γ)`;
* core/canonical: `quadraticallyRegularizedObjective` together with the exact-step owners from
  `Remark_2_41_1`;
* bridge/view: the pointwise expansion lemmas below and the specialization of
  `objective_lower_bound_of_isMinOn_regularizedAffineApproximation` to the chosen exact step.

Primitive data:
* the initial objective value `f0`, the initial point `x0`, and the initial curvature `gamma0`;
* the base point `xBar` and exact-step curvature `γ`.

Derived API:
* `initialQuadraticModel f0 gamma0 x0`, specialized in the minimax setting at `f0 = problem x0`;
* `problem.lowerModel xBar γ`;
* the pointwise formulas for those two source-facing models;
* the textbook lower-bound theorem written directly with `x_f` and `g_f`.

This file therefore does not stay recall-only. It reuses the canonical owner declarations above,
but keeps Definition 2.42 itself as public source-facing model data rather than leaving those
objects only as local notation plus `#check` examples.
-/

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Definition 2.42: the initial model is the quadratic regularization of the constant objective
with value `f0`, centered at `x0` with curvature `gamma0`. In the smooth minimax setting one
specializes to `f0 = problem x0`. -/
def initialQuadraticModel
    (f0 : ℝ) (gamma0 : ℝ) (x0 : E) :
    E → ℝ :=
  quadraticallyRegularizedObjective (fun _ : E ↦ f0) gamma0 x0

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The initial model expands to the textbook centered quadratic formula. -/
theorem initialQuadraticModel_apply
    (f0 : ℝ) (gamma0 : ℝ) (x0 x : E) :
    initialQuadraticModel f0 gamma0 x0 x =
      f0 + (gamma0 / 2) * ‖x - x0‖ ^ (2 : ℕ) :=
  quadraticallyRegularizedObjective_apply (fun _ : E ↦ f0) gamma0 x0 x

section ExactStep

variable [ProperSpace E]

variable (problem : SmoothMinimaxProblem E ι μ L) (xBar : E) (γ : NNRealˣ)

local notation "Q" => problem.feasibleSet
local instance instLocalChap02_Definition_2_421 : Fact (Set.Nonempty Q) := ⟨problem.feasible_nonempty⟩
local instance instLocalChap02_Definition_2_422 : Fact (IsClosed Q) := ⟨problem.feasible_closed⟩
local instance instLocalChap02_Definition_2_423 : Fact (Convex ℝ Q) := ⟨problem.feasible_convex⟩

/-- Definition 2.42: the lower model is the `μ`-regularized affine function built from the exact
step `x_f(problem.components; γ)` and reduced gradient `g_f(problem.components; γ)` at `xBar`. -/
def lowerModel : E → ℝ :=
  quadraticallyRegularizedObjective
    (fun y : E ↦
      problem (x_f[Q | problem.components; γ](xBar)) +
        inner ℝ (g_f[Q | problem.components; γ](xBar)) (y - xBar) +
        (1 / (2 * (γ : ℝ))) * ‖g_f[Q | problem.components; γ](xBar)‖ ^ (2 : ℕ))
    μ
    xBar

/-- The lower model expands to the textbook exact-step lower quadratic formula. -/
theorem lowerModel_apply
    (x : E) :
    problem.lowerModel xBar γ x =
      problem (x_f[Q | problem.components; γ](xBar)) +
        inner ℝ (g_f[Q | problem.components; γ](xBar)) (x - xBar) +
        (1 / (2 * (γ : ℝ))) * ‖g_f[Q | problem.components; γ](xBar)‖ ^ (2 : ℕ) +
        (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) :=
  quadraticallyRegularizedObjective_apply
    (fun y : E ↦
      problem (x_f[Q | problem.components; γ](xBar)) +
        inner ℝ (g_f[Q | problem.components; γ](xBar)) (y - xBar) +
        (1 / (2 * (γ : ℝ))) * ‖g_f[Q | problem.components; γ](xBar)‖ ^ (2 : ℕ))
    μ
    xBar
    x

/-- Definition 2.42 on the chapter's exact-step surface: if `L ≤ γ` and `x ∈ Q`, then the
objective dominates the lower model built from `x_f(problem.components; γ)` and
`g_f(problem.components; γ)` at `xBar`. -/
theorem objective_lower_bound
    (hLγ : L ≤ (γ : ℝ)) {x : E} (hx : x ∈ Q) :
    problem x ≥
      problem (x_f[Q | problem.components; γ](xBar)) +
        inner ℝ (g_f[Q | problem.components; γ](xBar)) (x - xBar) +
        (1 / (2 * (γ : ℝ))) * ‖g_f[Q | problem.components; γ](xBar)‖ ^ (2 : ℕ) +
        (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
  have hxPlus :=
    maxTypeGradientMapping_mem_and_isMinOn_ofFact
      Q problem.components xBar γ
  simpa [problem.lowerModel_apply xBar γ x] using
    objective_lower_bound_of_isMinOn_regularizedAffineApproximation
      problem
      xBar
      hLγ
      hx
      hxPlus.1
      hxPlus.2

end ExactStep

end SmoothMinimaxProblem
