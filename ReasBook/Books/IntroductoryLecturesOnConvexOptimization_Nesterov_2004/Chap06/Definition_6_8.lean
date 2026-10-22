/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_31

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 6.8 lies in the composite convex optimization / prox-subproblem domain.

Sampled owner-style declarations:
- `CompositeConvexMinimizationProblem` and `compositeObjective` in `Chap03/Definition_3_21`;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`;
- `ConvexC1On` in `Chap02/Definition_2_4`;
- `NesterovIsProxFunction` in `Chap06/Definition_6_31`.

Best owner abstraction:
- source-facing: `CompositeLipschitzGradientModel`;
- core/canonical: `CompositeConvexMinimizationProblem E`;
- bridge/view: the prox-subproblem objective `compositeAuxiliaryObjective`, together with the
  derived `NesterovIsProxFunction` witness for the prox term.

Primitive data:
- the ambient composite convex problem, owned by `CompositeConvexMinimizationProblem E`;
- a chosen dual-valued gradient field for the inherited smooth part, with its feasible-set
  derivative and Lipschitz data;
- a differentiable prox-function together with its canonical ambient-norm prox-function owner;
- attainment of the auxiliary prox subproblems.

Derived API:
- closedness/convexity of the feasible set and the closed-convex nonsmooth owner, inherited from
  `CompositeConvexMinimizationProblem`;
- the full extended-valued composite objective, reused directly from the inherited Chapter 3
  owner instead of a second local `objective` wrapper;
- the prox-function owner `NesterovIsProxFunction`, stored directly in its ambient-norm specialization
  instead of keeping a parallel raw `StrongConvexOn` field. -/

/-- The auxiliary objective of the prox subproblem on the feasible set `Q`, with linear term `s`,
prox weight `α`, and regularizer weight `β`. -/
def compositeAuxiliaryObjective
    (Q : Set E) (s : StrongDual ℝ E) (α β : NNReal) (d : E → ℝ) (Ψ : E → WithTop ℝ) :
    Q → WithTop ℝ :=
  _root_.compositeObjective
    (fun x : Q ↦ s x + (α : ℝ) * d x)
    (fun x : Q ↦ ((β : ℝ) : WithTop ℝ) * Ψ x)

/-- Evaluating the auxiliary objective gives the linear term plus prox penalty plus weighted
extended-valued regularizer. -/
-- Proof sketch: unfold `compositeAuxiliaryObjective`.
@[simp] theorem compositeAuxiliaryObjective_apply
    (Q : Set E) (s : StrongDual ℝ E) (α β : NNReal) (d : E → ℝ) (Ψ : E → WithTop ℝ)
    (x : Q) :
    compositeAuxiliaryObjective Q s α β d Ψ x =
      (((s x + (α : ℝ) * d x : ℝ) : WithTop ℝ) + ((β : ℝ) : WithTop ℝ) * Ψ x) :=
  rfl

/-- Definition 6 8: a composite convex optimization model with Lipschitz gradient consists of an
ambient composite convex problem from Definition 3.21, a chosen dual-valued gradient field for
its inherited smooth part with `L`-Lipschitz control on the feasible set, and a differentiable
`1`-strongly convex prox-function whose auxiliary subproblems admit minimizers. -/
structure CompositeLipschitzGradientModel (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    extends CompositeConvexMinimizationProblem E where
  /-- The chosen gradient map `∇f : E → E*`. -/
  smoothGradient : E → StrongDual ℝ E
  /-- The chosen gradient represents the derivative of the inherited smooth part at every
  feasible point. -/
  smoothPart_hasGradientWithinAt :
    ∀ ⦃x : E⦄, x ∈ feasibleSet →
      HasFDerivWithinAt objective (smoothGradient x) feasibleSet x
  /-- The Lipschitz constant for the gradient. -/
  L : NNReal
  /-- The gradient is `L`-Lipschitz on `Q` in the dual norm. -/
  smoothGradient_lipschitz :
    LipschitzOnWith L smoothGradient feasibleSet
  /-- The prox-function `d : E → ℝ`. -/
  proxFunction : E → ℝ
  /-- The prox-function is differentiable on `Q`. -/
  proxFunction_differentiable : DifferentiableOn ℝ proxFunction feasibleSet
  /-- The prox-function is a canonical ambient-norm prox-function on `Q`. -/
  proxFunction_isProxFunction : NesterovIsProxFunction (normSeminorm ℝ E) feasibleSet proxFunction
  /-- Every auxiliary prox subproblem with nonnegative weights admits a minimizer on `Q`. -/
  auxiliaryProblem_tractable :
    ∀ s : StrongDual ℝ E, ∀ α β : NNReal,
      ∃ x : feasibleSet, IsMinOn
        (compositeAuxiliaryObjective feasibleSet s α β proxFunction nonsmoothPart) Set.univ x

namespace CompositeLipschitzGradientModel

/-- A Definition 6.8 model can be evaluated as the inherited Chapter 3 composite objective. -/
instance : CoeFun (CompositeLipschitzGradientModel E) (fun _ ↦ E → WithTop ℝ) where
  coe model := model.toCompositeConvexMinimizationProblem

/-- Evaluating a Definition 6.8 model uses the inherited Chapter 3 composite objective. -/
@[simp] theorem coe_apply (model : CompositeLipschitzGradientModel E) (x : E) :
    model x = (model.objective x : WithTop ℝ) + model.nonsmoothPart x :=
  rfl

/-- The model's auxiliary prox subproblem objective on `Q` for parameters `s`, `α`, and `β`. -/
def auxiliaryObjective
    (model : CompositeLipschitzGradientModel E) (s : StrongDual ℝ E) (α β : NNReal) :
    model.feasibleSet → WithTop ℝ :=
  _root_.compositeAuxiliaryObjective
    model.feasibleSet s α β model.proxFunction model.nonsmoothPart

/-- Evaluating the model auxiliary objective gives the textbook affine-plus-prox-plus-regularizer
formula. -/
@[simp] theorem auxiliaryObjective_apply
    (model : CompositeLipschitzGradientModel E) (s : StrongDual ℝ E) (α β : NNReal)
    (x : model.feasibleSet) :
    model.auxiliaryObjective s α β x =
      (((s x + (α : ℝ) * model.proxFunction x : ℝ) : WithTop ℝ) +
        ((β : ℝ) : WithTop ℝ) * model.nonsmoothPart x) :=
  rfl

end CompositeLipschitzGradientModel

end
