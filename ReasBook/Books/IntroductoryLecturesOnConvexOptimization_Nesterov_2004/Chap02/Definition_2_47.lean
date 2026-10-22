/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_38
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_44
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Remark_2_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient MaxTypeStep

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

namespace SmoothFunctionalConstraintsMinimizationProblem

/-
Definition 2.47 sits at the bridge/view layer between smooth functional-constraint problems and
the chapter's canonical smooth minimax owner for a fixed parameter `t`.

Sampled owner-style declarations:
* `SmoothFunctionalConstraintsMinimizationProblem` in `Definition_2_44`, which owns the ambient
  set `Q`, the objective `f₀`, and the constraint family `fᵢ`;
* `SmoothMinimaxProblem` in `Definition_2_38`, the owner abstraction for fixed-feasible-set
  max-type problems together with the derived affine model `affineApproximation`;
* `SmoothFunctionalConstraintsMinimizationProblem.toLagrangianProblem` in `Definition_2_44`
  together with `LagrangianProblem.constrainedAuxiliaryComponents` in `Lemma_2_21`, which give
  the owner fixed-`t` max-type component family;
* `maxTypeAffineApproximation` in `Lemma_2_18`, which gives the explicit max-type formula for
  the fixed-`t` affine model;
* `quadraticallyRegularizedObjective` in `Definition_1_4_17.lean`, the owner quadratic
  regularization used by the exact-step predicate `IsMinOn`.

Best owner abstraction:
* the bridge problem `problem.toParametricSmoothMinimaxProblem t`;
* the exact-step predicate
  `IsMinOn
      (quadraticallyRegularizedObjective
        ((problem.toParametricSmoothMinimaxProblem t).affineApproximation (xBar : E))
        γ
        (xBar : E))
      (problem.toParametricSmoothMinimaxProblem t).feasibleSet
      xPlus`.

Primitive data:
* the constrained problem `problem`;
* the scalar parameter `t`;
* the feasible base point `xBar : problem.ambientSet`;
* the regularization parameter `γ`;
* the exact-step point `xPlus`, through the owner `IsMinOn` predicate.

Derived API:
* the fixed-`t` bridge `toParametricSmoothMinimaxProblem`;
* the residual expression `γ • ((xBar : E) - xPlus)`.

Source/core/bridge triage:
* source-facing: the textbook constrained step notation `x_f(t; xBar; γ)` and reduced-gradient
  residual once an exact step `xPlus` is fixed;
* core/canonical: `SmoothMinimaxProblem` together with the owner `IsMinOn` exact-step predicate;
* bridge/view: `toParametricSmoothMinimaxProblem` and the explicit
  `problem.toLagrangianProblem.constrainedAuxiliaryComponents` presentation of its affine model.

Accordingly this file does not introduce a second public chosen-point API via
`Classical.choose`; downstream files should use the owner exact-step predicate directly and only
bridge back to the explicit functional-constraint model when that view is mathematically needed.
-/

/-- Shifting the objective by the scalar parameter `t` preserves the owner
`𝓢^{1,1}_{μ,L}(E)` class. -/
private theorem objective_sub_const_mem
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (t : ℝ) :
    IsStrongConvexSmoothObjective μ L (fun x : E ↦ problem.objective x - t) := by
  rcases problem.objective_mem with ⟨hμ, hcont, hstrong, hlip⟩
  refine ⟨hμ, ?_, ?_, ?_⟩
  · simpa using hcont.sub contDiff_const
  · rw [strongConvexOn_iff_convex] at hstrong ⊢
    simpa [sub_eq_add_neg, sub_add_eq_add_sub, add_assoc, add_left_comm, add_comm] using
      hstrong.add_const (-t)
  · intro x y
    simpa [gradient, fderiv_sub_const] using hlip x y

/-- The fixed-`t` functional-constraint problem, viewed through the canonical smooth minimax owner
of Chapter 2. -/
def toParametricSmoothMinimaxProblem
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (t : ℝ) :
    SmoothMinimaxProblem E (Fin (m + 1)) μ L where
  feasibleSet := problem.ambientSet
  feasible_nonempty := problem.ambient_nonempty
  feasible_closed := problem.ambient_closed
  feasible_convex := problem.ambient_convex
  components := problem.constrainedAuxiliaryComponents t
  components_mem := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using problem.objective_sub_const_mem t
    · intro j
      simpa using problem.constraints_mem j

@[simp] theorem toParametricSmoothMinimaxProblem_feasibleSet
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (t : ℝ) :
    (problem.toParametricSmoothMinimaxProblem t).feasibleSet = problem.ambientSet :=
  rfl

/-- The constrained regularized model value of the fixed-`t` bridge problem at base point `xBar`
and regularization parameter `γ`. This is the infimum of the owner quadratically regularized
affine model over the owner feasible set. -/
def regularizedModelValue
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (t : ℝ) (xBar : E) (γ : ℝ) : ℝ :=
  let parametricProblem := problem.toParametricSmoothMinimaxProblem t
  sInf
    ((quadraticallyRegularizedObjective
        (parametricProblem.affineApproximation xBar)
        γ xBar) '' parametricProblem.feasibleSet)

section ExactStep

variable [ProperSpace E]
variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (t : ℝ)

local instance instLocalChap02_Definition_2_471 : Fact problem.ambientSet.Nonempty :=
  ⟨problem.ambient_nonempty⟩

local instance instLocalChap02_Definition_2_472 : Fact (IsClosed problem.ambientSet) :=
  ⟨problem.ambient_closed⟩

local instance instLocalChap02_Definition_2_473 : Fact (Convex ℝ problem.ambientSet) :=
  ⟨problem.ambient_convex⟩

/-- Definition 2.47: the constrained gradient mapping `x_f(t; xBar; γ)` is the chosen exact step
of the quadratically regularized affine model for the fixed-`t` bridge problem on the ambient
constraint set `Q`. -/
abbrev constrainedGradientMapping
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (t : ℝ) (xBar : E) (γ : NNRealˣ) : E :=
  x_f[problem.ambientSet | (problem.toParametricSmoothMinimaxProblem t).components; γ](xBar)

namespace ConstrainedStep

scoped notation:max
    "x_f[" problem ";" t ";" γ "]" "(" xBar ")" =>
  SmoothFunctionalConstraintsMinimizationProblem.constrainedGradientMapping problem t xBar γ

end ConstrainedStep

open scoped ConstrainedStep

-- Proof sketch: unfold `constrainedGradientMapping`; the result is exactly the feasible-point
-- theorem `maxTypeGradientMapping_mem` for the fixed-`t` bridge problem.
/-- The constrained gradient mapping belongs to the ambient feasible set `Q`. -/
theorem constrainedGradientMapping_mem
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (t : ℝ) (xBar : E) (γ : NNRealˣ) :
    x_f[problem; t; γ](xBar) ∈ problem.ambientSet := by
  simpa [constrainedGradientMapping] using
    (maxTypeGradientMapping_mem_and_isMinOn_ofFact
      problem.ambientSet
      (problem.toParametricSmoothMinimaxProblem t).components
      xBar
      γ).1

-- Proof sketch: unfold `constrainedGradientMapping`; this is the exact-step theorem
-- `maxTypeGradientMapping_isMinOn` for the fixed-`t` bridge problem.
/-- The constrained gradient mapping minimizes the fixed-`t` quadratically regularized affine
model on `Q`. -/
theorem constrainedGradientMapping_isMinOn
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (t : ℝ) (xBar : E) (γ : NNRealˣ) :
    IsMinOn
      (quadraticallyRegularizedObjective
        ((problem.toParametricSmoothMinimaxProblem t).affineApproximation xBar)
        γ
        xBar)
      problem.ambientSet
      x_f[problem; t; γ](xBar) := by
  simpa [constrainedGradientMapping] using
    (maxTypeGradientMapping_mem_and_isMinOn_ofFact
      problem.ambientSet
      (problem.toParametricSmoothMinimaxProblem t).components
      xBar
      γ).2

/-- The constrained reduced gradient `g_f(t; xBar; γ)` is the reduced-gradient residual attached
to the constrained gradient mapping. -/
abbrev constrainedReducedGradient
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (t : ℝ) (xBar : E) (γ : NNRealˣ) : E :=
  g_f[problem.ambientSet | (problem.toParametricSmoothMinimaxProblem t).components; γ](xBar)

namespace ConstrainedStep

scoped notation:max
    "g_f[" problem ";" t ";" γ "]" "(" xBar ")" =>
  SmoothFunctionalConstraintsMinimizationProblem.constrainedReducedGradient problem t xBar γ

end ConstrainedStep

-- Proof sketch: unfold `constrainedReducedGradient` and `constrainedGradientMapping`; the
-- statement is the specialized defining identity of `maxTypeReducedGradient`.
/-- The constrained reduced gradient is the scaled residual from `xBar` to the constrained
gradient mapping. -/
theorem constrainedReducedGradient_eq_smul_sub
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (t : ℝ) (xBar : E) (γ : NNRealˣ) :
    g_f[problem; t; γ](xBar) =
      (γ : ℝ) • (xBar - x_f[problem; t; γ](xBar)) := by
  simpa [constrainedReducedGradient, constrainedGradientMapping] using
    maxTypeReducedGradient_eq_smul_sub_ofFact
      problem.ambientSet
      (problem.toParametricSmoothMinimaxProblem t).components
      xBar
      γ

end ExactStep

end SmoothFunctionalConstraintsMinimizationProblem
