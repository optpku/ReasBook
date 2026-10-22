/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 4.4.10 lies in the merit-reformulation / unconstrained optimal-value domain.

Sampled owner-style declarations:
* `IsMeritFunction` in `Definition_4_4_1`, the chapter owner for residual scalarizers;
* `IsSharpMeritFunction` in `Definition_4_4_9`, the sharper source-facing residual scalarizer
  used later in the chapter;
* ordinary function composition, the canonical owner for the scalar objective `x ↦ φ (F x)`;
* `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the project
  owner for optimal values of whole-space objectives.

Best owner abstraction:
* source-facing: the merit reformulation `meritFunctionReformulation F φ`;
* core/canonical: ordinary function composition for the objective together with
  `SetConstrainedMinimizationProblem.optimalValue` for its optimal value;
* bridge/view: the whole-space optimal-value identity specialized to this reformulation.

Primitive data:
* a residual map `F : X → Y`;
* a scalar merit function `φ : Y → ℝ`.

Derived API:
* the evaluation formula for `meritFunctionReformulation`;
* the whole-space optimal-value identity obtained from the Chapter 1 owner.

This refinement keeps the source-facing owner `meritFunctionReformulation` and reuses the
Chapter 1 optimal-value owner instead of introducing a parallel local owner for the same
whole-space infimum.
-/

open SetConstrainedMinimizationProblem

variable {X : Type u} {Y : Type v}

/-- Definition 4.4.10: the merit-function reformulation of the nonlinear system `F(x) = 0`
attached to a residual map `F : X → Y` and a scalar merit function `φ : Y → ℝ` is the scalar
objective `f(x) = φ(F(x))` to be minimized over the whole domain. -/
def meritFunctionReformulation (F : X → Y) (φ : Y → ℝ) : X → ℝ :=
  φ ∘ F

/-- Evaluating the merit-function reformulation applies `φ` to the residual `F x`. -/
@[simp] theorem meritFunctionReformulation_apply
    (F : X → Y) (φ : Y → ℝ) (x : X) :
    meritFunctionReformulation F φ x = φ (F x) :=
  rfl

/-- The optimal value of the merit-function reformulation is the Chapter 1 whole-space optimal
value of the composed objective, hence the infimum of the values `φ (F x)`. -/
theorem meritFunctionReformulation_optimalValue_eq_sInf_range
    (F : X → Y) (φ : Y → ℝ) :
    (unconstrained (meritFunctionReformulation F φ)).optimalValue =
      sInf (Set.range fun x : X ↦ (φ (F x) : EReal)) := by
  simpa [meritFunctionReformulation] using
    (unconstrained (meritFunctionReformulation F φ)).optimalValue_eq_sInf_image
