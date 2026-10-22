/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped Gradient ConstrainedArgmin BInducedNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.3.6 lies in the bilinear-form-induced norm / cubic-Newton-step domain on complete
real inner-product spaces.

Sampled owner-style declarations:
* `LinearMap.BilinForm.primalSeminorm` in `Definition_4_3_4`, the canonical owner of the
  `B`-induced norm `‖·‖[B]`;
* `secondOrderTaylorModelAt` in `Definition_4_1_3`, the canonical owner of the quadratic Taylor
  part of the local model;
* `IsMinOn` and `argmin[Set.univ]`, the canonical global-minimizer owners on the ambient space.

Best owner abstraction:
* source-facing: the `B`-dependent cubic Newton model and the chosen step map `T_M`;
* core/canonical: `secondOrderTaylorModelAt f x` together with the `B`-induced norm
  `‖·‖[B]`;
* bridge/view: the canonical whole-space argmin membership of the chosen step values.

Primitive data:
* the bilinear form `B`;
* the objective `f`;
* the regularization parameter `M`;
* the chosen step map `T_M`.

Derived API:
* the displayed cubic Newton model with cubic term measured in the `B`-norm;
* the whole-space minimizing property of `T_M x`;
* the residual `r_M(x) = ‖T_M(x) - x‖[B]`.

Section 4.3 uses the geometry induced by `B`, so the source-facing owner cannot be collapsed to
the earlier ambient-inner-product owner `CubicRegularizationMapping`. Route correction: the core
Chapter 4.3 owner file only keeps the intrinsic `B`-geometry API used by the surrounding
propositions, so unrelated ambient-norm comparison bridges do not force extra import
dependencies. -/

/-- The cubic Newton model from Definition 4.3.6: the second-order Taylor model of `f` at `x`,
with the constant term `f x` removed and the cubic penalty measured in the `B`-induced norm. -/
def cubicNewtonModel
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → ℝ) (M : ℝ) (x : E) : E → ℝ :=
  fun T ↦ secondOrderTaylorModelAt f x T - f x + (M / 6 : ℝ) * ‖T - x‖[B] ^ (3 : ℕ)

/-- Evaluating `cubicNewtonModel B f M x` recovers the displayed cubic Newton model formula from
Definition 4.3.6. -/
theorem cubicNewtonModel_apply
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → ℝ) (M : ℝ) (x T : E) :
    cubicNewtonModel B f M x T =
      inner ℝ (∇ f x) (T - x) +
        (1 / 2 : ℝ) * inner ℝ (hessian f x (T - x)) (T - x) +
          (M / 6 : ℝ) * ‖T - x‖[B] ^ (3 : ℕ) := by
  simp [cubicNewtonModel, secondOrderTaylorModelAt_apply]
  ring

/-- Definition 4.3.6: a cubic Newton step for the `B`-induced geometry is a map `T_M : E → E`
such that, for every base point `x`, the value `T_M x` globally minimizes the `B`-dependent cubic
Newton model centered at `x`. -/
structure CubicNewtonStep
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → ℝ) (M : ℝ) where
  /-- The chosen cubic Newton step map `T_M`. -/
  toFun : E → E
  /-- For each base point `x`, the step `T_M x` globally minimizes the `B`-dependent cubic Newton
  model centered at `x`. -/
  isMinOn (x : E) :
    IsMinOn (cubicNewtonModel B f M x) Set.univ (toFun x)

namespace CubicNewtonStep

variable {B : BilinForm ℝ E} [Fact B.toQuadraticMap.PosDef] {f : E → ℝ} {M : ℝ}

/-- A cubic Newton step acts on a base point by evaluation of its chosen map `T_M`. -/
instance : CoeFun (CubicNewtonStep B f M) (fun _ ↦ E → E) where
  coe step := step.toFun

/-- Evaluating a cubic Newton step at `x` gives a global minimizer of the `B`-dependent cubic
Newton model centered at `x`. -/
theorem isMinOn_apply
    (step : CubicNewtonStep B f M) (x : E) :
    IsMinOn (cubicNewtonModel B f M x) Set.univ (step x) :=
  step.isMinOn x

/-- Evaluating a cubic Newton step at `x` gives a point of the canonical whole-space argmin set
of the `B`-dependent cubic Newton model centered at `x`. -/
theorem mem_argmin_apply
    (step : CubicNewtonStep B f M) (x : E) :
    step x ∈ argmin[Set.univ] (cubicNewtonModel B f M x) := by
  exact mem_constrainedArgmin_iff.mpr ⟨by simp, step.isMinOn_apply x⟩

/-- The cubic Newton point `T_M(x)` satisfies the canonical first-order optimality condition for
the `B`-dependent cubic Newton model centered at `x`. -/
theorem firstOrderOptimalityCondition
    (step : CubicNewtonStep B f M) (x : E) :
    fderiv ℝ (cubicNewtonModel B f M x) (step x) = 0 := by
  simpa using IsLocalMin.fderiv_eq_zero ((step.isMinOn_apply x).isLocalMin (by simp))

/-- The residual function `r_M(x) = ‖T_M(x) - x‖[B]` attached to a cubic Newton step. -/
def residual (step : CubicNewtonStep B f M) : E → ℝ :=
  fun x ↦ ‖step x - x‖[B]

end CubicNewtonStep

scoped[CubicNewtonStepNotation] notation:max "r[" step:arg "]" =>
  CubicNewtonStep.residual step

scoped[CubicNewtonStepNotation] notation:max "r[" step:arg "](" x:arg ")" =>
  CubicNewtonStep.residual step x

namespace CubicNewtonStep

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {B : BilinForm ℝ E} [Fact B.toQuadraticMap.PosDef] {f : E → ℝ} {M : ℝ}

open scoped CubicNewtonStepNotation

/-- Evaluating `r[step](x)` recovers the textbook quantity `r_M(x) = ‖T_M(x) - x‖[B]`. -/
@[simp] theorem residual_apply
    (step : CubicNewtonStep B f M) (x : E) :
    r[step](x) = ‖step x - x‖[B] :=
  rfl

end CubicNewtonStep
