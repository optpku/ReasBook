/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E₁ : Type u} [NormedAddCommGroup E₁]

/- Definition 4.4.12 lies in the chapter's quadratic-regularized local-model domain.

Sampled owner-style declarations:
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the project owner for a
  centered quadratic regularization;
* `argmin[Set.univ] ...` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the
  canonical minimizer owner on the ambient space;
* `ModifiedGaussNewtonStep` below, the source-facing choice of a minimizing iterate map;
* `Definition_4_1_3`, the nearby chapter pattern where a source-facing step/value layer is built
  on a pre-existing model owner rather than duplicating the owner itself.

Source/core/bridge triage:
* source-facing: the modified Gauss--Newton step `V_M` on the feasible set and the derived
  quantities `r_M`, `f_M`, and `δ_M`;
* core/canonical: the centered regularized objective
  `quadraticallyRegularizedObjective (ψ x) M x`;
* bridge/view: ambient-point evaluations such as `pointAt`, `residualAt`, `modelValueAt`, and
  `modelGapAt`.

Primitive data:
* the local model family `ψ`;
* the feasible set `𝓕`;
* the regularization parameter `M`;
* the chosen minimizer map `V_M` valued in the canonical argmin owner.

Derived API:
* global minimality of `V_M(x)` for the canonical regularized objective at base point `x`;
* the residual `r_M`, model value `f_M`, and model gap `δ_M`;
* ambient-point views of the same quantities.

The objective owner is already canonical upstream, so this file keeps only the source-facing step
layer and derives its API from `quadraticallyRegularizedObjective (ψ x) M x` directly, without a
parallel ambient-point wrapper layer. -/

/-- Definition 4.4.12: on a feasible set `𝓕`, a modified Gauss--Newton step with parameter `M`
chooses, for each base point `x ∈ 𝓕`, a global minimizer `V_M(x)` of the quadratic-regularized
local model `y ↦ ψ(x; y) + (M / 2) ‖y - x‖²`. The associated quantities `r_M`, `f_M`, and `δ_M`
are defined from this chosen step in the namespace below; later results may impose `0 < M` when
that positivity is mathematically needed. -/
structure ModifiedGaussNewtonStep
    (ψ : E₁ → E₁ → ℝ) (𝓕 : Set E₁) (M : ℝ) where
  /-- The chosen modified Gauss--Newton iterate `V_M(x)` as a point of the canonical whole-space
  argmin set of the quadratic-regularized local model centered at `x`. -/
  minimizer (x : 𝓕) :
    argmin[Set.univ] (quadraticallyRegularizedObjective (ψ x) M x)

namespace ModifiedGaussNewtonStep

variable {ψ : E₁ → E₁ → ℝ} {𝓕 : Set E₁} {M : ℝ}

/-- A modified Gauss--Newton step acts on a base point by evaluation of its chosen iterate map
`V_M`. -/
instance : CoeFun (ModifiedGaussNewtonStep ψ 𝓕 M) (fun _ ↦ 𝓕 → E₁) where
  coe step x := step.minimizer x

/-- At every feasible base point `x`, the iterate `step x` belongs to the canonical whole-space
argmin set of the quadratic-regularized local model centered at `x`. -/
theorem mem_argmin
    (step : ModifiedGaussNewtonStep ψ 𝓕 M) (x : 𝓕) :
    step x ∈ argmin[Set.univ] (quadraticallyRegularizedObjective (ψ x) M x) :=
  (step.minimizer x).2

/-- At every feasible base point `x`, the iterate `step x` globally minimizes the
quadratic-regularized local model centered at `x`. -/
theorem isMinOn_apply
    (step : ModifiedGaussNewtonStep ψ 𝓕 M) (x : 𝓕) :
    IsMinOn (quadraticallyRegularizedObjective (ψ x) M x) Set.univ (step x) :=
  (mem_constrainedArgmin_iff.mp (step.mem_argmin x)).2

/-- The residual function `r_M(x) = ‖V_M(x) - x‖` on feasible base points. -/
def residual (step : ModifiedGaussNewtonStep ψ 𝓕 M) : 𝓕 → ℝ :=
  fun x ↦ ‖step x - x‖

/-- Evaluating `step.residual` recovers the textbook quantity `r_M(x) = ‖V_M(x) - x‖`. -/
@[simp]
theorem residual_apply
    (step : ModifiedGaussNewtonStep ψ 𝓕 M) (x : 𝓕) :
    step.residual x = ‖step x - x‖ :=
  rfl

/-- The quadratic-regularized model value
`f_M(x) = ψ(x; V_M(x)) + (M / 2) r_M(x)^2` on feasible base points. -/
def modelValue (step : ModifiedGaussNewtonStep ψ 𝓕 M) : 𝓕 → ℝ :=
  fun x ↦ quadraticallyRegularizedObjective (ψ x) M x (step x)

/-- Evaluating `step.modelValue` recovers the textbook quantity
`f_M(x) = ψ(x; V_M(x)) + (M / 2) r_M(x)^2`. -/
@[simp]
theorem modelValue_def
    (step : ModifiedGaussNewtonStep ψ 𝓕 M) (x : 𝓕) :
    step.modelValue x =
      ψ x (step x) + (M / 2 : ℝ) * (step.residual x) ^ (2 : ℕ) := by
  simp [modelValue]

/-- The model gap `δ_M(x) = f(x) - f_M(x)` between the merit objective and the
quadratic-regularized model value on feasible base points. -/
def modelGap (step : ModifiedGaussNewtonStep ψ 𝓕 M) (f : E₁ → ℝ) : 𝓕 → ℝ :=
  fun x ↦ f x - step.modelValue x

/-- Evaluating `step.modelGap f` gives the textbook quantity `δ_M(x) = f(x) - f_M(x)`. -/
@[simp]
theorem modelGap_def
    (step : ModifiedGaussNewtonStep ψ 𝓕 M) (f : E₁ → ℝ) (x : 𝓕) :
    step.modelGap f x = f x - step.modelValue x :=
  rfl

section WholeSpace

/-- On the whole space, the ambient-point step value at `x` needs no membership proof. -/
abbrev point
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) : E₁ :=
  step ⟨x, Set.mem_univ x⟩

/-- On the whole space, the minimizing-step property at `x` needs no membership proof. -/
theorem isMinOn_point
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) :
    IsMinOn (quadraticallyRegularizedObjective (ψ x) M x) Set.univ (step.point x) := by
  simpa [point] using step.isMinOn_apply ⟨x, Set.mem_univ x⟩

/-- On the whole space, the residual `r_M(x)` needs no membership proof. -/
abbrev residualAtUniv
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) : ℝ :=
  step.residual ⟨x, Set.mem_univ x⟩

namespace ModifiedGaussNewtonStepWholeSpaceNotation

/-- Source-facing notation for the whole-space modified Gauss--Newton residual `r_M(x)` attached
to a chosen step owner. -/
scoped notation:max "r[" step:arg "]" =>
  ModifiedGaussNewtonStep.residualAtUniv step

/-- Pointwise source-facing notation for the whole-space modified Gauss--Newton residual
`r_M(x)`. -/
scoped notation:max "r[" step:arg "](" x:arg ")" =>
  ModifiedGaussNewtonStep.residualAtUniv step x

end ModifiedGaussNewtonStepWholeSpaceNotation

open scoped ModifiedGaussNewtonStepWholeSpaceNotation

/-- Evaluating `r[step](x)` recovers the textbook quantity `r_M(x) = ‖V_M(x) - x‖`. -/
@[simp]
theorem residualAtUniv_def
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) :
    r[step](x) = ‖step.point x - x‖ := by
  rfl

/-- On the whole space, the quadratic-regularized model value `f_M(x)` needs no membership
proof. -/
abbrev modelValueAtUniv
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) : ℝ :=
  step.modelValue ⟨x, Set.mem_univ x⟩

namespace ModifiedGaussNewtonStepWholeSpaceNotation

/-- Source-facing notation for the whole-space modified Gauss--Newton model value `f_M(x)`
attached to a chosen step owner. -/
scoped notation:max "f[" step:arg "]" =>
  ModifiedGaussNewtonStep.modelValueAtUniv step

/-- Pointwise source-facing notation for the whole-space modified Gauss--Newton model value
`f_M(x)`. -/
scoped notation:max "f[" step:arg "](" x:arg ")" =>
  ModifiedGaussNewtonStep.modelValueAtUniv step x

end ModifiedGaussNewtonStepWholeSpaceNotation

open scoped ModifiedGaussNewtonStepWholeSpaceNotation

/-- Evaluating `f[step](x)` recovers the textbook quantity
`f_M(x) = ψ(x; V_M(x)) + (M / 2) r_M(x)^2`. -/
@[simp]
theorem modelValueAtUniv_def
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) :
    f[step](x) =
      ψ x (step.point x) + (M / 2 : ℝ) * (r[step](x)) ^ (2 : ℕ) := by
  simp [modelValueAtUniv, point, residualAtUniv, modelValue]

/-- On the whole space, the model gap `δ_M(x) = f(x) - f_M(x)` needs no membership proof. -/
abbrev modelGapAtUniv
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (f : E₁ → ℝ) (x : E₁) : ℝ :=
  step.modelGap f ⟨x, Set.mem_univ x⟩

namespace ModifiedGaussNewtonStepWholeSpaceNotation

/-- Source-facing notation for the whole-space modified Gauss--Newton model gap `δ_M(x)`
attached to a chosen step owner and merit objective. -/
scoped notation:max "δ[" step:arg "; " f:arg "]" =>
  ModifiedGaussNewtonStep.modelGapAtUniv step f

/-- Pointwise source-facing notation for the whole-space modified Gauss--Newton model gap
`δ_M(x)`. -/
scoped notation:max "δ[" step:arg "; " f:arg "](" x:arg ")" =>
  ModifiedGaussNewtonStep.modelGapAtUniv step f x

end ModifiedGaussNewtonStepWholeSpaceNotation

open scoped ModifiedGaussNewtonStepWholeSpaceNotation

/-- Evaluating `δ[step; f](x)` gives the textbook quantity `δ_M(x) = f(x) - f_M(x)`. -/
@[simp]
theorem modelGapAtUniv_def
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (f : E₁ → ℝ) (x : E₁) :
    δ[step; f](x) = f x - f[step](x) := by
  rfl

end WholeSpace

end ModifiedGaussNewtonStep

end
