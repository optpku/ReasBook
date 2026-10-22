/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SetConstrainedMinimizationProblem
open scoped LevelSetNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u

variable {E : Type u} [NormedAddCommGroup E]
variable {f : E → ℝ} {ψ : E → E → ℝ}
variable {𝓕 : Set E} {L M : ℝ}

/- Corollary 4.4.1 lies in the modified Gauss--Newton whole-space step / optimal-value bridge
domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet` in
  `Chap01/Definition_1_3_7`, the canonical owner and pointwise upper-bound API for whole-space
  optimal values;
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the owner objective whose
  optimal value is `f_M(x)`;
* `modifiedGaussNewtonOptimalValueAt` and `modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv`
  in `Proposition_4_4_6`, the chapter owner for the intrinsic quantity `f_M(x)` and its attained
  whole-space bridge;
* `IsMinOn` and `isMinOn_univ_iff` in mathlib, the canonical owner for global minimizers.

Source/core/bridge triage:
* source-facing: the textbook upper bound on the modified Gauss--Newton model value `f_M(x)`;
* core/canonical: `modifiedGaussNewtonOptimalValueAt ψ x M`;
* bridge/view: the whole-space attained-value identity
  `modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv`.

Primitive data:
* the model family `ψ`;
* the objective `f`, its global minimizer `xStar`, and a chosen whole-space step `step`;
* the sublevel-set inclusion placing `xStar` in `𝓕`.

Derived API:
* the owner-level comparison
  `modifiedGaussNewtonOptimalValueAt ψ x M ≤ quadraticallyRegularizedObjective (ψ x) M x xStar`
  from `optimalValue_le_of_mem_feasibleSet`;
* the source-facing bridge `modifiedGaussNewtonOptimalValueAt ψ x M = f[step](x)` once a
  whole-space minimizing step is chosen.

This refinement keeps the textbook inequality on the source-facing whole-space step value
`f[step](x)`. The intrinsic owner `modifiedGaussNewtonOptimalValueAt ψ x M` remains in the file
only as the supporting bridge theorem that lets the proof reuse the Chapter 1 optimal-value API
without introducing a parallel local minimization wrapper.
-/

-- Proof sketch: since `xStar` minimizes `f` on `Set.univ`, it belongs to the canonical sublevel
-- set `𝓛[f]((f x))`. The hypothesis `hlevel` therefore gives `xStar ∈ 𝓕`. Apply the quadratic
-- upper-model bound `ψ(x; y) ≤ f(y) + (L / 2) ‖y - x‖²` at `y = xStar`, then compare the
-- intrinsic owner value `modifiedGaussNewtonOptimalValueAt ψ x M` with the quadratic objective at
-- `xStar` using the Chapter 1 optimal-value owner bound.
/-- Internal bridge: the intrinsic owner `modifiedGaussNewtonOptimalValueAt ψ x M` obeys the same
quadratic upper bound at a global minimizer that later yields the textbook `f[step](x)` form of
Corollary 4.4.1. -/
theorem modifiedGaussNewtonOptimalValueAt_le_solutionValue_add_quadratic_error
    (x xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (hupper :
      ∀ ⦃y : E⦄, y ∈ 𝓕 →
        ψ x y ≤ f y + (L / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ))
    (hlevel : 𝓛[f]((f x)) ⊆ 𝓕) :
    modifiedGaussNewtonOptimalValueAt ψ x M ≤
      f xStar + ((L + M) / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
  have hxStar_mem_level : xStar ∈ 𝓛[f]((f x)) := by
    rw [mem_levelSet_iff]
    exact (isMinOn_univ_iff.mp hxStar) x
  have hxStar_mem_𝓕 : xStar ∈ 𝓕 :=
    hlevel hxStar_mem_level
  have hopt :
      modifiedGaussNewtonOptimalValueAt ψ x M ≤
        ψ x xStar + (M / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
    let problem := unconstrained (quadraticallyRegularizedObjective (ψ x) M x)
    have hopt' : problem.optimalValue ≤ (problem xStar : EReal) :=
      problem.optimalValue_le_of_mem_feasibleSet (by simp [problem])
    simpa [problem, modifiedGaussNewtonOptimalValueAt, quadraticallyRegularizedObjective_apply,
      norm_sub_rev]
      using hopt'
  have hupperStar :
      ψ x xStar ≤ f xStar + (L / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
    simpa [norm_sub_rev] using hupper hxStar_mem_𝓕
  have hsum :
      ψ x xStar + (M / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) ≤
        f xStar + ((L + M) / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
    nlinarith [hupperStar]
  exact hopt.trans <| by
    exact_mod_cast hsum

-- Proof sketch: combine the intrinsic owner-level bridge above with the whole-space identity
-- `modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv`.
/-- Corollary 4.4.1: if `xStar` globally minimizes `f`, if the sublevel set
`𝓛[f]((f x)) = {y | f y ≤ f x}` is contained in `𝓕`, and if `step` is a whole-space modified
Gauss--Newton minimizer at regularization `M`, then the textbook value `f[step](x)` satisfies
`f[step](x) ≤ f^* + ((L + M) / 2) ‖x - xStar‖²`, where `f^* = f(xStar)`. In the intended
application, `f` is the merit-function reformulation from Definition 4.4.10 and `xStar` is an
exact solution. -/
theorem modifiedGaussNewton_modelValue_le_solutionValue_add_quadratic_error
    (step : ModifiedGaussNewtonStep ψ Set.univ M)
    (x xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (hupper :
      ∀ ⦃y : E⦄, y ∈ 𝓕 →
        ψ x y ≤ f y + (L / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ))
    (hlevel : 𝓛[f]((f x)) ⊆ 𝓕) :
    f[step](x) ≤
      f xStar + ((L + M) / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
  have howner :
      modifiedGaussNewtonOptimalValueAt ψ x M ≤
        f xStar + ((L + M) / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) :=
    modifiedGaussNewtonOptimalValueAt_le_solutionValue_add_quadratic_error
      x xStar hxStar hupper hlevel
  have hmodel : (f[step](x) : EReal) ≤
      f xStar + ((L + M) / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
    simpa [modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv step x] using howner
  exact_mod_cast hmodel
