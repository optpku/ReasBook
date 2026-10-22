/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SetConstrainedMinimizationProblem
open scoped Manifold
open scoped ModifiedGaussNewtonLocalModelNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Lemma 4.4.5 lies in the merit-scalarization / quadratic-regularized local-model domain.

Sampled owner-style declarations:
* `abs_meritFunctionReformulation_sub_modifiedGaussNewtonLocalModel_le` in `Lemma_4_4_1`, the
  chapter owner for comparing the true merit objective with the modified Gauss--Newton local
  model under the primitive scalarizer hypothesis `LipschitzWith 1 φ`;
* `modifiedGaussNewtonLocalModel` in `Definition_4_4_11`, the source-facing owner for the local
  model `ψ(x; y)`;
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the canonical project owner
  for the quadratic penalty added to a model;
* `SetConstrainedMinimizationProblem` and `SetConstrainedMinimizationProblem.optimalValue` in
  `Chap01/Definition_1_3_3` and `Chap01/Definition_1_3_7`, the canonical owner for the feasible
  minimization-value layer;
* `LipschitzWith.norm_sub_le` in mathlib, the canonical pointwise estimate used to compare
  scalarizer values.

Best owner abstraction:
* source-facing: the textbook upper bound on the modified Gauss--Newton model value `f_M(x)`;
* core/canonical: `LipschitzWith`, `modifiedGaussNewtonLocalModel`,
  `quadraticallyRegularizedObjective`, `ModifiedGaussNewtonStep`, and the Chapter 1 owner
  `SetConstrainedMinimizationProblem.optimalValue`;
* bridge/view: the textbook `sInf` formula over the feasible subtype `𝓕`.

Primitive data:
* the residual map `problem`;
* the scalarizer `φ` together with its primitive canonical regularity input `LipschitzWith 1 φ`;
* the feasible set `𝓕` and Jacobian-Lipschitz bound on `problem`;
* the chosen modified Gauss--Newton step `step`.

Derived API:
* the pointwise comparison with the feasible merit-plus-quadratic objective
  `y ↦ meritFunctionReformulation problem φ y + (((L : ℝ) + M) / 2) * ‖y - x‖²`;
* the textbook real-valued `sInf` bound over the feasible subtype `𝓕`.

This refinement keeps Lemma 4.4.5 at the source-facing textbook `sInf` layer while reusing the
chapter and project owner API directly, without introducing a one-off public wrapper around
`SetConstrainedMinimizationProblem.mk`.
-/

-- Proof sketch: global minimality of `step x` bounds `step.modelValue x` by the
-- quadratic-regularized local model at every comparison point `y`. The discrepancy estimate from
-- Lemma 4.4.1 then bounds the local model by the merit reformulation plus `(L / 2) ‖y - x‖²`,
-- and adding the existing `(M / 2) ‖y - x‖²` term yields the comparison objective.
/-- For every feasible comparison point `y ∈ 𝓕`, the model value `f_M(x)` is bounded above by
the feasible merit-plus-quadratic objective from Lemma 4.4.5 evaluated at `y`. -/
theorem modifiedGaussNewton_modelValue_le_feasibleMeritQuadraticObjective
    (problem : C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯)
    (φ : E₂ → ℝ) (hφ : LipschitzWith 1 φ)
    {𝓕 : Set E₁} {L : NNReal} {M : ℝ}
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (step :
      ModifiedGaussNewtonStep
        (ψ[problem; φ; (fderiv ℝ problem)])
        𝓕 M)
    (x : 𝓕) {y : E₁} (hy : y ∈ 𝓕) :
    step.modelValue x ≤
      meritFunctionReformulation problem φ y +
        (((L : ℝ) + M) / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
  have hmin :
      step.modelValue x ≤
        quadraticallyRegularizedObjective
          (ψ[problem; φ; (fderiv ℝ problem)] x) M x y :=
    (isMinOn_univ_iff.mp (step.isMinOn_apply x)) y
  have hmodel :
      ψ[problem; φ; (fderiv ℝ problem)](x; y) ≤
        meritFunctionReformulation problem φ y +
          ((L : ℝ) / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
    have hdiscrepancy :=
      abs_meritFunctionReformulation_sub_modifiedGaussNewtonLocalModel_le
        problem φ hφ h𝓕 h_jacobian_lipschitz x.2 hy
    have hlower :
        -(((L : ℝ) / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) ≤
          meritFunctionReformulation problem φ y -
            ψ[problem; φ; (fderiv ℝ problem)](x; y) :=
      (abs_le.mp hdiscrepancy).1
    linarith
  have hcompare :
      quadraticallyRegularizedObjective
          (ψ[problem; φ; (fderiv ℝ problem)] x) M x y ≤
        meritFunctionReformulation problem φ y +
          (((L : ℝ) + M) / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
    rw [quadraticallyRegularizedObjective_apply]
    linarith
  exact hmin.trans hcompare

-- Proof sketch: the feasible-value set is nonempty because it contains the base point `x`, and
-- the pointwise comparison theorem shows it is bounded below by `step.modelValue x`. The desired
-- real-valued `sInf` bound then follows from `le_csInf`.
/-- Lemma 4.4.5:
`f_M(x)` is bounded above by
`inf_{y ∈ 𝓕} [f(y) + ((L + M) / 2) ‖y - x‖²]`,
written as the infimum over the feasible subtype. -/
theorem modifiedGaussNewton_modelValue_le_sInf_feasible_merit_plus_quadratic
    (problem : C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯)
    (φ : E₂ → ℝ) (hφ : LipschitzWith 1 φ)
    {𝓕 : Set E₁} {L : NNReal} {M : ℝ}
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (step :
      ModifiedGaussNewtonStep
        (ψ[problem; φ; (fderiv ℝ problem)])
        𝓕 M)
    (x : 𝓕) :
    step.modelValue x ≤
      sInf (Set.range fun y : 𝓕 ↦
        meritFunctionReformulation problem φ (y : E₁) +
          (((L : ℝ) + M) / 2 : ℝ) * ‖(y : E₁) - x‖ ^ (2 : ℕ)) := by
  refine le_csInf ?_ ?_
  · exact ⟨_, ⟨x, rfl⟩⟩
  · intro b hb
    rcases hb with ⟨y, rfl⟩
    exact modifiedGaussNewton_modelValue_le_feasibleMeritQuadraticObjective
      problem φ hφ h𝓕 h_jacobian_lipschitz step x y.2
