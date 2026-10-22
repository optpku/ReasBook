/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_4_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open ModifiedGaussNewtonStep
open scoped InnerProduct MinimalSingularValue
open scoped ModifiedGaussNewtonLocalModelNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
variable [FiniteDimensional ℝ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
variable [FiniteDimensional ℝ E₂]

/- Lemma 4.4.7 lies in the modified Gauss--Newton local-model / dual-nondegeneracy domain.

Sampled owner-style declarations:
* `IsMeritFunction` in `Definition_4_4_1`, the chapter owner for nonnegative residual
  scalarizers that vanish exactly at the zero residual;
* `modifiedGaussNewtonLocalModel` with notation `ψ[F; φ; J]` in `Definition_4_4_11`, the
  source-facing owner for the local affine residual model;
* `ModifiedGaussNewtonStep.isMinOn_point` and `ModifiedGaussNewtonStep.residualAtUniv` in
  `Definition_4_4_12`, the whole-space step owner together with the source-facing residual
  notation `r[step](x)`;
* `ContinuousLinearMap.exists_preimage_norm_le_of_adjoint_minimalSingularValue_pos` in
  `Lemma_4_4_6`, the canonical linear-algebra bridge from `0 < σ_min(A†)` to a controlled right
  inverse.

Best owner abstraction:
* source-facing: the textbook residual bound for a whole-space modified Gauss--Newton step;
* core/canonical: `ModifiedGaussNewtonStep ... Set.univ M` together with
  `ContinuousLinearMap.exists_preimage_norm_le_of_adjoint_minimalSingularValue_pos`;
* bridge/view: the whole-space residual `r[step](x)`.

Primitive data:
* a residual map `problem`;
* a merit-function owner `[IsMeritFunction φ]` for the scalarizer `φ`;
* a positive regularization parameter `M`;
* a chosen whole-space modified Gauss--Newton step `step`;
* the pointwise dual nondegeneracy hypothesis `0 < σ_min((fderiv ℝ problem x)†)`.

Derived API:
* a controlled correction `h` solving the linearized equation at `x`;
* the source-facing residual bound `r[step](x) ≤ ‖problem x‖ / σ_min((F'(x))†)`.

The previous surface stored only the isolated datum `φ 0 = 0` and threaded a local `Set.univ`
membership proof through `residualAt`. Both are derived from existing owners: `φ 0 = 0` is part
of the merit-function owner, and the whole-space residual already has the canonical bridge
`r[step](x)`. The file also does not need the more concrete `ContMDiffMap` model wrapper:
Definition 4.4.11 and Lemma 4.4.6 only use the primitive residual map together with the canonical
total derivative `fderiv ℝ problem`.
-/

section ResidualBound

variable (problem : E₁ → E₂) (φ : E₂ → ℝ) [IsMeritFunction φ]

local notation "ψ" => ψ[problem; φ; (fderiv ℝ problem)]

-- Proof sketch: apply the owner theorem
-- `ContinuousLinearMap.exists_preimage_norm_le_of_adjoint_minimalSingularValue_pos`, and the
-- Jacobian `fderiv ℝ problem x` to the right-hand side `-problem x` to obtain a correction `h*`
-- with
-- `problem x + fderiv ℝ problem x h* = 0` and
-- `‖h*‖ ≤ ‖problem x‖ / σ_min((fderiv ℝ problem x)†)`. Use `x + h*` as a competitor in the
-- global minimization property of `step`. Since merit functions are nonnegative and vanish at the
-- zero residual, the local-model term at `x + h*` is `0`, so positivity of `M` lets the
-- quadratic term control `r[step](x)`.
/-- Lemma 4.4.7: if the Jacobian `F'(x)` is dual nondegenerate, then the modified Gauss--Newton
residual `r_M(x)` is bounded by `‖F(x)‖ / σ_min(F'(x)^*)`. -/
theorem modifiedGaussNewton_residual_le_nonlinearResidual_div_minimalSingularValue_adjoint
    {M : ℝ} (hM : 0 < M)
    (step : ModifiedGaussNewtonStep ψ Set.univ M)
    (x : E₁)
    (hdual : 0 < σ_min((fderiv ℝ problem x)†)) :
    r[step](x) ≤ ‖problem x‖ / σ_min((fderiv ℝ problem x)†) := by
  let A : E₁ →L[ℝ] E₂ := fderiv ℝ problem x
  have hdualA : 0 < σ_min(A†) := by
    simpa [A] using hdual
  have hpreimage :
      ∃ h : E₁,
        A h = -problem x ∧ ‖h‖ ≤ ‖-problem x‖ / σ_min(A†) :=
    A.exists_preimage_norm_le_of_adjoint_minimalSingularValue_pos hdualA (-problem x)
  rcases hpreimage with
    ⟨h, hh, hbound⟩
  have hh' : fderiv ℝ problem x h = -problem x := by
    simpa [A] using hh
  have hzero : problem x + fderiv ℝ problem x h = 0 := by
    rw [hh']
    simp
  have hmin :
      f[step](x) ≤ quadraticallyRegularizedObjective (ψ x) M x (x + h) := by
    simpa [modelValueAtUniv_def, residualAtUniv_def, quadraticallyRegularizedObjective_apply] using
      (isMinOn_univ_iff.mp (step.isMinOn_point x)) (x + h)
  have hleft :
      (M / 2 : ℝ) * (r[step](x)) ^ (2 : ℕ) ≤ f[step](x) := by
    have hnonneg : 0 ≤ ψ x (step.point x) := by
      simpa [modifiedGaussNewtonLocalModel_apply] using
        (IsMeritFunction.nonneg
          (problem x + fderiv ℝ problem x (step.point x - x)))
    have hle :
        (M / 2 : ℝ) * (r[step](x)) ^ (2 : ℕ) ≤
          ψ x (step.point x) + (M / 2 : ℝ) * (r[step](x)) ^ (2 : ℕ) := by
      linarith
    simpa [modelValueAtUniv_def]
      using hle
  have hφ_zero : φ 0 = 0 := by
    simpa using (IsMeritFunction.eq_zero_iff 0).2 rfl
  have hright :
      quadraticallyRegularizedObjective (ψ x) M x (x + h) = (M / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) := by
    simp [quadraticallyRegularizedObjective_apply, modifiedGaussNewtonLocalModel_apply, hzero,
      hφ_zero]
  have hquad :
      (M / 2 : ℝ) * (r[step](x)) ^ (2 : ℕ) ≤
        (M / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) :=
    hleft.trans <| hmin.trans_eq hright
  have hsq :
      (r[step](x)) ^ (2 : ℕ) ≤ ‖h‖ ^ (2 : ℕ) := by
    nlinarith [hM, hquad]
  have hres_nonneg : 0 ≤ r[step](x) := by
    simp
  have hres_le : r[step](x) ≤ ‖h‖ := by
    nlinarith [hsq, hres_nonneg, norm_nonneg h]
  simpa [norm_neg] using hres_le.trans hbound

end ResidualBound
