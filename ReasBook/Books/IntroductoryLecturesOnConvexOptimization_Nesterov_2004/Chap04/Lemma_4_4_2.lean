/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]

open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

/- Lemma 4.4.2 lies in the modified Gauss--Newton quadratic-regularization domain.

Sampled owner-style declarations:
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the canonical owner of the
  centered quadratic penalty model;
* `ModifiedGaussNewtonStep.isMinOn_point` in `Definition_4_4_12`, the minimizing-step owner for
  the regularized local model;
* the whole-space notation/API `δ[step; f](x)` and `r[step](x)` from
  `Definition_4_4_12`, the whole-space source-facing bridge views;
* mathlib `ConvexOn`, the intrinsic convexity owner for the local model slice `ψ x`.

Source/core/bridge triage:
* source-facing: the modified Gauss--Newton model-gap estimate at a base point `x`;
* core/canonical: a convex local model slice `ψ x` together with the minimizer owner
  `step.isMinOn_point x` for the quadratic-regularized objective;
* bridge/view: the whole-space quantities `δ[step; f](x)` and `r[step](x)`.

Primitive data:
* the local model slice `ψ x`;
* its convexity in the trial-point variable;
* the regularization parameter `M`;
* the chosen minimizing step.

Derived API:
* segment comparisons between the minimizer `step.point x` and points on the ray from `x`;
* the source-facing lower bound for the modified Gauss--Newton model gap.

This lower bound does not need a separate strong-convexity wrapper for the quadratic penalty.
Convexity of `ψ x` and the owner minimizer property for the regularized objective already imply the
required estimate on a real normed space. -/

open ModifiedGaussNewtonStep

-- Proof sketch: use convexity of `ψ x` to make the quadratic-regularized local model
-- `quadraticallyRegularizedObjective (ψ x) M x` smaller at its minimizer `step x` than at every
-- segment point `x + t (step x - x)` with `0 ≤ t < 1`. Convexity of `ψ x` bounds the local model
-- at those segment points by a convex combination of `ψ x x` and `ψ x (step x)`, which yields
-- `δ_M(x) ≥ t (M / 2) r_M(x)^2` for every `t < 1`; then let `t` approach `1`.
/-- Lemma 4.4.2: if the local model slice `ψ(x; ·)` is convex on the whole space, then for a
modified Gauss--Newton step on the whole space the model improvement `δ_M(x)` attached to the
diagonal objective `f(x) = ψ(x; x)` satisfies `δ_M(x) ≥ (M / 2) r_M(x)^2`. -/
theorem modifiedGaussNewton_modelGap_ge_half_mul_residual_sq
    {ψ : E₁ → E₁ → ℝ} {M : ℝ}
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁)
    (hconv : ConvexOn ℝ Set.univ (ψ x)) :
    δ[step; fun z ↦ ψ z z](x) ≥
      (M / 2 : ℝ) * (r[step](x)) ^ (2 : ℕ) := by
  let f : E₁ → ℝ := fun z ↦ ψ z z
  let obj : E₁ → ℝ := quadraticallyRegularizedObjective (ψ x) M x
  let y := step.point x
  let c : ℝ := (M / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)
  have hmin : IsMinOn obj Set.univ y := by
    simpa [obj, y] using step.isMinOn_point x
  have hdelta : δ[step; f](x) = ψ x x - ψ x y - c := by
    simp [f, c, y]
    ring
  have hδ0 : 0 ≤ δ[step; f](x) := by
    have hx := (isMinOn_univ_iff.mp hmin) x
    simpa [f, obj, c, y, quadraticallyRegularizedObjective_apply] using hx
  by_cases hc : c ≤ 0
  · have hgoal : (M / 2 : ℝ) * (r[step](x)) ^ (2 : ℕ) ≤ 0 := by
      simpa [ModifiedGaussNewtonStep.residualAtUniv_def, y, c] using hc
    linarith
  · have hc_pos : 0 < c := lt_of_not_ge hc
    have hc_le : c ≤ δ[step; f](x) := by
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      by_cases hε_large : c ≤ ε
      · linarith
      · have hε_lt_c : ε < c := lt_of_not_ge hε_large
        let t : ℝ := 1 - ε / c
        have ht_nonneg : 0 ≤ t := by
          have ht_lt_one' : ε / c < 1 := (div_lt_one hc_pos).2 hε_lt_c
          dsimp [t]
          linarith
        have ht_lt_one : t < 1 := by
          dsimp [t]
          have : 0 < ε / c := by positivity
          linarith
        have hmin_t := (isMinOn_univ_iff.mp hmin) (x + t • (y - x))
        have hconv_t :
            ψ x (x + t • (y - x)) ≤ (1 - t) * ψ x x + t * ψ x y := by
          have hsegment : x + t • (y - x) = AffineMap.lineMap x y t := by
            rw [AffineMap.lineMap_apply_module']
            ac_rfl
          simpa [hsegment, AffineMap.lineMap_apply_module, smul_eq_mul] using
            hconv.2 (by simp) (by simp) (sub_nonneg.mpr ht_lt_one.le) ht_nonneg (by ring)
        have hsub_t : x + t • (y - x) - x = t • (y - x) := by
          abel_nf
        have hnorm_t :
            ‖x + t • (y - x) - x‖ ^ (2 : ℕ) = t ^ (2 : ℕ) * ‖y - x‖ ^ (2 : ℕ) := by
          rw [hsub_t, norm_smul, Real.norm_of_nonneg ht_nonneg, mul_pow]
        have hpenalty_t :
            (M / 2 : ℝ) * ‖x + t • (y - x) - x‖ ^ (2 : ℕ) = c * t ^ (2 : ℕ) := by
          rw [hnorm_t]
          simp [c]
          ring
        have hbound :
            ψ x y + c ≤ (1 - t) * ψ x x + t * ψ x y + c * t ^ (2 : ℕ) := by
          calc
            ψ x y + c = obj y := by
              show ψ x y + c = quadraticallyRegularizedObjective (ψ x) M x y
              simp [c, quadraticallyRegularizedObjective_apply]
            _ ≤ obj (x + t • (y - x)) := hmin_t
            _ = ψ x (x + t • (y - x)) + c * t ^ (2 : ℕ) := by
                  change quadraticallyRegularizedObjective (ψ x) M x (x + t • (y - x)) =
                    ψ x (x + t • (y - x)) + c * t ^ (2 : ℕ)
                  rw [quadraticallyRegularizedObjective_apply, hpenalty_t]
            _ ≤ (1 - t) * ψ x x + t * ψ x y + c * t ^ (2 : ℕ) := by linarith
        have hct : c - ε = c * t := by
          dsimp [t]
          field_simp [hc_pos.ne']
        have hct_le : c * t ≤ δ[step; f](x) := by
          nlinarith [hbound, hdelta]
        linarith
    simpa [ModifiedGaussNewtonStep.residualAtUniv_def, y, c] using hc_le
