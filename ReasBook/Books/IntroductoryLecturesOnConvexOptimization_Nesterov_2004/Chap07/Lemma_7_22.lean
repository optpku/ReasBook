/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_20

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RelativeScaleTransformNotation

universe u v

/- Lemma 7.22 lies in the chapter's relative-scale transform / algebraic metric-update domain.

Sampled owner-style declarations:
- `relativeScaleTransformedObjective` in `Lemma_7_20`, the Chapter 7 owner of the textbook
  transform `f̂`;
- `relativeScaleTransformedObjective_apply` in `Lemma_7_20`, the owner-side evaluation formula for
  `f̂`;
- `relativeScaleTransformedSubgradient` in `Lemma_7_20`, the Chapter 7 owner of the textbook
  transformed subgradient `ĝ[f; x] g`;
- `relativeScaleTransformedSubgradient_def` in `Lemma_7_20`, the owner-side evaluation formula for
  `ĝ[f; x] g`.

Best owner abstraction:
- source-facing: the progress identity for the transformed objective and transformed subgradient;
- core/canonical: the Chapter 7 owners `relativeScaleTransformedObjective` and
  `relativeScaleTransformedSubgradient`;
- bridge/view: this purely algebraic simplification theorem for an abstract squared dual norm.

Primitive data:
- a type `X` carrying scalar multiplication by `ℝ`;
- a metric parameter type `Metric` and a squared dual norm `dualNormSq : Metric → X → ℝ`;
- the current and updated metrics, an objective `f`, points `xk`, `gk`, and scalars `a`, `δ`.

Derived API:
- the transformed objective notation `f̂ xk`;
- the transformed subgradient notation `ĝ[f; xk] gk`;
- the algorithmic progress identity below.

This lemma is algebraic: it uses only the Chapter 7 transform owners and scalar arithmetic, so the
ambient space should stay on the weakest owner-compatible layer rather than the concrete model
`EuclideanSpace ℝ (Fin n)`.
-/
/-- Lemma 7.22: if the transformed subgradient norm at the updated metric `G_{k+1}` scales by
`f(x_k)^2`, the rank-one metric update sends the squared dual norm of `g_k` from `G_k` to
`(1 - δ)` times its old value, the accuracy parameter satisfies `δ ≠ 1`, and the step size `a_k`
satisfies the displayed reciprocal norm identity, then the algorithmic progress identity
`(1 / 2) a_k^2 ‖ĝ[f; x_k] g_k‖_{G_{k+1}}^{*2} = δ a_k f̂ x_k` holds. -/
theorem algorithmic_progress_identity
    {X : Type u} [SMul ℝ X] {Metric : Type v} (dualNormSq : Metric → X → ℝ)
    {Gk GkNext : Metric} {f : X → ℝ} {xk gk : X} {a δ : ℝ}
    (hδ : δ ≠ 1)
    (htransformed_norm :
      dualNormSq GkNext (ĝ[f; xk] gk) =
        (f xk) ^ (2 : ℕ) * dualNormSq GkNext gk)
    (hmetric_update :
      dualNormSq GkNext gk = (1 - δ) * dualNormSq Gk gk)
    (hstep :
      dualNormSq Gk gk = δ / ((1 - δ) * a)) :
    (1 / 2 : ℝ) * a ^ (2 : ℕ) *
        dualNormSq GkNext (ĝ[f; xk] gk) =
      δ * a * f̂ xk := by
  rw [htransformed_norm, hmetric_update, hstep, relativeScaleTransformedObjective_apply]
  have hδ' : 1 - δ ≠ 0 := sub_ne_zero.mpr hδ.symm
  by_cases ha : a = 0
  · subst ha
    simp
  · field_simp [hδ', ha]

end
