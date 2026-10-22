/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold
open scoped ModifiedGaussNewtonLocalModelNotation

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/- Lemma 4.4.1 lies in the merit-scalarization / Gauss--Newton local-model domain.

Sampled owner-style declarations:
* `meritFunctionReformulation` in `Definition_4_4_10`, the source-facing owner for merit
  scalarization by composition;
* `modifiedGaussNewtonLocalModel` in `Definition_4_4_11`, the source-facing owner for the
  Gauss--Newton local model;
* `jacobian_lipschitz_taylor_remainder_le` in `Proposition_4_4_5`, the owner bridge for the
  residual linearization error under Jacobian Lipschitz control;
* `LipschitzWith.norm_sub_le` in mathlib, the canonical pointwise consequence of a
  `1`-Lipschitz scalarizer.

Best owner abstraction:
* source-facing: the textbook discrepancy bound between the merit reformulation and the
  Gauss--Newton local model;
* core/canonical: the owners `LipschitzWith`, `meritFunctionReformulation`,
  `modifiedGaussNewtonLocalModel`, and `LipschitzOnWith` on the derivative map;
* bridge/view: this lemma, obtained by applying the scalarizer Lipschitz estimate to the
  residual Taylor remainder owner theorem.

Primitive data:
* a bundled smooth residual map `problem`;
* a `1`-Lipschitz scalarizer `φ`;
* a convex feasible set `𝓕`;
* the Jacobian-Lipschitz owner `h_jacobian_lipschitz`.

Derived API:
* the bound on the scalarized discrepancy between `f(y)` and `ψ(x; y)`.

This file therefore keeps only the source-facing discrepancy theorem and reuses the canonical
Taylor remainder owner from `Proposition_4_4_5` instead of carrying a parallel local remainder
API. -/

-- Proof sketch: write the model discrepancy as
-- `|φ (F y) - φ (F x + F'(x) (y - x))|`, use the `1`-Lipschitz property of the scalarizer `φ`
-- to bound it by the norm of the residual linearization error, and then apply the
-- first-order Taylor remainder estimate for `F` on the convex feasible set `𝓕` under the
-- derivative Lipschitz hypothesis.
/-- Lemma 4.4.1: if `𝓕` is convex and `x` and `y` belong to `𝓕`, then the difference between the
merit reformulation `f(y) = φ(F y)` and the modified Gauss--Newton local model
`ψ(x; y) = φ(F(x) + F'(x)(y - x))` is bounded by `((L : ℝ) / 2) * ‖y - x‖²`. -/
theorem abs_meritFunctionReformulation_sub_modifiedGaussNewtonLocalModel_le
    (problem : C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯)
    (φ : F → ℝ) (hφ : LipschitzWith 1 φ)
    {𝓕 : Set E} {L : NNReal}
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    {x y : E} (hx : x ∈ 𝓕) (hy : y ∈ 𝓕) :
    |meritFunctionReformulation problem φ y -
        ψ[problem; φ; (fderiv ℝ problem)](x; y)| ≤
      ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  calc
    |meritFunctionReformulation problem φ y - ψ[problem; φ; (fderiv ℝ problem)](x; y)|
        = ‖φ (problem y) - φ (problem x + fderiv ℝ problem x (y - x))‖ := by
            simp
    _ ≤ ‖problem y - (problem x + fderiv ℝ problem x (y - x))‖ := by
      simpa [dist_eq_norm] using
        hφ.norm_sub_le (problem y)
          (problem x + fderiv ℝ problem x (y - x))
    _ ≤ ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        problem.jacobian_lipschitz_taylor_remainder_le
          h𝓕 h_jacobian_lipschitz x y hx hy
