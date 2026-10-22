/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

/- Lemma 4.1.6 lies in the Chapter 4 cubic-regularization / local-stationarity domain.

Sampled owner declarations:
* `cubicRegularizationLocalOptimalityMeasure` in `Definition_4_1_4`, the source-facing owner
  `μ[M](x)`;
* `HessianLipschitzOn` in `Definition_4_1_2`, the chapter owner for the local `C²` Hessian-
  Lipschitz hypothesis;
* `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation` in `Lemma_4_1_4`, the
  owner-level gradient estimate for a cubic-model minimizer;
* `hessianLeastEigenvalue` and the notation `λ_min(∇² f x)` in `Definition_4_1_6`.

Source/core/bridge triage:
* source-facing: the textbook estimate `μ_M(y) ≤ ‖y - x‖`;
* core/canonical: `cubicRegularizationLocalOptimalityMeasure f L M y`,
  `HessianLipschitzOn L 𝓕 f`, and
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y`;
* bridge/view: the gradient bound from `Lemma_4_1_4` together with the assumed least-eigenvalue
  lower bound at `y`.

Primitive data:
* the objective `f : E → ℝ`;
* the regularization parameter `M`;
* the Lipschitz parameter `L`;
* points `x` and `y`;
* the owner hypotheses
  `HessianLipschitzOn L 𝓕 f` and
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y`.

Derived API:
* the local-optimality-measure bound `μ[M](y) ≤ ‖y - x‖`.

The previous file kept the concrete model `EuclideanSpace ℝ (Fin n)` even though the owner
measure, the Hessian-Lipschitz owner, and the upstream cubic-minimizer estimate already live on
the intrinsic finite-dimensional real inner-product-space layer. This refinement removes that
extra model specialization instead of keeping a parallel Euclidean-only copy of the same theorem.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → ℝ} {L : NNReal}

local notation:max "μ[" M "](" x ")" =>
  cubicRegularizationLocalOptimalityMeasure f (L : ℝ) M x

-- Proof sketch: apply
-- `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation` to control the
-- gradient term in `μ_M(y)`, use the `HessianLipschitzOn` owner from `Definition_4_1_2` for the
-- on-set `C²` and Hessian-Lipschitz data, and control the spectral term by the assumed lower
-- bound on the least eigenvalue of the Hessian at `y`.
/-- Lemma 4.1.6: if `x ∈ 𝓕`, the Hessian of `f` is `L`-Lipschitz on `𝓕`, `y` globally minimizes
the cubic model centered at `x` with parameter `M`, `y ∈ 𝓕`, and the least eigenvalue of
`∇² f(y)` is bounded below by `-((M / 2) + L) ‖y - x‖`, then
`μ_M(y) ≤ ‖y - x‖`. -/
theorem cubicRegularizationLocalOptimalityMeasure_le_norm_sub_of_isMinOn
    {𝓕 : Set E} {M : ℝ} {x y : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hM : 0 < M)
    (hy :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y)
    (hx : x ∈ 𝓕)
    (hy𝓕 : y ∈ 𝓕)
    (hlambdaMin :
      -(((M / 2) + (L : ℝ)) * ‖y - x‖) ≤ λ_min(∇²f y)) :
    μ[M](y) ≤ ‖y - x‖ := by
  rw [cubicRegularizationLocalOptimalityMeasure_eq_max]
  refine max_le ?_ ?_
  · have hgrad :=
      gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation
        hf hM.le hy hx hy𝓕
    have hLM : 0 < (L : ℝ) + M := by
      exact add_pos_of_nonneg_of_pos (show 0 ≤ (L : ℝ) by exact_mod_cast L.2) hM
    have hsq :
        (2 / ((L : ℝ) + M)) * ‖∇ f y‖ ≤ ‖y - x‖ ^ (2 : ℕ) := by
      have hscale : 0 ≤ 2 / ((L : ℝ) + M) := by positivity
      calc
        (2 / ((L : ℝ) + M)) * ‖∇ f y‖
            ≤
              (2 / ((L : ℝ) + M)) *
                ((((L : ℝ) + M) / 2) * ‖y - x‖ ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hgrad hscale
        _ = ‖y - x‖ ^ (2 : ℕ) := by
          field_simp [hLM.ne']
    calc
      Real.sqrt ((2 / ((L : ℝ) + M)) * ‖∇ f y‖)
          ≤ Real.sqrt (‖y - x‖ ^ (2 : ℕ)) :=
        Real.sqrt_le_sqrt hsq
      _ = ‖y - x‖ := by
        rw [Real.sqrt_sq (norm_nonneg (y - x))]
  · have hLM : 0 < 2 * (L : ℝ) + M := by
      nlinarith [show 0 ≤ (L : ℝ) by exact_mod_cast L.2, hM]
    have hnegLambda : -λ_min(∇²f y) ≤ ((M / 2) + (L : ℝ)) * ‖y - x‖ := by
      linarith
    have hscale : 0 ≤ 2 / (2 * (L : ℝ) + M) := by positivity
    calc
      -(2 / (2 * (L : ℝ) + M)) * λ_min(∇²f y)
          = (2 / (2 * (L : ℝ) + M)) * (-λ_min(∇²f y)) := by ring
      _ ≤ (2 / (2 * (L : ℝ) + M)) * (((M / 2) + (L : ℝ)) * ‖y - x‖) :=
        mul_le_mul_of_nonneg_left hnegLambda hscale
      _ = ‖y - x‖ := by
        field_simp [hLM.ne']
        ring

end
