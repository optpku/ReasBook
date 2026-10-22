/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_13

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

noncomputable section

open scoped StandardSimplex
open scoped Matrix.Norms.L2Operator MatrixOrder

/- Proposition 6.14 lies in the finite simplex / entropy-smoothing / primal-dual gap domain.

Sampled owner declarations:
* `primal_dual_gap_bound_of_smoothed_lower_approximation` in `Lemma_6_12`, the chapter owner for
  the interval-valued raw primal-dual gap bound;
* `normalizedEntropyProxFunction` and
  `sSup_range_normalizedEntropyProxFunction_eq_log` in `Lemma_6_3`, the simplex entropy-prox owner
  and its maximal-value bridge;
* `l2OperatorNorm_eq_sqrt_sSup_spectrum_transpose_mul_self` in `Proposition_6_13`, the spectral
  bridge identifying the Euclidean operator norm with the displayed Gram-spectrum quantity.

Best owner abstraction:
* source-facing: the simplex matrix-game gap estimate written with the spectral right-hand side;
* core/canonical: interval membership `f xHat - φ uHat ∈ Set.Icc 0 bound`;
* bridge/view: the entropy-prox maximal value on `Δ[m]` and the operator-norm-to-spectrum rewrite.

Primitive data:
* the matrix `A`;
* the local lower-approximation bound at `xHat` with entropy budget
  `μ₂ * sSup (Set.range (normalizedEntropyProxFunction m))`;
* the pointwise inequalities `φ uHat ≤ fμ₂ xHat ≤ f xHat`;
* the residual smoothed gap bound `fμ₂ xHat - φ uHat ≤ r`;
* the chosen smoothing scale identifying that entropy budget with
  `4 ‖A‖ / √(N (N + 1))`.

Derived API:
* the operator-norm interval bound with residual term `r`;
* the spectral interval bound with residual term `r`;
* the paired-inequality companion form.

Source/core/bridge triage:
* source-facing: the spectral statement below;
* core/canonical: `primal_dual_gap_bound_of_smoothed_lower_approximation`;
* bridge/view: `sSup_range_normalizedEntropyProxFunction_eq_log` and
  `l2OperatorNorm_eq_sqrt_sSup_spectrum_transpose_mul_self`.

The previous version assumed the displayed spectral upper bound as a hypothesis and then returned
that same bound, which erased the actual simplex-smoothing content. The repaired version now
specializes the chapter's canonical raw-gap owner to the entropy-prox smoothing budget together
with the explicit residual smoothed-gap term, and uses the spectral theorem only as the final
rewrite step.
-/

-- Proof sketch: apply
-- `primal_dual_gap_bound_of_smoothed_lower_approximation` with
-- `D₂ = sSup (Set.range (normalizedEntropyProxFunction m))`. The simplex entropy-prox maximum is
-- nonnegative because it equals `log m`, and the assumed smoothing-scale identity rewrites the
-- upper endpoint to `4 ‖A‖ / √(N (N + 1))`.
section

variable {m n : ℕ+} (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ)
variable (f fμ₂ : Δ[n] → ℝ) (φ : Δ[m] → ℝ)
variable (N : ℕ) (xHat : Δ[n]) (uHat : Δ[m]) {μ₂ r : ℝ}

/-- The simplex matrix-game primal-dual gap lies in the canonical interval
`[0, 4 ‖A‖ / √(N (N + 1)) + r]` once the entropy-smoothing lower-approximation budget equals that
operator-norm quantity and the residual smoothed gap is bounded by `r`. -/
theorem simplex_matrix_game_primalDualGap_mem_Icc_of_entropy_smoothing_norm_bound
    (happrox :
      f xHat - μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) ≤ fμ₂ xHat)
    (hφ_le : φ uHat ≤ fμ₂ xHat)
    (hsmoothed_gap : fμ₂ xHat - φ uHat ≤ r)
    (hfμ₂_le : fμ₂ xHat ≤ f xHat)
    (hscale :
      μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) =
        (4 * ‖A‖) / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))
    :
    f xHat - φ uHat ∈ Set.Icc 0
      (((4 * ‖A‖) / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) + r) := by
  simpa [hscale] using
    (primal_dual_gap_bound_of_smoothed_lower_approximation
      happrox hφ_le hsmoothed_gap hfμ₂_le)

-- Proof sketch: first obtain the operator-norm interval bound above, then rewrite `‖A‖` by
-- `l2OperatorNorm_eq_sqrt_sSup_spectrum_transpose_mul_self`.
/-- Proposition 6.14: for the entropy-smoothed simplex matrix game, if the smoothing budget is
chosen so that
`μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) = 4 ‖A‖ / √(N (N + 1))`,
then the primal-dual gap at `(xHat, uHat)` lies in the interval whose upper endpoint is the
spectral quantity
`4 * sqrt (sSup (spectrum ℝ (Aᵀ * A))) / sqrt (N (N + 1)) + r`, provided the residual smoothed
gap `fμ₂ xHat - φ uHat` is bounded by `r`. -/
theorem simplex_matrix_game_primalDualGap_mem_Icc_of_entropy_smoothing_spectral_bound
    (happrox :
      f xHat - μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) ≤ fμ₂ xHat)
    (hφ_le : φ uHat ≤ fμ₂ xHat)
    (hsmoothed_gap : fμ₂ xHat - φ uHat ≤ r)
    (hfμ₂_le : fμ₂ xHat ≤ f xHat)
    (hscale :
      μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) =
        (4 * ‖A‖) / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))
    :
    f xHat - φ uHat ∈ Set.Icc 0
      ((4 * Real.sqrt (sSup (spectrum ℝ (Aᵀ * A)))) /
        Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) + r) := by
  simpa [l2OperatorNorm_eq_sqrt_sSup_spectrum_transpose_mul_self A] using
    simplex_matrix_game_primalDualGap_mem_Icc_of_entropy_smoothing_norm_bound
      A f fμ₂ φ N xHat uHat happrox hφ_le hsmoothed_gap hfμ₂_le hscale

/-- Proposition 6.14 in paired-inequality form: the simplex matrix-game primal-dual gap is
nonnegative and bounded above by the spectral entropy-smoothing estimate together with the
residual smoothed-gap term `r`. -/
theorem simplex_matrix_game_primalDualGap_nonneg_le_entropy_smoothing_spectral_bound
    (happrox :
      f xHat - μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) ≤ fμ₂ xHat)
    (hφ_le : φ uHat ≤ fμ₂ xHat)
    (hsmoothed_gap : fμ₂ xHat - φ uHat ≤ r)
    (hfμ₂_le : fμ₂ xHat ≤ f xHat)
    (hscale :
      μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) =
        (4 * ‖A‖) / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))
    :
    0 ≤ f xHat - φ uHat ∧
      f xHat - φ uHat ≤
        (4 * Real.sqrt (sSup (spectrum ℝ (Aᵀ * A)))) /
          Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) + r := by
  simpa [Set.mem_Icc] using
    simplex_matrix_game_primalDualGap_mem_Icc_of_entropy_smoothing_spectral_bound
      A f fμ₂ φ N xHat uHat happrox hφ_le hsmoothed_gap hfμ₂_le hscale

end
