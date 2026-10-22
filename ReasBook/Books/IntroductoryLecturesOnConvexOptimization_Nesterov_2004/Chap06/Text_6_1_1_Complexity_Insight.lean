/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Text 6.1.1-Complexity Insight lies in the chapter's scalar oracle-complexity scaling domain.

Owner-style declarations sampled before refining:
* `sqrt_rate_complexity_bound` in `Chap01/Definition_1_2_5`, the earlier project owner for turning
  a square-root rate estimate into an explicit complexity threshold;
* `constantStepSchemeIII_objective_gap_le_geometric_rate` in `Chap02/Theorem_2_46`, the chapter
  accelerated-gradient owner carrying the canonical square-root rate factor on the method side;
* mathlib `Real.sqrt_le_sqrt` and `mul_le_mul_of_nonneg_left`, the canonical scalar-order tools
  governing the proof of the present rescaling lemma.

Best owner abstraction:
* source-facing: the displayed `ε⁻¹` oracle bound for the smoothed surrogate complexity estimate;
* core/canonical: the scalar comparison
  `L_μ / ε ≤ (C_L / c_μ) / ε^2` together with monotonicity of `Real.sqrt`;
* bridge/view: this theorem, which isolates the scalar oracle-count algebra from the surrounding
  smoothing and optimization statements.

Primitive data:
* the positive scale parameters `ε` and `cμ`;
* the fast-gradient prefactor `CF`;
* the smoothing-scale inequality `cμ * ε ≤ μ`;
* the Lipschitz-growth bound `Lμ ≤ CL / μ`;
* the input oracle-count estimate `(N : ℝ) ≤ CF * sqrt (Lμ / ε)`.

Derived API:
* the explicit inverse-`ε` oracle-count bound
  `(N : ℝ) ≤ (CF * Real.sqrt (CL / cμ)) / ε`.

This file is therefore kept at the scalar bridge layer. The nearby bundled Chapter 6 smoothing
theorem should reuse this atomic lemma for its oracle-count conclusion instead of carrying a
parallel local copy of the same algebra.
-/

/-- Text 6.1.1-Complexity Insight: if the smoothed surrogate has gradient Lipschitz constant
`L_μ` with `L_μ ≤ C_L / μ`, the smoothing parameter is chosen on the scale `μ ≳ ε`, and a fast
gradient method reaches an `ε`-approximation within `C_F * √(L_μ / ε)` oracle calls, then the
number of oracle calls is bounded by a constant multiple of `ε⁻¹`. -/
-- Proof sketch: if `Lμ / ε ≤ 0`, then the oracle estimate forces `N = 0`, so the conclusion is
-- immediate. Otherwise `Lμ ≥ 0`; the lower bound `cμ * ε ≤ μ` and positivity of `ε` imply
-- `μ > 0`, hence `L_μ / ε ≤ (C_L / c_μ) / ε^2`. Taking square roots and multiplying by the
-- fast-gradient prefactor `C_F` gives the displayed `1 / ε` oracle-complexity bound.
theorem fastGradient_oracleComplexity_le_const_div_epsilon_of_smoothApproximation
    {ε μ Lμ CL CF cμ : ℝ} (hε : 0 < ε) (hcμ : 0 < cμ) (hCF : 0 ≤ CF)
    (hμ : cμ * ε ≤ μ) (hLμ : Lμ ≤ CL / μ) {N : ℕ}
    (hN : (N : ℝ) ≤ CF * Real.sqrt (Lμ / ε)) :
    (N : ℝ) ≤ (CF * Real.sqrt (CL / cμ)) / ε := by
  by_cases hLμε_nonneg : 0 ≤ Lμ / ε
  · have hμ_pos : 0 < μ := lt_of_lt_of_le (mul_pos hcμ hε) hμ
    have hLμ_nonneg : 0 ≤ Lμ := by
      have hscaled : 0 ≤ (Lμ / ε) * ε := mul_nonneg hLμε_nonneg hε.le
      simpa [div_eq_mul_inv, mul_assoc, hε.ne'] using hscaled
    have hμLμ_le : μ * Lμ ≤ CL := by
      have hscaled := mul_le_mul_of_nonneg_right hLμ hμ_pos.le
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hμ_pos.ne'] using hscaled
    have hCL : 0 ≤ CL := le_trans (mul_nonneg hμ_pos.le hLμ_nonneg) hμLμ_le
    have hLμ_le : Lμ ≤ CL / (cμ * ε) := by
      refine (le_div_iff₀ (mul_pos hcμ hε)).2 ?_
      have hscaled := mul_le_mul_of_nonneg_right hμ hLμ_nonneg
      exact (le_trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled) hμLμ_le)
    have hratio : Lμ / ε ≤ (CL / cμ) / ε ^ (2 : ℕ) := by
      have hdiv := div_le_div_of_nonneg_right hLμ_le hε.le
      simpa [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using hdiv
    have hCLcμ : 0 ≤ CL / cμ := div_nonneg hCL hcμ.le
    have hsqrt_split : Real.sqrt ((CL / cμ) / ε ^ (2 : ℕ)) = Real.sqrt (CL / cμ) / ε := by
      rw [Real.sqrt_div hCLcμ, Real.sqrt_sq_eq_abs, abs_of_pos hε]
    calc
      (N : ℝ) ≤ CF * Real.sqrt (Lμ / ε) := hN
      _ ≤ CF * Real.sqrt ((CL / cμ) / ε ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hratio) hCF
      _ = (CF * Real.sqrt (CL / cμ)) / ε := by
        rw [hsqrt_split]
        simp [div_eq_mul_inv, mul_left_comm, mul_comm]
  · have hN_zero : (N : ℝ) ≤ 0 := by
      simpa [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hLμε_nonneg)] using hN
    have hrhs_nonneg : 0 ≤ (CF * Real.sqrt (CL / cμ)) / ε := by
      exact div_nonneg (mul_nonneg hCF (Real.sqrt_nonneg _)) hε.le
    exact le_trans hN_zero hrhs_nonneg

end
