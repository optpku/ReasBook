/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.21 lies in the restarting-gradient auxiliary-bound / logarithmic-threshold domain.

Sampled owner declarations:
* `radiusRatio_exp_neg_lt_one_of_log_threshold` in `Chap03/Proposition_3_45`, the project owner
  turning a logarithmic threshold into an exponential decay bound;
* `Real.exp_lt_one_iff` and `Real.exp_log`, the mathlib scalar owners used by that threshold
  bridge;
* `accelerated_cubic_newton_min_gradient_norm_le_explicit_rate` in `Text_4_2_18`, the nearby
  chapter pattern where the public surface is a source-facing estimate rather than a family of
  one-off scalar wrapper definitions.

Source/core/bridge triage:
* source-facing: Text 4.2.21's conclusion that every index above the displayed logarithmic
  threshold satisfies `‖∇ f (yAux k)‖ ≤ ε`;
* core/canonical: `radiusRatio_exp_neg_lt_one_of_log_threshold` together with `Real.exp`,
  `Real.log`, and `Real.sqrt`;
* bridge/view: the textbook scalar substitutions `δ = ε / (2 D²)` and `x = L₃ D² / ε`.

Primitive data:
* the objective `f`, third-derivative Lipschitz bound `L3`, radius `D`, target accuracy `ε`, and
  auxiliary sequence `yAux`;
* the positivity assumption `0 < ε`;
* the auxiliary gradient estimate after the textbook choice `δ = ε / (2 D²)` has been
  simplified to the source-facing form
  `e^(-2k/3) L₃ D² √(1 + ε / (L₃ D²)) + ε / 2`.

Derived API:
* the logarithmic threshold
  `(3 / 2) log (2 √(((L₃ D² / ε)^2) + L₃ D² / ε))`;
* the target estimate `‖∇ f (yAux k)‖ ≤ ε`.

A previous version exposed two public scalar abbreviations and a separate `δ` parameter whose only
role was to be specialized immediately by an equality hypothesis. The first refinement specialized
`δ` but still left the raw substitution artifacts on the public theorem surface. Those scalars are
not chapter owners, and `δ` is not primitive public data for the source-facing theorem. This
refinement keeps the theorem source-facing, deletes the disposable wrapper API, simplifies the
specialized auxiliary bound on the public surface, and uses ordinary binders for the thresholded
index `k`.
-/

-- Proof sketch: write `x = L₃ D² / ε`, so the assumed estimate becomes
-- `‖∇ f (yAux k)‖ ≤ ε * (x * exp (-(2k / 3)) * √(1 + 1 / x) + 1 / 2)`, and use the lower bound
-- on `k` to obtain `exp (-(2k / 3)) ≤ 1 / (2 * √(x² + x))`, which makes the parenthesized
-- factor at most `1`.
/-- Bridge/view companion for Text 4.2.21: the logarithmic threshold
`(3 / 2) log (2 √(((a / ε)^2) + a / ε))` forces the first scalar term in the restarting
auxiliary gradient estimate to be at most `ε / 2`. The source-facing theorem below then combines
this with the explicit `ε / 2` remainder term. -/
theorem restarting_auxiliary_scalar_term_le_half_of_log_threshold
    {a ε : ℝ} (hε : 0 < ε) {k : ℕ}
    (hk :
      (3 / 2 : ℝ) * Real.log (2 * Real.sqrt (((a / ε) ^ 2) + a / ε)) ≤
        (k : ℝ)) :
    Real.exp (-(2 * (k : ℝ) / 3)) * a * Real.sqrt (1 + ε / a) ≤ ε / 2 := by
  let x : ℝ := a / ε
  have hkx : (3 / 2 : ℝ) * Real.log (2 * Real.sqrt (x ^ 2 + x)) ≤ (k : ℝ) := by
    simpa [x] using hk
  by_cases hx : 0 < x
  · have ha_pos : 0 < a := by
      have hx' : 0 < a / ε := by simpa [x] using hx
      exact (div_pos_iff_of_pos_right hε).1 hx'
    have hquad_nonneg : 0 ≤ x ^ 2 + x := by
      nlinarith [hx]
    have hlog_arg_pos : 0 < 2 * Real.sqrt (x ^ 2 + x) := by
      have hquad_pos : 0 < x ^ 2 + x := by
        nlinarith [hx]
      have hsqrt_pos : 0 < Real.sqrt (x ^ 2 + x) := Real.sqrt_pos.mpr hquad_pos
      nlinarith
    have hlog_le : Real.log (2 * Real.sqrt (x ^ 2 + x)) ≤ 2 * (k : ℝ) / 3 := by
      nlinarith [hkx]
    have harg_le : 2 * Real.sqrt (x ^ 2 + x) ≤ Real.exp (2 * (k : ℝ) / 3) := by
      exact (Real.log_le_iff_le_exp hlog_arg_pos).mp hlog_le
    have hsqrt_le_half :
        Real.exp (-(2 * (k : ℝ) / 3)) * Real.sqrt (x ^ 2 + x) ≤ 1 / 2 := by
      have hexp_pos : 0 < Real.exp (2 * (k : ℝ) / 3) := Real.exp_pos _
      have hsqrt_div : Real.sqrt (x ^ 2 + x) / Real.exp (2 * (k : ℝ) / 3) ≤ 1 / 2 := by
        refine (div_le_iff₀ hexp_pos).2 ?_
        linarith
      simpa [Real.exp_neg, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hsqrt_div
    have hsqrt_id : x * Real.sqrt (1 + 1 / x) = Real.sqrt (x ^ 2 + x) := by
      have hleft_nonneg : 0 ≤ x * Real.sqrt (1 + 1 / x) := by
        positivity
      have hright_nonneg : 0 ≤ Real.sqrt (x ^ 2 + x) := by
        positivity
      apply (mul_self_inj_of_nonneg hleft_nonneg hright_nonneg).1
      have hone_nonneg : 0 ≤ 1 + 1 / x := by
        positivity
      calc
        (x * Real.sqrt (1 + 1 / x)) * (x * Real.sqrt (1 + 1 / x)) =
            x ^ 2 * (Real.sqrt (1 + 1 / x)) ^ 2 := by
              ring
        _ = x ^ 2 * (1 + 1 / x) := by
          rw [Real.sq_sqrt hone_nonneg]
        _ = x ^ 2 + x := by
          field_simp [hx.ne']
        _ = Real.sqrt (x ^ 2 + x) * Real.sqrt (x ^ 2 + x) := by
          rw [← sq, Real.sq_sqrt hquad_nonneg]
    have ha_eq : a = ε * x := by
      dsimp [x]
      field_simp [hε.ne']
    have hdiv_eq : ε / (ε * x) = 1 / x := by
      field_simp [hε.ne', hx.ne']
    calc
      Real.exp (-(2 * (k : ℝ) / 3)) * a * Real.sqrt (1 + ε / a) =
          ε * (Real.exp (-(2 * (k : ℝ) / 3)) * (x * Real.sqrt (1 + 1 / x))) := by
            rw [ha_eq, hdiv_eq]
            ring
      _ = ε * (Real.exp (-(2 * (k : ℝ) / 3)) * Real.sqrt (x ^ 2 + x)) := by
        rw [hsqrt_id]
      _ ≤ ε * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hsqrt_le_half hε.le
      _ = ε / 2 := by ring
  · have hx_nonpos : x ≤ 0 := le_of_not_gt hx
    have ha_nonpos : a ≤ 0 := by
      have hx' : a / ε ≤ 0 := by simpa [x] using hx_nonpos
      simpa using (div_le_iff₀ hε).1 hx'
    have hfirst_nonpos :
        Real.exp (-(2 * (k : ℝ) / 3)) * a * Real.sqrt (1 + ε / a) ≤ 0 := by
      have hmid_nonpos : a * Real.sqrt (1 + ε / a) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ha_nonpos (Real.sqrt_nonneg _)
      have hexp_nonneg : 0 ≤ Real.exp (-(2 * (k : ℝ) / 3)) := (Real.exp_pos _).le
      simpa [mul_assoc] using mul_nonpos_of_nonneg_of_nonpos hexp_nonneg hmid_nonpos
    linarith

/-- Text 4.2.21: if the auxiliary points of a restarting scheme satisfy
`‖∇ f (y_k^*)‖ ≤ e^(-2k/3) L₃ D² √(1 + ε / (L₃ D²)) + ε / 2` for every `k`, then every index
`k` above the logarithmic threshold `(3 / 2) log (2 √(x² + x))`, with `x = L₃ D² / ε`,
satisfies `‖∇ f (y_k^*)‖ ≤ ε`. -/
theorem gradient_norm_le_target_of_restarting_auxiliary_bound
    (f : E → ℝ) (L3 : NNReal) (D ε : ℝ) (yAux : ℕ → E)
    (hε : 0 < ε)
    (hbound :
      ∀ k : ℕ,
        ‖∇ f (yAux k)‖ ≤
          Real.exp (-(2 * (k : ℝ) / 3)) * (L3 : ℝ) * D ^ 2 *
              Real.sqrt (1 + ε / ((L3 : ℝ) * D ^ 2)) +
            ε / 2)
    (k : ℕ)
    (hk :
      (3 / 2 : ℝ) * Real.log
          (2 * Real.sqrt ((((L3 : ℝ) * D ^ 2 / ε) ^ 2) + (L3 : ℝ) * D ^ 2 / ε)) ≤
        (k : ℝ)) :
    ‖∇ f (yAux k)‖ ≤ ε := by
  have hfirst_le :
      Real.exp (-(2 * (k : ℝ) / 3)) * (L3 : ℝ) * D ^ 2 *
          Real.sqrt (1 + ε / ((L3 : ℝ) * D ^ 2)) ≤
        ε / 2 := by
    simpa [mul_assoc] using
      (restarting_auxiliary_scalar_term_le_half_of_log_threshold hε hk :
        Real.exp (-(2 * (k : ℝ) / 3)) * ((L3 : ℝ) * D ^ 2) *
            Real.sqrt (1 + ε / ((L3 : ℝ) * D ^ 2)) ≤
          ε / 2)
  linarith [hbound k, hfirst_le]

end
