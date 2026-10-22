/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

section

/-
Primary domain: scalar logarithmic complexity bounds obtained from one-step exponential gap
estimates.

Owner abstractions sampled before refining:
- `Real.le_log_iff_exp_le` for the canonical passage from a positive exponential inequality to a
  logarithmic bound;
- `Real.log_mul` for the canonical split of the product ratio into the constant term
  `log (2 * (Qf - 1) / κ)` and the terminal ratio `log (Δ k / Δ (k + 1))`;
- the accumulated-sum helper later used in `Proposition_2_33.lean`, whose one-step input is
  exactly the split logarithmic bound produced here.

Best owner abstraction:
- the direct one-step exponential estimate on `Δ (k + 1)`, which is the minimal scalar input
  needed for the logarithmic stopping-index bound.

Primitive data:
- the sequences `j` and `Δ`;
- the positivity of `Δ (k + 1)`;
- the direct exponential bound for `Δ (k + 1)`.

Source/core/bridge triage:
- source-facing: the textbook one-step logarithmic stopping-index estimate;
- core/canonical: `stoppingIndex_le_one_add_sqrt_condition_log_ratio`;
- bridge/view: downstream files can compose auxiliary comparison chains into this owner theorem,
  so this file keeps no separate public bridge wrapper.

The positivity of `Δ k` needed for the logarithm is derived from `Δ (k + 1) > 0` and the direct
exponential estimate, so no separate positivity hypothesis for `Δ k` is kept as primitive data.
-/

/-- Lemma 2.27: if `Q_f > 1`, `κ > 0`, `Δ_{k+1} > 0`, and
`Δ_{k+1} ≤ (2 (Q_f - 1) / κ) * exp (-(j(k) - 1) / √Q_f) * Δ_k` for every `k ≤ N`, then the
stopping index `j(k)` is bounded above by
`1 + √Q_f log (2 (Q_f - 1) / κ) + √Q_f log (Δ_k / Δ_{k+1})` for every `k ≤ N`. -/
-- Proof sketch: multiply the one-step estimate by `exp ((j k - 1) / √Q_f)`, divide by the
-- positive factor `Δ (k + 1)`, take logarithms, split the resulting logarithm into the constant
-- and ratio terms, and rearrange the result to isolate `j k` on the left.
lemma stoppingIndex_le_one_add_sqrt_condition_log_ratio
    (Qf κ : ℝ) (N : ℕ) (j Δ : ℕ → ℝ)
    (hQf : 1 < Qf) (hκ : 0 < κ)
    (hΔ_succ_pos : ∀ ⦃k : ℕ⦄, k ≤ N → 0 < Δ (k + 1))
    (hΔ_succ_bound :
      ∀ ⦃k : ℕ⦄, k ≤ N →
        Δ (k + 1) ≤
          (2 * (Qf - 1) / κ) *
            Real.exp (-((j k - 1) / Real.sqrt Qf)) *
            Δ k)
    {k : ℕ} (hk : k ≤ N) :
    j k ≤
      1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / κ) +
        Real.sqrt Qf * Real.log (Δ k / Δ (k + 1)) := by
  let a : ℝ := (j k - 1) / Real.sqrt Qf
  let c : ℝ := 2 * (Qf - 1) / κ
  have hQf_pos : 0 < Qf := lt_trans zero_lt_one hQf
  have hQf_sub_pos : 0 < Qf - 1 := sub_pos.mpr hQf
  have hsqrt_pos : 0 < Real.sqrt Qf := Real.sqrt_pos.mpr hQf_pos
  have hconst_pos : 0 < c := by
    dsimp [c]
    exact div_pos (mul_pos two_pos hQf_sub_pos) hκ
  have hΔ_succ_pos' : 0 < Δ (k + 1) := hΔ_succ_pos hk
  have hfactor_pos : 0 < c * Real.exp (-a) := mul_pos hconst_pos (Real.exp_pos _)
  have hΔk_pos : 0 < Δ k := by
    have hbound_pos :
        0 < c * Real.exp (-a) * Δ k := by
      exact lt_of_lt_of_le hΔ_succ_pos' (by simpa [a, c] using hΔ_succ_bound hk)
    exact pos_of_mul_pos_right (by simpa [mul_assoc] using hbound_pos) hfactor_pos.le
  have hratio_pos : 0 < Δ k / Δ (k + 1) := div_pos hΔk_pos hΔ_succ_pos'
  have hmul :
      Real.exp a * Δ (k + 1) ≤ c * Δ k := by
    have hscaled :=
      mul_le_mul_of_nonneg_left
        (show Δ (k + 1) ≤ c * Real.exp (-a) * Δ k by
          simpa [a, c] using hΔ_succ_bound hk)
        (show 0 ≤ Real.exp a by positivity)
    calc
      Real.exp a * Δ (k + 1) ≤
          Real.exp a * (c * Real.exp (-a) * Δ k) := hscaled
      _ = c * Δ k := by
            rw [Real.exp_neg]
            field_simp [Real.exp_ne_zero a, hκ.ne']
  have hexp_le :
      Real.exp a ≤ c * (Δ k / Δ (k + 1)) := by
    have hdiv : Real.exp a ≤ (c * Δ k) / Δ (k + 1) := by
      exact (le_div_iff₀ hΔ_succ_pos').2 hmul
    calc
      Real.exp a ≤ (c * Δ k) / Δ (k + 1) := hdiv
      _ = c * (Δ k / Δ (k + 1)) := by ring
  have hcore :
      (j k - 1) / Real.sqrt Qf ≤
        Real.log c + Real.log (Δ k / Δ (k + 1)) := by
    have hlog :
        a ≤ Real.log (c * (Δ k / Δ (k + 1))) := by
      exact (Real.le_log_iff_exp_le (mul_pos hconst_pos hratio_pos)).2 hexp_le
    rw [Real.log_mul hconst_pos.ne' hratio_pos.ne'] at hlog
    simpa [a] using hlog
  have hscaled :
      j k - 1 ≤
        (Real.log c + Real.log (Δ k / Δ (k + 1))) * Real.sqrt Qf := by
    exact (div_le_iff₀ hsqrt_pos).1 (by simpa using hcore)
  have hfinal :
      j k ≤
        1 + (Real.log c + Real.log (Δ k / Δ (k + 1))) * Real.sqrt Qf := by
    linarith
  calc
    j k ≤
        1 + (Real.log c + Real.log (Δ k / Δ (k + 1))) * Real.sqrt Qf := hfinal
    _ = 1 + Real.sqrt Qf * Real.log c +
          Real.sqrt Qf * Real.log (Δ k / Δ (k + 1)) := by
            ring
    _ = 1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / κ) +
          Real.sqrt Qf * Real.log (Δ k / Δ (k + 1)) := by
            simp [c]

end
