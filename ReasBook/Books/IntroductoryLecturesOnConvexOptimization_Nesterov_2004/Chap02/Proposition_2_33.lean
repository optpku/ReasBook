/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_32

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

/- Primary domain: scalar logarithmic complexity bounds for total internal costs in Chapter 2.

Owner abstractions sampled before refining:
- `sum_le_of_log_ratio_step_bounds` in `Proposition_2_32.lean`, the Chapter 2 owner for
  the accumulated internal cost `∑_{k=0}^N j(k)`;
- `accuracyStoppingIndex_le_one_add_sqrt_condition_log_ratio` in `Lemma_2_28.lean`, the Chapter 2
  owner bound for the terminal stopping index `j^*`;
- `Real.log_mul` for the canonical recombination of the intermediate logarithms
  `log (Δ₀ / Δ_{N+1})` and `log (Δ_{N+1} / ε)`.

Best owner abstraction:
- the source-facing owner theorem
  `constrainedMinimization_totalIterationCount_le_logarithmic_bound`, obtained by combining the
  Chapter 2 accumulated-cost owner theorem `sum_le_of_log_ratio_step_bounds` with the
  terminal logarithmic bound.

Source/core/bridge triage:
- source-facing: Proposition 2.33 itself, which packages the total internal iteration count on the
  positive domain `x ∈ (0, 2 * (Q_f - 1))`, `ε > 0`, and positive `Δ₀, …, Δ_{N+1}`;
- core/canonical: the Chapter 2 accumulated-cost owner
  `sum_le_of_log_ratio_step_bounds`;
- bridge/view: the private recombination lemma
  `combine_terminal_and_accumulated_log_bounds`.

Primitive data:
- the cost sequence `j`, the terminal contribution `jStar`, and the positive stage sequence `Δ`;
- the source-domain parameters `Qf`, `x`, and `ε`.

Derived API:
- the final total logarithmic estimate after recombining the endpoint ratios.
-/

/-- Helper for Proposition 2.33: combine the scalar terminal bound for `jStar` with the scalar
accumulated bound for `∑_{k=0}^N j(k)` after splitting and recombining the endpoint logarithms. -/
private theorem combine_terminal_and_accumulated_log_bounds
    (N : ℕ) (jStar accumulatedCost Δfinal Δ0 Qf x ε : ℝ)
    (hconst_pos : 0 < 2 * (Qf - 1) / x)
    (hΔ0 : 0 < Δ0) (hΔfinal : 0 < Δfinal) (hε : 0 < ε)
    (hjStar_bound :
      jStar ≤
        1 + Real.sqrt Qf * Real.log ((2 * (Qf - 1) * Δfinal) / (x * ε)))
    (hsum_bound :
      accumulatedCost ≤
        (N + 1 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x)) +
          Real.sqrt Qf * Real.log (Δ0 / Δfinal)) :
    jStar + accumulatedCost ≤
      (N + 2 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x)) +
        Real.sqrt Qf * Real.log (Δ0 / ε) := by
  let c : ℝ := 1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x)
  have hx_ne : x ≠ 0 := by
    intro hx
    simp [hx] at hconst_pos
  have hinitial_ratio_pos : 0 < Δ0 / Δfinal := div_pos hΔ0 hΔfinal
  have hterminal_ratio_pos : 0 < Δfinal / ε := div_pos hΔfinal hε
  -- Split the terminal logarithm into the common constant part and the final endpoint ratio.
  have hlog_jStar :
      Real.log ((2 * (Qf - 1) * Δfinal) / (x * ε)) =
        Real.log (2 * (Qf - 1) / x) + Real.log (Δfinal / ε) := by
    calc
      Real.log ((2 * (Qf - 1) * Δfinal) / (x * ε)) =
          Real.log ((2 * (Qf - 1) / x) * (Δfinal / ε)) := by
            congr 1
            field_simp [hx_ne, hε.ne']
      _ = Real.log (2 * (Qf - 1) / x) + Real.log (Δfinal / ε) := by
            rw [Real.log_mul hconst_pos.ne' hterminal_ratio_pos.ne']
  -- Recombine the initial and terminal endpoint ratios into the public `Δ 0 / ε` quantity.
  have hlog_total :
      Real.log (Δ0 / Δfinal) + Real.log (Δfinal / ε) =
        Real.log (Δ0 / ε) := by
    calc
      Real.log (Δ0 / Δfinal) + Real.log (Δfinal / ε) =
          Real.log ((Δ0 / Δfinal) * (Δfinal / ε)) := by
            symm
            rw [Real.log_mul hinitial_ratio_pos.ne' hterminal_ratio_pos.ne']
      _ = Real.log (Δ0 / ε) := by
            congr 1
            field_simp [hΔfinal.ne', hε.ne']
  have hjStar_bound' :
      jStar ≤ c + Real.sqrt Qf * Real.log (Δfinal / ε) := by
    calc
      jStar ≤
          1 +
            Real.sqrt Qf *
              (Real.log (2 * (Qf - 1) / x) + Real.log (Δfinal / ε)) := by
                simpa [hlog_jStar] using hjStar_bound
      _ = c + Real.sqrt Qf * Real.log (Δfinal / ε) := by
            simp [c]
            ring
  calc
    jStar + accumulatedCost ≤
        (c + Real.sqrt Qf * Real.log (Δfinal / ε)) +
          ((N + 1 : ℝ) * c + Real.sqrt Qf * Real.log (Δ0 / Δfinal)) := by
            exact add_le_add hjStar_bound' (by simpa [c] using hsum_bound)
    _ = (N + 2 : ℝ) * c +
          (Real.sqrt Qf * Real.log (Δ0 / Δfinal) +
            Real.sqrt Qf * Real.log (Δfinal / ε)) := by
          ring
    _ = (N + 2 : ℝ) * c +
          Real.sqrt Qf *
            (Real.log (Δ0 / Δfinal) + Real.log (Δfinal / ε)) := by
          ring
    _ = (N + 2 : ℝ) * c + Real.sqrt Qf * Real.log (Δ0 / ε) := by
          rw [hlog_total]
    _ = (N + 2 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x)) +
          Real.sqrt Qf * Real.log (Δ0 / ε) := by
          simp [c]

/-- Proposition 2.33: if `x ∈ (0, 2 * (Q_f - 1))` (so in particular `Q_f > 1`), `ε > 0`, the
stage values `Δ₀, …, Δ_{N+1}` are positive, the terminal index `j^*` satisfies the Lemma 2.28
bound with `Δ_{N+1}`, and each internal cost `j(k)` satisfies the Proposition 2.32 hypothesis,
then the total internal iteration count is bounded by
`(N + 2) * (1 + √Q_f * log (2 (Q_f - 1) / x)) + √Q_f * log (Δ₀ / ε)`. -/
-- Proof sketch: first specialize `sum_le_of_log_ratio_step_bounds` with `L = Q_f`,
-- `μ = 1`, and `κ = x` to obtain the accumulated bound for `∑_{k=0}^N j(k)`.
-- Then combine that estimate with the assumed terminal bound for `j^*` and use `Real.log_mul`
-- to eliminate the intermediate quantity `Δ_{N+1}` from the final logarithm.
theorem constrainedMinimization_totalIterationCount_le_logarithmic_bound
    (N : ℕ) (j : ℕ → ℝ) (jStar : ℝ) (Δ : ℕ → ℝ) (Qf x ε : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) (2 * (Qf - 1)))
    (hε : 0 < ε)
    (hΔ_pos : ∀ ⦃k : ℕ⦄, k ≤ N + 1 → 0 < Δ k)
    (hjStar_bound :
      jStar ≤
        1 + Real.sqrt Qf * Real.log ((2 * (Qf - 1) * Δ (N + 1)) / (x * ε)))
    (hj_bound :
      ∀ ⦃k : ℕ⦄, k ≤ N →
        j k ≤
          1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x) +
            Real.sqrt Qf * Real.log (Δ k / Δ (k + 1))) :
    jStar + Finset.sum (Finset.range (N + 1)) j ≤
      (N + 2 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x)) +
        Real.sqrt Qf * Real.log (Δ 0 / ε) := by
  have hsum_bound :
      Finset.sum (Finset.range (N + 1)) j ≤
        (N + 1 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x)) +
          Real.sqrt Qf * Real.log (Δ 0 / Δ (N + 1)) := by
    have hΔ_pos' : ∀ k ≤ N + 1, 0 < Δ k := fun k hk ↦ hΔ_pos hk
    have hj_bound' :
        ∀ k ≤ N,
          j k ≤
            1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / (x * 1)) +
              Real.sqrt Qf * Real.log (Δ k / Δ (k + 1)) := by
      intro k hk
      simpa [mul_one] using hj_bound hk
    simpa [mul_one] using sum_le_of_log_ratio_step_bounds N j Δ Qf Qf 1 x hΔ_pos' hj_bound'
  -- The interval hypothesis provides the positive logarithm domain needed by the helper theorem.
  have hQf_sub_pos : 0 < Qf - 1 := by
    nlinarith [hx.1, hx.2]
  have hconst_pos : 0 < 2 * (Qf - 1) / x := by
    exact div_pos (mul_pos two_pos hQf_sub_pos) hx.1
  have hDelta0 : 0 < Δ 0 := by
    exact hΔ_pos (show 0 ≤ N + 1 by simp)
  have hdeltaFinal : 0 < Δ (N + 1) := by
    exact hΔ_pos (Nat.le_refl _)
  -- Finish by combining the accumulated sum estimate with the assumed terminal bound.
  exact
    combine_terminal_and_accumulated_log_bounds
      N jStar (Finset.sum (Finset.range (N + 1)) j) (Δ (N + 1)) (Δ 0) Qf x ε
      hconst_pos hDelta0 hdeltaFinal hε hjStar_bound hsum_bound
