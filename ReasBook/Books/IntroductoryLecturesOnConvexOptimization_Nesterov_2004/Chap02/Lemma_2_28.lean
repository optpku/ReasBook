/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_27

-- Declarations for this item will be appended below by the statement pipeline.

section

/-
Primary domain: scalar logarithmic stopping-index bounds coming from one-step exponential
comparisons.

Owner abstractions sampled before refining:
- `stoppingIndex_le_one_add_sqrt_condition_log_ratio` in `Lemma_2_27.lean`, the Chapter 2 owner
  theorem for one-step logarithmic stopping-index bounds;
- the accumulated-sum helper later used in `Proposition_2_33.lean`, which consumes the same
  one-step logarithmic bound termwise;
- `Real.log_mul` for the canonical combination of the constant logarithm
  `log (2 * (Qf - 1) / κ)` with the terminal ratio `log (ΔNext / ε)`;
- `Nat.cast_add` together with the standard cast arithmetic reducing the predecessor relation
  `jStar = jPrev + 1` to the owner exponent `((jStar : ℝ) - 1)`.

Best owner abstraction:
- the source-facing owner theorem
  `stoppingIndex_le_one_add_sqrt_condition_log_ratio`.

Source/core/bridge triage:
- source-facing: the textbook terminal stopping-index estimate of Lemma 2.28;
- core/canonical: `stoppingIndex_le_one_add_sqrt_condition_log_ratio`;
- bridge/view: the comparison chain through `previousInternalValue` and `objectiveGap`, which is
  kept only as proof input and not packaged as a parallel owner API.

Primitive data:
- the predecessor index `jPrev`, the terminal gap `ΔNext`, and the target accuracy `ε`;
- the source comparison data `previousInternalValue` and `objectiveGap`.

Derived API:
- the displayed logarithmic bound for `jStar`, obtained by deriving the one-step estimate on `ε`
  and then specializing the owner theorem to the single step `k = 0`.

The positivity of `ΔNext` needed for the terminal logarithm is derived from `ε > 0` and the
comparison chain `ε ≤ previousInternalValue ≤ ((Qf - 1) / κ) * objectiveGap ≤ ... * ΔNext`, so no
separate terminal-gap positivity hypothesis is kept as primitive data.
-/

/-- Lemma 2.28: if `Q_f > 1`, `κ > 0`, `ε > 0`, and if for the predecessor
index `j = j^* - 1` one has
`ε ≤ f^*(t_{N+1}; x_{N+1}, j; L) ≤ ((Q_f - 1) / κ) * (f(t_{N+1}; x_{N+1}, j) - f^*(t_{N+1}))`
and
`((Q_f - 1) / κ) * (f(t_{N+1}; x_{N+1}, j) - f^*(t_{N+1}))`
`≤ (2 * (Q_f - 1) / κ) * e^{-j / √Q_f} * Δ_{N+1}`,
then `j^* ≤ 1 + √Q_f * log (2 (Q_f - 1) Δ_{N+1} / (κ ε))`. -/
-- Proof sketch: specialize Lemma 2.27 to the one-step sequence with `Δ 0 = ΔNext` and
-- `Δ 1 = ε`. The assumed comparison chain gives the one-step estimate required by the owner
-- theorem from Lemma 2.27. The same chain forces `ΔNext > 0`, and then `Real.log_mul` combines
-- `log (2 * (Qf - 1) / κ)` with `log (ΔNext / ε)`.
lemma accuracyStoppingIndex_le_one_add_sqrt_condition_log_ratio
    (Qf κ ε ΔNext : ℝ) (jStar jPrev : ℕ)
    {previousInternalValue objectiveGap : ℝ}
    (hQf : 1 < Qf) (hκ : 0 < κ) (hε : 0 < ε)
    (hjStar : jStar = jPrev + 1)
    (hLower : ε ≤ previousInternalValue)
    (hMiddle : previousInternalValue ≤ ((Qf - 1) / κ) * objectiveGap)
    (hUpper :
      ((Qf - 1) / κ) * objectiveGap ≤
        (2 * (Qf - 1) / κ) * Real.exp (-((jPrev : ℝ) / Real.sqrt Qf)) * ΔNext) :
    (jStar : ℝ) ≤
      1 + Real.sqrt Qf * Real.log ((2 * (Qf - 1) * ΔNext) / (κ * ε)) := by
  let c : ℝ := 2 * (Qf - 1) / κ
  let j : ℕ → ℝ := fun _ ↦ jStar
  let Δ : ℕ → ℝ := fun k ↦ if k = 0 then ΔNext else ε
  have hΔ_pos : ∀ ⦃k : ℕ⦄, k ≤ 0 → 0 < Δ (k + 1) := by
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    simp [Δ, hε]
  have hjPrev : (jPrev : ℝ) = (jStar : ℝ) - 1 := by
    norm_num [hjStar]
  have hstep_bound :
      ε ≤
        c *
          Real.exp (-(((jStar : ℝ) - 1) / Real.sqrt Qf)) *
          ΔNext := by
    calc
      ε ≤ previousInternalValue := hLower
      _ ≤ ((Qf - 1) / κ) * objectiveGap := hMiddle
      _ ≤ c * Real.exp (-((jPrev : ℝ) / Real.sqrt Qf)) * ΔNext := by
            simpa [c] using hUpper
      _ = c * Real.exp (-(((jStar : ℝ) - 1) / Real.sqrt Qf)) * ΔNext := by
            rw [hjPrev]
  have hΔ_succ_bound :
      ∀ ⦃k : ℕ⦄, k ≤ 0 →
        Δ (k + 1) ≤
          c *
            Real.exp (-((j k - 1) / Real.sqrt Qf)) *
            Δ k := by
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    simpa [j, Δ] using hstep_bound
  have hbound :
      j 0 ≤
        1 + Real.sqrt Qf * Real.log c +
          Real.sqrt Qf * Real.log (Δ 0 / Δ (0 + 1)) :=
    stoppingIndex_le_one_add_sqrt_condition_log_ratio
      Qf κ 0 j Δ hQf hκ hΔ_pos hΔ_succ_bound (by simp)
  have hQf_sub_pos : 0 < Qf - 1 := sub_pos.mpr hQf
  have hconst_pos : 0 < c := by
    dsimp [c]
    exact div_pos (mul_pos (show (0 : ℝ) < 2 by norm_num) hQf_sub_pos) hκ
  have hterminal_pos :
      0 < c * Real.exp (-((jPrev : ℝ) / Real.sqrt Qf)) * ΔNext := by
    exact lt_of_lt_of_le hε <| le_trans hLower <| le_trans hMiddle hUpper
  have hterminal_factor_pos : 0 < c * Real.exp (-((jPrev : ℝ) / Real.sqrt Qf)) := by
    exact mul_pos hconst_pos (Real.exp_pos _)
  have hΔNext : 0 < ΔNext := by
    exact pos_of_mul_pos_right
      (by simpa [c, mul_assoc] using hterminal_pos)
      hterminal_factor_pos.le
  have hratio_pos : 0 < ΔNext / ε := div_pos hΔNext hε
  have hlog : Real.log c + Real.log (ΔNext / ε) =
        Real.log ((2 * (Qf - 1) * ΔNext) / (κ * ε)) := by
    calc
      Real.log c + Real.log (ΔNext / ε) =
          Real.log (c * (ΔNext / ε)) := by
            symm
            rw [Real.log_mul hconst_pos.ne' hratio_pos.ne']
      _ = Real.log ((2 * (Qf - 1) * ΔNext) / (κ * ε)) := by
            congr 1
            dsimp [c]
            field_simp [hκ.ne', hε.ne']
  calc
    (jStar : ℝ) ≤
        1 + Real.sqrt Qf * Real.log c +
          Real.sqrt Qf * Real.log (ΔNext / ε) := by
            simpa [c, j, Δ] using hbound
    _ = 1 + Real.sqrt Qf * (Real.log c + Real.log (ΔNext / ε)) := by
          ring
    _ = 1 + Real.sqrt Qf * Real.log ((2 * (Qf - 1) * ΔNext) / (κ * ε)) := by
          rw [hlog]

end
