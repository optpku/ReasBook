/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

section

/- Primary domain: scalar logarithmic bounds for accumulated internal iteration counts.

Owner abstractions sampled before refining:
* project `accuracyStoppingIndex_le_one_add_sqrt_condition_log_ratio` in `Lemma_2_28.lean`, the
  one-step logarithmic owner bound used immediately downstream with the same log-ratio term;
* mathlib `Real.log_div`, the canonical logarithm identity turning ratios into additive
  telescoping terms;
* mathlib `Finset.sum_range_sub'`, the canonical telescoping-sum owner on `Finset.range`;
* mathlib `Finset.sum_le_sum`, the canonical accumulation of termwise upper bounds.

Best owner abstraction:
* source-facing/core: `sum_le_of_log_ratio_step_bounds`

Primitive data:
* the positive stage sequence `Δ`;
* the internal-cost sequence `j`;
* the one-step logarithmic upper bound on each `j k`.

Derived API:
* the helper telescoping identity `sum_range_log_div_eq_log_div`;
* the accumulated logarithmic estimate `sum_le_of_log_ratio_step_bounds`.

Source/core/bridge triage:
* source-facing: Proposition 2.32, the accumulated bound for `∑_{k=0}^N j(k)`;
* core/canonical: `sum_le_of_log_ratio_step_bounds`;
* bridge/view: the helper telescoping lemma `sum_range_log_div_eq_log_div`.
-/

/-- Helper for Proposition 2.32: positive consecutive ratios telescope after taking logarithms. -/
theorem sum_range_log_div_eq_log_div
    (N : ℕ) (Δ : ℕ → ℝ) (hΔ_pos : ∀ k ≤ N + 1, 0 < Δ k) :
    Finset.sum (Finset.range (N + 1)) (fun k ↦ Real.log (Δ k / Δ (k + 1))) =
      Real.log (Δ 0 / Δ (N + 1)) := by
  calc
    Finset.sum (Finset.range (N + 1)) (fun k ↦ Real.log (Δ k / Δ (k + 1))) =
        Finset.sum (Finset.range (N + 1)) (fun k ↦ Real.log (Δ k) - Real.log (Δ (k + 1))) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simpa using
            (Real.log_div
              (hΔ_pos k (Nat.le_trans (Nat.le_of_lt_succ <| Finset.mem_range.mp hk) <|
                Nat.le_succ N)).ne'
              (hΔ_pos (k + 1) (Nat.succ_le_succ <| Nat.le_of_lt_succ <|
                Finset.mem_range.mp hk)).ne')
    _ = Real.log (Δ 0) - Real.log (Δ (N + 1)) := by
          simpa using Finset.sum_range_sub' (fun k ↦ Real.log (Δ k)) (N + 1)
    _ = Real.log (Δ 0 / Δ (N + 1)) := by
          symm
          simpa using
            (Real.log_div (hΔ_pos 0 <| Nat.zero_le (N + 1)).ne' (hΔ_pos (N + 1) <|
              Nat.le_refl _).ne')

/-- Proposition 2.32: if each internal cost `j(k)` satisfies the one-step logarithmic bound
`j(k) ≤ 1 + √Q_f log (2 (L - μ) / (κ μ)) + √Q_f log (Δ_k / Δ_{k+1})`, then summing from
`k = 0` to `N` yields
`∑_{k=0}^N j(k) ≤ (N + 1) * (1 + √Q_f log (2 (L - μ) / (κ μ))) + √Q_f log (Δ_0 / Δ_{N+1})`. -/
theorem sum_le_of_log_ratio_step_bounds
    (N : ℕ) (j Δ : ℕ → ℝ) (Qf L μ κ : ℝ)
    (hΔ_pos : ∀ k ≤ N + 1, 0 < Δ k)
    (hj_bound : ∀ k ≤ N,
      j k ≤ 1 + Real.sqrt Qf * Real.log (2 * (L - μ) / (κ * μ)) +
        Real.sqrt Qf * Real.log (Δ k / Δ (k + 1))) :
    Finset.sum (Finset.range (N + 1)) j ≤
      (N + 1 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (L - μ) / (κ * μ))) +
        Real.sqrt Qf * Real.log (Δ 0 / Δ (N + 1)) := by
  let c : ℝ := 1 + Real.sqrt Qf * Real.log (2 * (L - μ) / (κ * μ))
  calc
    Finset.sum (Finset.range (N + 1)) j ≤
        Finset.sum (Finset.range (N + 1))
          (fun k ↦ c + Real.sqrt Qf * Real.log (Δ k / Δ (k + 1))) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            exact hj_bound k <| Nat.le_of_lt_succ <| Finset.mem_range.mp hk
    _ = Finset.sum (Finset.range (N + 1)) (fun _ ↦ c) +
          Finset.sum (Finset.range (N + 1))
            (fun k ↦ Real.sqrt Qf * Real.log (Δ k / Δ (k + 1))) := by
            rw [Finset.sum_add_distrib]
    _ = (N + 1 : ℝ) * c +
          Finset.sum (Finset.range (N + 1))
            (fun k ↦ Real.sqrt Qf * Real.log (Δ k / Δ (k + 1))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            simp
    _ = (N + 1 : ℝ) * c +
          Real.sqrt Qf *
            Finset.sum (Finset.range (N + 1)) (fun k ↦ Real.log (Δ k / Δ (k + 1))) := by
            rw [← Finset.mul_sum]
    _ = (N + 1 : ℝ) * c + Real.sqrt Qf * Real.log (Δ 0 / Δ (N + 1)) := by
            rw [sum_range_log_div_eq_log_div N Δ hΔ_pos]
    _ = (N + 1 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (L - μ) / (κ * μ))) +
          Real.sqrt Qf * Real.log (Δ 0 / Δ (N + 1)) := by
            simp [c]

end
