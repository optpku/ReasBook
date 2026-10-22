/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_6_9

-- Declarations for this item will be appended below by the statement pipeline.

variable {r : ℕ → ℝ}

/- Primary domain: scalar convergence rates.

Source/core/bridge triage for Definition 1.2.5:
* source-facing: the power-law sublinear statement
  `∃ c > 0, ∃ p > 0, ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.rpow (k : ℝ) p`
* core/canonical: under optimization-error-sequence hypotheses, the later eventual-bound owner
  `HasConvergenceRateOfOrder`
* bridge/view: the concrete square-root estimate `r k ≤ c / Real.sqrt (k : ℝ)` and the resulting
  specialization `HasConvergenceRateOfOrder r (fun N ↦ 1 / Real.sqrt (N : ℝ))`

Relevant declarations sampled before refining:
* `HasGeometricRateOfConvergence` in `Definition_1_2_6.lean`, the neighboring source-facing
  rate predicate in the same chapter
* `HasConvergenceRateOfOrder` in `Definition_1_6_9.lean`, the later source-facing eventual-bound
  owner organized around `IsOptimizationErrorSequence`
* the direct square-root specialization
  `HasConvergenceRateOfOrder r (fun N ↦ 1 / Real.sqrt (N : ℝ))` in
  `Definition_1_6_9.lean`

Primitive data:
* the sequence `r`
* witnesses `c > 0` and `p > 0`
* the positive-index estimate `r k ≤ c / Real.rpow (k : ℝ) p`

Derived API:
* the source-facing recalled statement itself
* the square-root special case
* the bridge from a square-root bound plus `IsOptimizationErrorSequence` to the eventual-bound
  owner `HasConvergenceRateOfOrder r (fun N ↦ 1 / Real.sqrt (N : ℝ))`
* the explicit `(c / ε)^2` complexity threshold for the square-root example -/

/- Definition 1.2.5 is the source-facing existential statement

`∃ c > 0, ∃ p > 0, ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.rpow (k : ℝ) p`.

Unlike Definitions 1.2.6 and 1.2.7, this file has no reused fixed-parameter owner elsewhere in
the chapter. The previous alias `HasSublinearRateOfConvergence` therefore added no owner-level
mathematics and only duplicated the source statement. The numbered item is now recalled directly,
while the square-root specialization and later-rate bridge remain as the actual reusable API. -/
#check (∃ c > 0, ∃ p > 0, ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.rpow (k : ℝ) p)

private theorem div_sqrt_le_max_div_sqrt (c : ℝ) (k : ℕ) :
    c / Real.sqrt (k : ℝ) ≤ max c 1 / Real.sqrt (k : ℝ) :=
  div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)

/-- A square-root decay bound yields the source-facing power-law estimate from Definition 1.2.5. -/
theorem exists_power_law_bound_of_sqrt_bound
    {c : ℝ}
    (h : ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.sqrt (k : ℝ)) :
    ∃ C > 0, ∃ p > 0, ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ C / Real.rpow (k : ℝ) p := by
  refine ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), (1 / 2 : ℝ), by positivity, ?_⟩
  intro k hk
  refine (h hk).trans ?_
  simpa [Real.sqrt_eq_rpow] using div_sqrt_le_max_div_sqrt c k

namespace IsOptimizationErrorSequence

variable {r : ℕ → ℝ} {c : ℝ}

/-- Under the optimization-error-sequence hypotheses from Definition 1.6.9, a pointwise
`1 / sqrt N` estimate yields the later source-facing eventual-bound owner
`HasConvergenceRateOfOrder r (fun N ↦ 1 / Real.sqrt (N : ℝ))`. -/
theorem hasConvergenceRateOfOrder_of_sqrt_bound
    (hr : IsOptimizationErrorSequence r)
    (h : ∀ ⦃N : ℕ⦄, 0 < N → r N ≤ c / Real.sqrt (N : ℝ)) :
    HasConvergenceRateOfOrder r (fun N : ℕ ↦ 1 / Real.sqrt (N : ℝ)) := by
  refine ⟨hr, max c 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  refine Filter.eventually_atTop.2 ⟨1, fun N hN ↦ ?_⟩
  have hN_pos : 0 < N := Nat.succ_le_iff.mp hN
  refine (h hN_pos).trans ?_
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    div_sqrt_le_max_div_sqrt c N

end IsOptimizationErrorSequence

/-- A `1 / sqrt k` convergence estimate yields the complexity threshold `(c / ε)^2`. -/
theorem sqrt_rate_complexity_bound
    {r : ℕ → ℝ} {c ε : ℝ}
    (h : ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.sqrt (k : ℝ))
    (hε : 0 < ε)
    {k : ℕ} (hk : 0 < k)
    (hkComplexity : (c / ε) ^ (2 : ℕ) ≤ (k : ℝ)) :
    r k ≤ ε := by
  have hk_real : 0 < (k : ℝ) := by
    exact_mod_cast hk
  have hsqrt_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk_real
  refine (h hk).trans ?_
  by_cases hc : c ≤ 0
  · have hnonpos : c / Real.sqrt (k : ℝ) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hc (Real.sqrt_nonneg _)
    exact hnonpos.trans hε.le
  · have hle_sqrt : c / ε ≤ Real.sqrt (k : ℝ) := by
      have hc_pos : 0 < c := lt_of_not_ge hc
      have hdiv_nonneg : 0 ≤ c / ε := by
        positivity
      have hsq : (c / ε) ^ (2 : ℕ) ≤ (Real.sqrt (k : ℝ)) ^ (2 : ℕ) := by
        simpa [Real.sq_sqrt hk_real.le] using hkComplexity
      exact
        (sq_le_sq₀ hdiv_nonneg (by positivity : 0 ≤ Real.sqrt (k : ℝ))).1 hsq
    exact (div_le_iff₀ hsqrt_pos).2 <| by
      simpa [mul_comm] using (div_le_iff₀ hε).1 hle_sqrt
