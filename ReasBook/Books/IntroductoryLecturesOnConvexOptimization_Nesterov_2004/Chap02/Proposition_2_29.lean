/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-
Primary domain: scalar geometric-decay thresholds for the residual sequence `n ↦ tStar - t n`.

Owner-style declarations sampled before refining:
* `HasGeometricRateOfConvergence` in `Chap01/Definition_1_2_6.lean`
* `HasGeometricRateOfConvergence.of_step_bound` in `Chap01/Definition_1_2_6.lean`
* `HasGeometricRateOfConvergence.le_target_of_iterationThreshold_le` and
  `HasGeometricRateOfConvergence.iterationThreshold` in `Chap01/Definition_1_2_6.lean`
* `constrainedMinimizationInternalGap_hasGeometricRateOfConvergence` in
  `Chap02/Proposition_2_30.lean`

Best owner abstraction:
* `HasGeometricRateOfConvergence` for the residual sequence `n ↦ tStar - t n`

Primitive data:
* the scalar sequence `t`
* the limit value `tStar`
* the one-step contraction inequality on the residuals

Derived API:
* the owner geometric-rate statement for `n ↦ tStar - t n`
* the owner exact logarithmic-threshold consequences
* the source-facing specialization to Proposition 2.29

Source/core/bridge triage:
* source-facing: Proposition 2.29 and its nat-ceil corollary
* core/canonical: `HasGeometricRateOfConvergence`
* bridge/view: the recurrence-to-owner theorem
  `residual_hasGeometricRateOfConvergence`

The recurrence-to-owner bridge stays local. The public proposition specializes the canonical owner
theorem `HasGeometricRateOfConvergence.le_target_of_iterationThreshold_le` to the residual
sequence and the exact base-`2 * (1 - κ)` threshold from the text.
-/

open HasGeometricRateOfConvergence

section

variable {κ tStar : ℝ} {t : ℕ → ℝ}

local notation "base" => 2 * (1 - κ)
local notation "residual" => fun n : ℕ ↦ tStar - t n

/-- Helper for Proposition 2.29: the one-step residual contraction is exactly the owner
geometric-rate statement for the residual sequence. -/
theorem residual_hasGeometricRateOfConvergence
    (hκ_contract : 1 < 2 * (1 - κ))
    (hstep : ∀ n : ℕ, residual (n + 1) ≤ residual n / (2 * (1 - κ))) :
    HasGeometricRateOfConvergence residual (1 - (2 * (1 - κ))⁻¹) (residual 0) := by
  -- The contraction hypothesis gives the nonnegativity needed to place the owner parameter in
  -- the admissible interval `(-∞, 1]`.
  have hfactor_nonneg : 0 ≤ (2 * (1 - κ))⁻¹ := by
    have hfactor_pos : 0 < 2 * (1 - κ) := lt_trans zero_lt_one hκ_contract
    exact inv_nonneg.mpr hfactor_pos.le
  have hq₁ : 1 - (2 * (1 - κ))⁻¹ ≤ 1 := by
    simpa using sub_le_self (1 : ℝ) hfactor_nonneg
  -- Rewrite the textbook division step as the owner multiplicative step `(1 - q) * residual n`.
  refine of_step_bound hq₁ le_rfl ?_
  intro n
  calc
    residual (n + 1) ≤ residual n / (2 * (1 - κ)) := hstep n
    _ = residual n * (2 * (1 - κ))⁻¹ := by rw [div_eq_mul_inv]
    _ = (1 - (1 - (2 * (1 - κ))⁻¹)) * residual n := by ring

/-- Helper for Proposition 2.29: the textbook contraction base `2 * (1 - κ)` is the reciprocal
owner base `(1 - q)⁻¹` attached to `q = 1 - (2 * (1 - κ))⁻¹`. -/
private theorem owner_contract
    (hκ_contract : 1 < 2 * (1 - κ)) :
    1 < (1 - (1 - base⁻¹))⁻¹ := by
  have hbase_pos : 0 < base := lt_trans zero_lt_one hκ_contract
  have hbase_ne : base ≠ 0 := ne_of_gt hbase_pos
  simpa [hbase_ne] using hκ_contract

/-- Helper for Proposition 2.29: the owner iteration threshold simplifies to the textbook
logarithmic expression `N(ε)`. -/
private theorem residual_iterationThreshold_eq_textbook
    {ε : ℝ} :
    iterationThreshold (1 - (2 * (1 - κ))⁻¹) (tStar - t 0) ((1 - κ) * ε) =
      Real.log ((tStar - t 0) / ((1 - κ) * ε)) / Real.log (2 * (1 - κ)) := by
  -- Expand the owner threshold and normalize the logarithm base.
  rw [iterationThreshold, Real.logb]
  simp

/-- Proposition 2.29: if the residual sequence satisfies
`t^* - t_{n + 1} ≤ (t^* - t_n) / (2 (1 - κ))` at every step and `1 < 2 * (1 - κ)`, then every
iterate index `n ≥ N(ε)` satisfies `t^* - t_n ≤ (1 - κ) ε`, where `N(ε)` is the explicit
logarithmic threshold from the proposition. -/
-- Proof sketch: the recurrence defines an owner geometric-rate bound on the residual sequence
-- `n ↦ tStar - t n`; evaluating that bound at the iterate `n` gives
-- `tStar - t n ≤ (tStar - t 0) * ((2 * (1 - κ))⁻¹)^n`. Solve the resulting scalar inequality
-- by taking logarithms under the contraction hypothesis `1 < 2 * (1 - κ)`. The textbook side
-- assumptions `0 < κ < 1` and the residual-positivity guards are redundant for this scalar
-- consequence, so the public Lean theorem keeps only the sharper contraction hypothesis together
-- with the actual one-step contraction inequality.
theorem constrainedMinimization_error_le_target_of_iterationThreshold_le
    {ε : ℝ} (hκ_contract : 1 < 2 * (1 - κ)) (hε : 0 < ε)
    (hstep :
      ∀ n : ℕ, tStar - t (n + 1) ≤ (tStar - t n) / (2 * (1 - κ)))
    {n : ℕ}
    (hn :
      Real.log ((tStar - t 0) / ((1 - κ) * ε)) / Real.log (2 * (1 - κ)) ≤ (n : ℝ)) :
    tStar - t n ≤ (1 - κ) * ε := by
  have hresidual := residual_hasGeometricRateOfConvergence hκ_contract hstep
  have htarget_pos : 0 < (1 - κ) * ε := by
    have hone_sub_kappa_pos : 0 < 1 - κ := by
      nlinarith
    positivity
  have howner_threshold :
      iterationThreshold (1 - (2 * (1 - κ))⁻¹) (residual 0) ((1 - κ) * ε) ≤ (n : ℝ) := by
    change iterationThreshold (1 - (2 * (1 - κ))⁻¹) (tStar - t 0) ((1 - κ) * ε) ≤ (n : ℝ)
    rw [residual_iterationThreshold_eq_textbook]
    exact hn
  change residual n ≤ (1 - κ) * ε
  exact
    le_target_of_iterationThreshold_le hresidual (owner_contract hκ_contract) htarget_pos
      howner_threshold

/-- The ceiling of the logarithmic threshold gives an upper bound on the number of full
iterations required to reach the target error level `(1 - κ) ε`. -/
-- Proof sketch: apply
-- `constrainedMinimization_error_le_target_of_iterationThreshold_le` at the iterate index
-- `⌈log ((t^* - t_0) / ((1 - κ) ε)) / log (2 * (1 - κ))⌉₊`, or equivalently the owner threshold
-- `⌈iterationThreshold (1 - (2 * (1 - κ))⁻¹) (tStar - t 0) ((1 - κ) * ε)⌉₊`.
theorem constrainedMinimization_error_le_target_at_natCeil_iterationThreshold
    {ε : ℝ} (hκ_contract : 1 < 2 * (1 - κ)) (hε : 0 < ε)
    (hstep :
      ∀ n : ℕ, tStar - t (n + 1) ≤ (tStar - t n) / (2 * (1 - κ))) :
    tStar -
        t ⌈Real.log ((tStar - t 0) / ((1 - κ) * ε)) / Real.log (2 * (1 - κ))⌉₊ ≤
      (1 - κ) * ε := by
  have hresidual := residual_hasGeometricRateOfConvergence hκ_contract hstep
  have htarget_pos : 0 < (1 - κ) * ε := by
    have hone_sub_kappa_pos : 0 < 1 - κ := by
      nlinarith
    positivity
  have hnatCeil :
      residual ⌈iterationThreshold (1 - (2 * (1 - κ))⁻¹) (tStar - t 0) ((1 - κ) * ε)⌉₊ ≤
        (1 - κ) * ε := by
    simpa using
      le_target_at_natCeil_iterationThreshold hresidual (owner_contract hκ_contract) htarget_pos
  change
    residual ⌈Real.log ((tStar - t 0) / ((1 - κ) * ε)) / Real.log (2 * (1 - κ))⌉₊ ≤
      (1 - κ) * ε
  rw [residual_iterationThreshold_eq_textbook]
    at hnatCeil
  exact hnatCeil

end

end
