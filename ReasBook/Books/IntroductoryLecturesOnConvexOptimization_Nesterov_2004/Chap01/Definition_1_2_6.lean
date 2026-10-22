/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open Asymptotics Filter

/-
Primary domain: scalar convergence rates for real sequences.

Source/core/bridge triage:
* source-facing condition
  `∃ c > 0, ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ HasGeometricRateOfConvergence r q c`
* core owner for this scalar notion `HasGeometricRateOfConvergence`
* bridge/view: the canonical asymptotic estimate
  `HasGeometricRateOfConvergence.isBigO : r =O[atTop] (fun k ↦ (1 - q)^k)` under
  nonnegativity hypotheses, and then the later owner `HasConvergenceRateOfOrder` from
  `Definition_1_6_9.lean`, which additionally packages optimization-error-sequence data

Relevant declarations sampled before refining:
* `IsBigO.of_bound` in mathlib, the canonical asymptotic owner constructor for a pointwise norm
  bound
* `HasConvergenceRateOfOrder` in `Definition_1_6_9.lean`, the later project owner built from
  `IsOptimizationErrorSequence` and `=O[atTop]`
* `linear_iteration_contraction_estimate` in `Proposition_1_6_13.lean`
* `constrainedMinimizationInternalGap_hasGeometricRateOfConvergence` in
  `Chap02/Proposition_2_30.lean`
* `tendsto_pow_atTop_nhds_zero_of_lt_one` in mathlib for the geometric-to-zero consequence

Primitive data:
* the sequence `r`
* the constants `q` and `c`
* the global pointwise bound `r k ≤ c * (1 - q)^k`

Derived API:
* the source-facing linear-rate existence statement
* the asymptotic bridge to `=O[atTop]`
* the exponential bound, convergence-to-zero consequence, and complexity threshold
-/

/-- A rate of convergence controlled by a geometric factor in the iteration counter. -/
def HasGeometricRateOfConvergence (r : ℕ → ℝ) (q c : ℝ) : Prop :=
  ∀ k : ℕ, r k ≤ c * (1 - q) ^ k

variable {r : ℕ → ℝ}

/- Definition 1.2.6 is the source-facing existence statement

`∃ c > 0, ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ HasGeometricRateOfConvergence r q c`.

The owner abstraction is `HasGeometricRateOfConvergence`; the numbered item only restricts the
admissible witnesses `c` and `q`. -/
#check (∃ c > 0, ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ HasGeometricRateOfConvergence r q c)

namespace HasGeometricRateOfConvergence

variable {q c : ℝ}

/-- A one-step contraction estimate with factor `1 - q` and initial bound `c` yields the
corresponding geometric-rate owner statement. -/
theorem of_step_bound
    (hq₁ : q ≤ 1)
    (h0 : r 0 ≤ c)
    (hstep : ∀ k : ℕ, r (k + 1) ≤ (1 - q) * r k) :
    HasGeometricRateOfConvergence r q c := by
  intro k
  induction k with
  | zero =>
      simpa using h0
  | succ k ih =>
      calc
        r (k + 1) ≤ (1 - q) * r k := hstep k
        _ ≤ (1 - q) * (c * (1 - q) ^ k) := by
          gcongr
        _ = c * (1 - q) ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- A nonnegative geometric-rate bound gives the canonical asymptotic estimate
`r =O[atTop] (fun k ↦ (1 - q)^k)`. -/
theorem isBigO
    (h : HasGeometricRateOfConvergence r q c)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
    (hc : 0 ≤ c) :
    r =O[atTop] (fun k : ℕ ↦ (1 - q) ^ k) := by
  refine IsBigO.of_bound c <| Filter.Eventually.of_forall fun k ↦ ?_
  calc
    ‖r k‖ = r k := by simp [Real.norm_eq_abs, abs_of_nonneg (hr_nonneg k)]
    _ ≤ c * (1 - q) ^ k := h k
    _ ≤ c * ‖(1 - q) ^ k‖ := by
      exact mul_le_mul_of_nonneg_left (le_abs_self ((1 - q) ^ k)) hc

/-- Helper for Definition 1.2.6: the geometric factor `(1 - q)^k` is dominated by the exponential
majorant `exp (-q k)` when `q ≤ 1`. -/
lemma geometric_factor_le_exp_neg_mul_nat
    (hq₁ : q ≤ 1) (k : ℕ) :
    (1 - q) ^ k ≤ Real.exp (-(q * (k : ℝ))) := by
  -- Reduce the comparison to the standard estimate `(1 - t / n)^n ≤ exp (-t)`.
  cases k with
  | zero =>
      simp
  | succ k =>
      have haux : q * ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        nlinarith
      have hbase :=
        Real.one_sub_div_pow_le_exp_neg (n := k + 1) (t := q * ((k + 1 : ℕ) : ℝ)) haux
      have hdiv : q * ((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ)) = q := by
        field_simp
      -- Rewrite the normalized factor back to the original contraction parameter `q`.
      calc
        (1 - q) ^ (k + 1) =
            (1 - q * ((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ))) ^ (k + 1) := by
          rw [hdiv]
        _ ≤ Real.exp (-(q * ((k + 1 : ℕ) : ℝ))) := hbase

/-- A geometric decay estimate with nonnegative constant `c` and `0 < q ≤ 1` is bounded above by
the corresponding exponential estimate `c * exp (-q k)`. -/
-- Proof sketch: combine the pointwise geometric bound with the standard inequality
-- `(1 - q)^k ≤ exp (-q k)` valid for `0 < q ≤ 1`, then multiply by the nonnegative constant `c`.
theorem exp_bound
    (h : HasGeometricRateOfConvergence r q c)
    (hc : 0 ≤ c)
    (hq₀ : 0 < q) (hq₁ : q ≤ 1)
    (k : ℕ) :
    r k ≤ c * Real.exp (-(q * (k : ℝ))) := by
  have hq_nonneg : 0 ≤ q := hq₀.le
  -- First use the geometric owner bound, then replace the geometric factor by the exponential one.
  calc
    r k ≤ c * (1 - q) ^ k := h k
    _ ≤ c * Real.exp (-(q * (k : ℝ))) := by
      gcongr
      exact geometric_factor_le_exp_neg_mul_nat hq₁ k

/-- A nonnegative sequence with a geometric rate and factor `0 < q < 1` converges to `0`. -/
-- Proof sketch: combine the geometric upper bound with the convergence
-- `(1 - q)^k → 0`, then squeeze `r k` between `0` and `c * (1 - q)^k`.
theorem tendsto_zero
    (h : HasGeometricRateOfConvergence r q c)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k) (hc : 0 ≤ c)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    Tendsto r atTop (nhds 0) := by
  have hcontract_nonneg : 0 ≤ 1 - q := by
    linarith
  have hupper_nonneg : ∀ k : ℕ, 0 ≤ c * (1 - q) ^ k := by
    intro k
    exact mul_nonneg hc (pow_nonneg hcontract_nonneg k)
  have hpow : Tendsto (fun k : ℕ ↦ (1 - q) ^ k) atTop (nhds 0) := by
    -- The contraction factor lies in `[0, 1)`, so its powers tend to `0`.
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · exact hcontract_nonneg
    · linarith
  have hmajorant : Tendsto (fun k : ℕ ↦ c * (1 - q) ^ k) atTop (nhds 0) := by
    -- Multiplying by the fixed constant `c` preserves convergence to `0`.
    simpa using tendsto_const_nhds.mul hpow
  -- Squeeze the sequence between `0` and the vanishing majorant.
  exact squeeze_zero hr_nonneg (fun k ↦ h k) hmajorant

/-- Helper for Definition 1.2.6: a logarithmic lower bound on the iteration counter forces the
exponential majorant `c * exp (-q k)` below the target level `ε`. -/
lemma exp_threshold_le_target
    {ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hq₀ : 0 < q)
    {k : ℕ} (hk : Real.log (c / ε) / q ≤ (k : ℝ)) :
    c * Real.exp (-(q * (k : ℝ))) ≤ ε := by
  have hk' : Real.log (c / ε) ≤ q * (k : ℝ) := by
    -- Clear the positive denominator `q` to put the threshold in exponential form.
    have hk'' := (div_le_iff₀ hq₀).mp hk
    simpa [mul_comm] using hk''
  have hratio_pos : 0 < c / ε := by
    positivity
  have hratio : c / ε ≤ Real.exp (q * (k : ℝ)) := by
    -- Convert the logarithmic bound into a direct bound on `c / ε`.
    exact (Real.log_le_iff_le_exp hratio_pos).mp hk'
  have hce : c ≤ ε * Real.exp (q * (k : ℝ)) := by
    -- Restore the target scale by multiplying through by the positive tolerance `ε`.
    simpa [mul_comm] using (div_le_iff₀ hε).mp hratio
  have hexp_pos : 0 < Real.exp (q * (k : ℝ)) := Real.exp_pos _
  have hdiv : c / Real.exp (q * (k : ℝ)) ≤ ε := by
    -- Divide by the positive exponential term to recover the desired decay estimate.
    exact (div_le_iff₀ hexp_pos).2 hce
  simpa [Real.exp_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- The geometric estimate `r k ≤ c * (1 - q)^k` yields the logarithmic complexity threshold
`log (c / ε) / q`. -/
-- Proof sketch: first replace the geometric factor by the exponential bound
-- `c * exp (-q k)`, then solve `c * exp (-q k) ≤ ε` by taking logarithms and using
-- the lower bound on `k`.
theorem complexity_bound
    {ε : ℝ} (h : HasGeometricRateOfConvergence r q c)
    (hc : 0 < c) (hq₀ : 0 < q) (hq₁ : q ≤ 1) (hε : 0 < ε)
    {k : ℕ} (hkComplexity : Real.log (c / ε) / q ≤ (k : ℝ)) :
    r k ≤ ε := by
  -- Chain the exponential bridge with the logarithmic threshold estimate.
  calc
    r k ≤ c * Real.exp (-(q * (k : ℝ))) := exp_bound h hc.le hq₀ hq₁ k
    _ ≤ ε := exp_threshold_le_target hc hε hq₀ hkComplexity

/-- The exact logarithmic iteration threshold attached to the bound
`r k ≤ c * (1 - q)^k`, written with base `(1 - q)⁻¹`. -/
noncomputable abbrev iterationThreshold (q c ε : ℝ) : ℝ :=
  Real.logb ((1 - q)⁻¹) (c / ε)

/-- The exact geometric estimate `r k ≤ c * (1 - q)^k` yields the logarithmic threshold with base
`(1 - q)⁻¹`. -/
-- Proof sketch: rewrite the geometric factor as `((1 - q)⁻¹)⁻k`, then solve
-- `c * ((1 - q)⁻¹)⁻k ≤ ε` directly by taking logarithms in the base `(1 - q)⁻¹`.
theorem le_target_of_iterationThreshold_le
    {ε : ℝ} (h : HasGeometricRateOfConvergence r q c)
    (hq_contract : 1 < (1 - q)⁻¹) (hε : 0 < ε)
    {k : ℕ} (hk : iterationThreshold q c ε ≤ (k : ℝ)) :
    r k ≤ ε := by
  have hgeom : r k ≤ c * ((1 - q)⁻¹)⁻¹ ^ k := by
    simpa using h k
  have hbase_pos : 0 < (1 - q)⁻¹ := lt_trans zero_lt_one hq_contract
  have hterm : c * ((1 - q)⁻¹)⁻¹ ^ k ≤ ε := by
    by_cases hratio : 0 < c / ε
    · have hpow : c / ε ≤ ((1 - q)⁻¹) ^ (k : ℝ) := by
        exact (Real.logb_le_iff_le_rpow hq_contract hratio).1 <| by
          simpa [iterationThreshold] using hk
      have hmul : c ≤ ((1 - q)⁻¹) ^ (k : ℝ) * ε := (div_le_iff₀ hε).1 hpow
      have hpow_pos : 0 < ((1 - q)⁻¹) ^ (k : ℝ) := Real.rpow_pos_of_pos hbase_pos _
      have : c * (((1 - q)⁻¹) ^ (k : ℝ))⁻¹ ≤ ε := by
        rw [← div_eq_mul_inv, div_le_iff₀ hpow_pos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      simpa [Real.rpow_natCast, inv_pow] using this
    · have hc_nonpos : c ≤ 0 := by
        by_contra hc_nonpos
        have hc_pos : 0 < c := lt_of_not_ge hc_nonpos
        have : 0 < c / ε := by positivity
        exact hratio this
      have hpow_nonneg : 0 ≤ ((1 - q)⁻¹)⁻¹ ^ k := by
        exact pow_nonneg (inv_nonneg.mpr hbase_pos.le) _
      exact (mul_nonpos_of_nonpos_of_nonneg hc_nonpos hpow_nonneg).trans hε.le
  exact hgeom.trans hterm

/-- The natural ceiling of the exact logarithmic iteration threshold gives a valid iterate index at
which the target error level is reached. -/
theorem le_target_at_natCeil_iterationThreshold
    {ε : ℝ} (h : HasGeometricRateOfConvergence r q c)
    (hq_contract : 1 < (1 - q)⁻¹) (hε : 0 < ε) :
    r ⌈iterationThreshold q c ε⌉₊ ≤ ε := by
  simpa using le_target_of_iterationThreshold_le h hq_contract hε (Nat.le_ceil _)

end HasGeometricRateOfConvergence
