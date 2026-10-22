/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

variable {r : ℕ → ℝ}

/-
Primary domain: scalar convergence rates for real error sequences.

Source/core/bridge triage for Definition 1.2.7:
* source-facing: the textbook quadratic-rate statement
  `∃ c > 0, ∀ k, r (k + 1) ≤ c * r k^2`;
* core/canonical: `HasEventuallySuperlinearErrorBound r 0 c 0`;
* bridge/view: the equivalence between that owner specialization and the explicit quadratic
  recurrence.

Relevant owner-style declarations sampled before refining:
* the scalar owner `HasEventuallySuperlinearErrorBound`, introduced below and reused by
  `HasSuperlinearRateOfConvergence` in `Definition_1_8_15.lean`;
* the owner `HasGeometricRateOfConvergence` and the source-facing linear-rate condition in
  `Definition_1_2_6.lean`;
* the direct square-root specialization
  `HasConvergenceRateOfOrder r (fun N ↦ 1 / Real.sqrt (N : ℝ))` in
  `Definition_1_6_9.lean`.

Owner abstraction:
* `HasEventuallySuperlinearErrorBound r 0 c 0`

Primitive data:
* the sequence `r`
* the constant `c`
* the owner recurrence witness `HasEventuallySuperlinearErrorBound r 0 c 0`

Derived API:
* the textbook quadratic recurrence `r (k + 1) ≤ c * r k^2`
* the source-facing existential statement from Definition 1.2.7
* the linear one-step estimate derived once `c * r k ≤ 1 / 2`
* the Proposition 1.7.6 tail estimate and logarithmic threshold consequence in the quadratic case

This file therefore recalls the owner specialization directly and removes the redundant alias
`HasQuadraticRateOfConvergence`. The numbered item is the canonical specialization
`∃ c > 0, HasEventuallySuperlinearErrorBound r 0 c 0`, while the explicit quadratic recurrence
remains available through the two atomic bridge lemmas below.
-/

/-- An error sequence has an eventual superlinear bound with lag `lag` from index `N` onward if
the textbook estimate
`r_{k+1} ≤ c * r_k * r_{k-lag}`
holds for every `k ≥ N`, with `N` chosen large enough that the lagged term is available. -/
def HasEventuallySuperlinearErrorBound
    (r : ℕ → ℝ) (lag : ℕ) (c : ℝ) (N : ℕ) : Prop :=
  lag ≤ N ∧ ∀ ⦃k : ℕ⦄, N ≤ k → r (k + 1) ≤ c * r k * r (k - lag)

/- Definition 1.2.7 is recalled by the canonical specialization
`∃ c > 0, HasEventuallySuperlinearErrorBound r 0 c 0`. -/
#check (∃ c > 0, HasEventuallySuperlinearErrorBound r 0 c 0)

namespace HasEventuallySuperlinearErrorBound

variable {c : ℝ}

/-- The starting index `N` is large enough that the lagged term `r (k - lag)` is available. -/
theorem lag_le
    {lag N : ℕ}
    (h : HasEventuallySuperlinearErrorBound r lag c N) :
    lag ≤ N :=
  h.1

/-- The textbook recurrence estimate holds at every index `k ≥ N`. -/
theorem bound
    {lag N : ℕ}
    (h : HasEventuallySuperlinearErrorBound r lag c N) :
    ∀ ⦃k : ℕ⦄, N ≤ k → r (k + 1) ≤ c * r k * r (k - lag) :=
  h.2

/-- A quadratic recurrence bound immediately gives the corresponding one-step estimate. -/
-- Proof sketch: specialize `HasEventuallySuperlinearErrorBound.bound` to `lag = 0` and `N = 0`,
-- then simplify `r (k - 0)` to `r k`.
theorem quadratic_bound
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    (k : ℕ) :
    r (k + 1) ≤ c * (r k)^2 := by
  simpa [pow_two, Nat.sub_zero, mul_assoc] using h.bound (Nat.zero_le k)

/-- The textbook quadratic recurrence defines the owner specialization with `lag = 0` and
starting index `0`. -/
theorem of_quadratic_bound
    (h : ∀ k : ℕ, r (k + 1) ≤ c * (r k)^2) :
    HasEventuallySuperlinearErrorBound r 0 c 0 := by
  refine ⟨le_rfl, ?_⟩
  intro k hk
  simpa [pow_two, Nat.sub_zero, mul_assoc] using h k

/-- Once `c * r k ≤ 1 / 2`, a quadratic recurrence implies the linear estimate
`r (k + 1) ≤ (1 / 2) * r k` at the next iterate. -/
-- Proof sketch: combine `quadratic_bound` with `c * r k ≤ 1 / 2`, rewrite
-- `c * (r k)^2` as `(c * r k) * r k`, and use `0 ≤ r k` to preserve the inequality after
-- multiplying by `r k`.
theorem linear_bound_of_mul_le_half
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    {k : ℕ}
    (hrk : 0 ≤ r k)
    (hthreshold : c * r k ≤ (1 / 2 : ℝ)) :
    r (k + 1) ≤ (1 / 2 : ℝ) * r k := by
  refine (quadratic_bound h k).trans ?_
  have hmul := mul_le_mul_of_nonneg_right hthreshold hrk
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Definition 1.2.7: after scaling by `c`, the quadratic recurrence becomes the
repeated-squaring step `a_{k+1} ≤ a_k^2`. -/
-- Proof sketch: multiply `quadratic_bound` by the positive factor `c` and regroup the product
-- into the square of the scaled quantity.
lemma scaled_quadratic_step
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    (hc : 0 < c)
    (k : ℕ) :
    c * r (k + 1) ≤ (c * r k)^2 := by
  have hmul :=
    mul_le_mul_of_nonneg_left (quadratic_bound h k) (le_of_lt hc)
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Definition 1.2.7: the scaled quadratic recurrence yields a repeated-squaring tail
bound for every offset `j`. -/
-- Proof sketch: induct on the offset, apply `scaled_quadratic_step` at the current index, and
-- use monotonicity of squaring on nonnegative reals to square the induction hypothesis.
lemma scaled_tail_bound
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k) (hc : 0 < c)
    (k0 j : ℕ) :
    c * r (k0 + j) ≤ (c * r k0) ^ (2 ^ j : ℕ) := by
  induction j with
  | zero =>
      -- At offset `0`, the claimed bound is exactly the identity `a ≤ a`.
      simp
  | succ j ih =>
      -- The recurrence turns the next scaled iterate into a square, and the induction
      -- hypothesis bounds the previous scaled iterate by the previous repeated square.
      have hstep := scaled_quadratic_step h hc (k0 + j)
      have hscaled_nonneg : 0 ≤ c * r (k0 + j) := by
        exact mul_nonneg (le_of_lt hc) (hr_nonneg (k0 + j))
      have hpow_nonneg : 0 ≤ (c * r k0) ^ (2 ^ j : ℕ) := by
        exact pow_nonneg (mul_nonneg (le_of_lt hc) (hr_nonneg k0)) _
      have hsquare :
          (c * r (k0 + j)) ^ 2 ≤ ((c * r k0) ^ (2 ^ j : ℕ)) ^ 2 := by
        exact (sq_le_sq₀ hscaled_nonneg hpow_nonneg).2 ih
      calc
        c * r (k0 + j.succ) = c * r ((k0 + j) + 1) := by
          simp [Nat.add_assoc]
        _ ≤ (c * r (k0 + j)) ^ 2 := by
          simpa [Nat.add_assoc] using hstep
        _ ≤ ((c * r k0) ^ (2 ^ j : ℕ)) ^ 2 := hsquare
        _ = (c * r k0) ^ (2 ^ j.succ : ℕ) := by
          rw [show (2 ^ j.succ : ℕ) = (2 ^ j : ℕ) * 2 by rw [Nat.pow_succ], pow_mul]

/-- Helper for Definition 1.2.7: a base-two logarithmic lower bound implies that the repeated
square `(a ^ (2^j))` has already dropped below the target `b`. -/
-- Proof sketch: convert the `logb` inequality into a bound on the ratio of positive logarithms,
-- rewrite the resulting real power as the natural power `2 ^ j`, compare logarithms, and then
-- invert the positive quantities.
lemma scaled_pow_le_target_of_logb_bound
    {a b : ℝ} {j : ℕ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hj : Real.logb 2 (Real.log (1 / b) / Real.log (1 / a)) ≤ (j : ℝ)) :
    a ^ (2 ^ j : ℕ) ≤ b := by
  have hlog_a_pos : 0 < Real.log (1 / a) := by
    -- Since `0 < a < 1`, its reciprocal is larger than `1`, so its logarithm is positive.
    have h_inv : 1 < 1 / a := by
      rw [one_div]
      exact (one_lt_inv₀ ha0).2 ha1
    exact Real.log_pos h_inv
  have hlog_b_pos : 0 < Real.log (1 / b) := by
    -- The same reciprocal-log positivity applies to the target scale `b`.
    have h_inv : 1 < 1 / b := by
      rw [one_div]
      exact (one_lt_inv₀ hb0).2 hb1
    exact Real.log_pos h_inv
  have hratio_pos : 0 < Real.log (1 / b) / Real.log (1 / a) := by
    exact div_pos hlog_b_pos hlog_a_pos
  have hpow_real : Real.log (1 / b) / Real.log (1 / a) ≤ (2 : ℝ) ^ (j : ℝ) := by
    exact (Real.logb_le_iff_le_rpow (by norm_num) hratio_pos).1 hj
  have hmul : Real.log (1 / b) ≤ ((2 : ℝ) ^ (j : ℝ)) * Real.log (1 / a) := by
    exact (div_le_iff₀ hlog_a_pos).1 hpow_real
  have hpow_cast : ((2 : ℝ) ^ (j : ℝ)) = (2 ^ j : ℕ) := by
    rw [Real.rpow_natCast]
    norm_num [Nat.cast_pow]
  have hmul_nat : Real.log (1 / b) ≤ (2 ^ j : ℕ) * Real.log (1 / a) := by
    simpa [hpow_cast] using hmul
  have hlog_le : Real.log (1 / b) ≤ Real.log ((1 / a) ^ (2 ^ j : ℕ)) := by
    -- This is the logarithmic form of the desired power comparison.
    rw [← Real.rpow_natCast, Real.log_rpow (by positivity), mul_comm]
    simpa [mul_comm] using hmul_nat
  have hle_inv : 1 / b ≤ (1 / a) ^ (2 ^ j : ℕ) := by
    -- Strict monotonicity of `log` on positive reals turns the logarithmic inequality back into
    -- an inequality of the positive arguments themselves.
    refine le_of_not_gt ?_
    intro hgt
    have hlt_log : Real.log ((1 / a) ^ (2 ^ j : ℕ)) < Real.log (1 / b) := by
      exact Real.strictMonoOn_log
        (by simpa using show 0 < (1 / a) ^ (2 ^ j : ℕ) by positivity)
        (by simpa using hb0)
        hgt
    linarith
  have ha_pow_pos : 0 < a ^ (2 ^ j : ℕ) := by
    exact pow_pos ha0 _
  have hle_inv' : b⁻¹ ≤ (a ^ (2 ^ j : ℕ))⁻¹ := by
    simpa [one_div, inv_pow] using hle_inv
  exact (inv_le_inv₀ hb0 ha_pow_pos).1 hle_inv'

/-- Proposition 1.7.6, owner form: under a quadratic recurrence, the tail is bounded by
repeated squaring of `c * r K`. -/
theorem quadratic_tail_bound
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k) (hc : 0 < c)
    (k0 j : ℕ) :
    r (k0 + j) ≤ (1 / c) * (c * r k0) ^ (2 ^ j : ℕ) := by
  -- We first bound the scaled tail `c * r (k0 + j)` by repeated squaring and then divide by the
  -- positive constant `c`.
  have hscaled := scaled_tail_bound h hr_nonneg hc k0 j
  simpa [one_div] using
    (le_inv_mul_iff₀ hc).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)

/-- Proposition 1.7.6, owner form: a base-two logarithmic lower bound on `j` forces the tail
estimate `r (K + j) ≤ ε` under the quadratic recurrence assumptions. -/
theorem quadratic_tail_le_of_logb_bound
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k) (hc : 0 < c)
    (k0 j : ℕ) (ε : ℝ)
    (hK0 : 0 < c * r k0) (hK1 : c * r k0 < 1)
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / c))
    (hj :
      Real.logb 2 (Real.log (1 / (c * ε)) / Real.log (1 / (c * r k0))) ≤ (j : ℝ)) :
    r (k0 + j) ≤ ε := by
  -- Route correction: keep the source-owner route. First use the repeated-squaring tail bound,
  -- then show that the logarithmic threshold forces the repeated square below `c * ε`.
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hε0 : 0 < ε := hε.1
  have hb0 : 0 < c * ε := by
    exact mul_pos hc hε0
  have hb1 : c * ε < 1 := by
    have hmul : c * ε < c * (1 / c) := by
      exact mul_lt_mul_of_pos_left hε.2 hc
    simpa [one_div, hc0, mul_assoc] using hmul
  have hpow_le :
      (c * r k0) ^ (2 ^ j : ℕ) ≤ c * ε := by
    exact scaled_pow_le_target_of_logb_bound hK0 hK1 hb0 hb1 hj
  have htail := quadratic_tail_bound h hr_nonneg hc k0 j
  have hfinal :
      (1 / c) * (c * r k0) ^ (2 ^ j : ℕ) ≤ ε := by
    -- Multiplying by `1 / c` preserves the inequality and collapses `((1 / c) * c)` to `1`.
    have hscaled :
        (1 / c) * (c * r k0) ^ (2 ^ j : ℕ) ≤ (1 / c) * (c * ε) := by
      exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
    simpa [one_div, hc0, mul_assoc, mul_left_comm, mul_comm] using hscaled
  exact htail.trans hfinal

end HasEventuallySuperlinearErrorBound
