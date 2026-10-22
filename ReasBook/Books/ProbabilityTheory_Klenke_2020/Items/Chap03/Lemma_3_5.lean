/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Lemma 3.5: evaluating the binomial formal multilinear series on a constant tuple
recovers the usual generalized binomial coefficient times the corresponding power. -/
lemma binomial_series_term_eval {α : ℝ} {x : ℂ} (n : ℕ) :
    (binomialSeries ℂ (α : ℂ)) n (fun _ : Fin n ↦ x) = Ring.choose (α : ℂ) n * x ^ n := by
  -- The multilinear term is the scalar coefficient times the product of the constant tuple.
  rw [binomialSeries_apply]
  simp [smul_eq_mul]

/-- Lemma 3.5: the generalized binomial series for a real exponent `α` sums to the principal
complex power `(1 + x)^α` for `|x| < 1`. -/
-- Proof sketch: use `Complex.one_add_cpow_hasFPowerSeriesOnBall_zero`, evaluate the resulting
-- power series at `x` via `HasFPowerSeriesOnBall.hasSum_sub`, and rewrite the coefficients with
-- `binomialSeries_apply` and `Complex.ofReal_choose`.
theorem generalized_binomial_hasSum {α : ℝ} {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ ↦ Ring.choose (α : ℂ) k * x ^ k) ((1 + x) ^ (α : ℂ)) := by
  -- The analytic power series theorem applies on the open unit ball around `0`.
  have hx' : x ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using hx
  -- Evaluate the formal series at `x` and rewrite each term into the standard binomial shape.
  refine
    (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (α : ℂ))).hasSum_sub hx' |>.congr_fun ?_
  intro n
  simpa using (binomial_series_term_eval (α := α) (x := x) n).symm

/-- Helper for Lemma 3.5: the coefficients `\binom{-1/2}{n}` satisfy the expected one-step
recurrence. -/
lemma choose_half_neg_recurrence (n : ℕ) :
    Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) (n + 1) =
      -(((2 * n + 1 : ℂ) / (2 * (n + 1))) *
        Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) n) := by
  -- Clear the factorial denominator using the descending Pochhammer recurrence.
  have hrec : (n + 1 : ℂ) * Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) (n + 1) =
      (((-((1 : ℝ) / 2) : ℝ) : ℂ) - n) * Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) n := by
    have hdesc :=
      congrArg (fun p : Polynomial ℤ ↦ p.smeval (((-((1 : ℝ) / 2) : ℝ) : ℂ)))
        (descPochhammer_succ_right ℤ n)
    simp only [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast] at hdesc
    rw [Ring.descPochhammer_eq_factorial_smul_choose,
      Ring.descPochhammer_eq_factorial_smul_choose] at hdesc
    simp only [nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hdesc
    have hfac : ((n.factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    exact (mul_right_injective₀ hfac) <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hdesc
  have hsucc : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  -- Multiply by `n + 1` to avoid divisions, then solve the resulting scalar identity.
  apply_fun (fun z : ℂ ↦ z * (n + 1 : ℂ)) using mul_left_injective₀ hsucc
  calc
    Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) (n + 1) * (n + 1 : ℂ)
        = (((-((1 : ℝ) / 2) : ℝ) : ℂ) - n) *
            Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) n := by
            simpa [mul_comm] using hrec
    _ = -(((2 * n + 1 : ℂ) / (2 * (n + 1))) *
            Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) n) * (n + 1 : ℂ) := by
          field_simp [hsucc]
          norm_num
          ring

/-- Helper for Lemma 3.5: the central binomial coefficients satisfy the matching one-step
recurrence after dividing by powers of `4`. -/
lemma central_binomial_step (n : ℕ) :
    ((2 * n + 1 : ℂ) / (2 * (n + 1))) * (Nat.choose (2 * n) n : ℂ) =
      (Nat.choose (2 * (n + 1)) (n + 1) : ℂ) * (4 : ℂ)⁻¹ := by
  -- Cast the natural recurrence for central binomial coefficients into `ℂ`.
  have hcb : ((n + 1 : ℂ) * (Nat.choose (2 * (n + 1)) (n + 1) : ℂ)) =
      (2 * (2 * n + 1) : ℂ) * (Nat.choose (2 * n) n : ℂ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have hsucc : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have htwo : (2 : ℂ) ≠ 0 := by
    norm_num
  have hmul : (2 * (n + 1 : ℂ)) ≠ 0 := by
    exact mul_ne_zero htwo hsucc
  -- Again, clear denominators first and only then rewrite with the natural-number recurrence.
  apply_fun (fun z : ℂ ↦ z * (2 * (n + 1 : ℂ))) using mul_left_injective₀ hmul
  field_simp [htwo, hsucc]
  have hcb' := congrArg (fun z : ℂ ↦ (2 : ℂ) * z) hcb
  convert hcb'.symm using 1 <;> ring

/-- Helper for Lemma 3.5: the signed half-binomial coefficients equal the normalized central
binomial coefficients. -/
lemma neg_half_choose_signed_eq_central (n : ℕ) :
    Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) n * (-1 : ℂ) ^ n =
      (Nat.choose (2 * n) n : ℂ) * (4 : ℂ)⁻¹ ^ n := by
  induction n with
  | zero =>
      -- Both sides start with the constant coefficient `1`.
      simp
  | succ n ih =>
      -- Advance both coefficient sequences by their matching recurrences.
      calc
        Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) (n + 1) * (-1 : ℂ) ^ (n + 1)
            = ((2 * n + 1 : ℂ) / (2 * (n + 1))) *
                (Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) n * (-1 : ℂ) ^ n) := by
                  rw [pow_succ, choose_half_neg_recurrence]
                  ring
        _ = ((2 * n + 1 : ℂ) / (2 * (n + 1))) *
              ((Nat.choose (2 * n) n : ℂ) * (4 : ℂ)⁻¹ ^ n) := by
                rw [ih]
        _ = (((2 * n + 1 : ℂ) / (2 * (n + 1))) * (Nat.choose (2 * n) n : ℂ)) *
              (4 : ℂ)⁻¹ ^ n := by
                ring
        _ = ((Nat.choose (2 * (n + 1)) (n + 1) : ℂ) * (4 : ℂ)⁻¹) *
              (4 : ℂ)⁻¹ ^ n := by
                rw [central_binomial_step]
        _ = (Nat.choose (2 * (n + 1)) (n + 1) : ℂ) * (4 : ℂ)⁻¹ ^ (n + 1) := by
              rw [pow_succ]
              ring

/-- Helper for Lemma 3.5: after substituting `-x` into the half-binomial series, the coefficient of
`x^n` becomes the normalized central binomial coefficient. -/
lemma neg_half_choose_mul_neg_pow {x : ℂ} (n : ℕ) :
    Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) n * (-x) ^ n =
      (Nat.choose (2 * n) n : ℂ) * (4 : ℂ)⁻¹ ^ n * x ^ n := by
  -- Separate the sign from `(-x)^n`, then rewrite the signed coefficient.
  rw [show (-x) = (-1 : ℂ) * x by ring, mul_pow]
  calc
    Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) n * ((-1 : ℂ) ^ n * x ^ n)
        = (Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) n * (-1 : ℂ) ^ n) * x ^ n := by
            ring
    _ = ((Nat.choose (2 * n) n : ℂ) * (4 : ℂ)⁻¹ ^ n) * x ^ n := by
          rw [neg_half_choose_signed_eq_central]
    _ = (Nat.choose (2 * n) n : ℂ) * (4 : ℂ)⁻¹ ^ n * x ^ n := by
          ring

/-- The central-binomial specialization of the generalized binomial theorem gives the power series
for `1 / √(1 - x)` on the open unit disk. -/
-- Proof sketch: apply `generalized_binomial_hasSum` to `-x` with exponent `α = -1 / 2`, rewrite
-- the left-hand side as `1 / Complex.sqrt (1 - x)`, and simplify the coefficients using
-- `Ring.choose_neg`, `Ring.choose_natCast`, and `Nat.choose_symm_add`.
theorem inverse_sqrt_one_sub_hasSum {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ (Nat.choose (2 * n) n : ℂ) * (4 : ℂ)⁻¹ ^ n * x ^ n)
      (1 / Complex.sqrt (1 - x)) := by
  -- Route correction: specialize the main generalized binomial theorem at `-x`; the sign
  -- cancellation is handled once and for all by `neg_half_choose_mul_neg_pow`.
  have hspecial :
      HasSum
        (fun n : ℕ ↦ Ring.choose (((-((1 : ℝ) / 2) : ℝ) : ℂ)) n * (-x) ^ n)
        ((1 + -x) ^ (((-((1 : ℝ) / 2) : ℝ) : ℂ))) := by
    simpa using generalized_binomial_hasSum (α := -((1 : ℝ) / 2)) (x := -x) (by simpa using hx)
  -- Rewrite the summand termwise into the central-binomial form.
  have hcoeff :
      HasSum
        (fun n : ℕ ↦ (Nat.choose (2 * n) n : ℂ) * (4 : ℂ)⁻¹ ^ n * x ^ n)
        ((1 + -x) ^ (((-((1 : ℝ) / 2) : ℝ) : ℂ))) := by
    refine hspecial.congr_fun ?_
    intro n
    exact (neg_half_choose_mul_neg_pow (x := x) n).symm
  -- The value is exactly the reciprocal of the principal square root.
  simpa [sub_eq_add_neg, Complex.sqrt, Complex.cpow_neg] using hcoeff
