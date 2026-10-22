/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 15.30 is `source-facing`: its public content is the explicit Taylor remainder estimate
for the oscillatory scalar `t ↦ exp (it)`.

The owner abstractions for the proof are the interval-integral FTC identities for
`x ↦ Complex.exp ((x : ℂ) * Complex.I)`, the base-case bound
`Real.norm_exp_I_mul_ofReal_sub_one_le`, and the interval-integral moment formula
`integral_pow_abs_sub_uIoc`.

Accordingly, the public API stays as the textbook explicit partial-sum estimate; we do not add a
parallel local wrapper around `taylorWithinEval` or a local packaged Taylor object.
-/
/-- Helper for Lemma 15.30: the Taylor polynomial of `t ↦ exp (i t)` truncated after `n` terms. -/
noncomputable def expMulITaylor (n : ℕ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range n) fun m ↦ ((Complex.I * (t : ℂ)) ^ m) / (m.factorial : ℂ)

/-- Helper for Lemma 15.30: the remainder after truncating the Taylor series of `exp (i t)` after
`n` terms. -/
noncomputable def expMulIRemainder (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ)) - expMulITaylor n t

/-- Helper for Lemma 15.30: the next Taylor polynomial is obtained by adding the next monomial. -/
lemma expMulITaylor_succ (n : ℕ) (t : ℝ) :
    expMulITaylor (n + 1) t =
      expMulITaylor n t + ((Complex.I * (t : ℂ)) ^ n) / (n.factorial : ℂ) := by
  -- Split off the last Taylor coefficient to get a stable recursive normal form.
  simp [expMulITaylor, Finset.sum_range_succ]

/-- Helper for Lemma 15.30: over `ℂ`, the factor from the power rule cancels one factor in
`(n + 1)!`. -/
lemma succ_natCast_mul_factorial_inv (n : ℕ) :
    (n + 1 : ℂ) * (((n + 1).factorial : ℂ)⁻¹) = ((n.factorial : ℂ)⁻¹) := by
  -- Expand `(n + 1)! = (n + 1) * n!` and clear the nonzero denominator.
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp [Nat.cast_ne_zero]
  norm_num

/-- Helper for Lemma 15.30: the `(n+1)`st Taylor monomial differentiates to `I` times the `n`th
Taylor monomial. -/
lemma hasDerivAt_expMulITaylorTerm_succ (n : ℕ) (t : ℝ) :
    HasDerivAt
      (fun x : ℝ ↦ ((Complex.I * (x : ℂ)) ^ (n + 1)) / ((n + 1).factorial : ℂ))
      (Complex.I * (((Complex.I * (t : ℂ)) ^ n) / (n.factorial : ℂ))) t := by
  -- Differentiate the linear phase `x ↦ I * x`, then the power, then simplify the factorial.
  have hlin : HasDerivAt (fun x : ℝ ↦ Complex.I * (x : ℂ)) Complex.I t := by
    simpa only [mul_one] using ((hasDerivAt_id (x := (t : ℂ))).const_mul Complex.I).comp_ofReal
  have hpow := (hlin.pow (n + 1)).div_const (((n + 1).factorial : ℂ))
  simpa [div_eq_mul_inv, succ_natCast_mul_factorial_inv, mul_assoc, mul_left_comm, mul_comm]
    using hpow

/-- Helper for Lemma 15.30: the derivative of the truncated Taylor polynomial is `I` times the
previous truncation. -/
lemma expMulITaylor_hasDerivAt_succ (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ expMulITaylor (n + 1) x) (Complex.I * expMulITaylor n t) t := by
  induction n with
  | zero =>
      -- The first Taylor polynomial is constant, so its derivative vanishes.
      simpa [expMulITaylor] using (hasDerivAt_const t (c := (1 : ℂ)))
  | succ n ih =>
      -- Differentiate the recursive decomposition termwise.
      simpa [expMulITaylor_succ, mul_add, mul_assoc] using
        (ih.add (hasDerivAt_expMulITaylorTerm_succ n t))

/-- Helper for Lemma 15.30: every positive Taylor truncation evaluated at `0` equals `1`. -/
lemma expMulITaylor_succ_zero (n : ℕ) : expMulITaylor (n + 1) 0 = 1 := by
  induction n with
  | zero =>
      -- The first truncation keeps only the constant coefficient.
      simp [expMulITaylor]
  | succ n ih =>
      -- Higher-order monomials vanish at `0`, so the truncation value stays equal to `1`.
      rw [expMulITaylor_succ, ih]
      simp

/-- Helper for Lemma 15.30: the remainder at `0` vanishes after at least one Taylor term. -/
lemma expMulIRemainder_succ_zero (n : ℕ) : expMulIRemainder (n + 1) 0 = 0 := by
  -- At `t = 0`, the exponential and the first Taylor coefficient are both `1`.
  rw [expMulIRemainder, expMulITaylor_succ_zero]
  simp

/-- Helper for Lemma 15.30: the named remainder varies continuously with the real phase. -/
lemma continuous_expMulIRemainder (n : ℕ) : Continuous (fun t : ℝ ↦ expMulIRemainder n t) := by
  -- Expand the named remainder once, prove continuity structurally, and reuse this interface.
  simpa [expMulIRemainder, expMulITaylor] using
    (show Continuous
      (fun t : ℝ ↦
        Complex.exp (Complex.I * (t : ℂ)) -
          Finset.sum (Finset.range n)
            (fun m ↦ ((Complex.I * (t : ℂ)) ^ m) / (m.factorial : ℂ))) from by
        fun_prop)

/-- Helper for Lemma 15.30: the derivative of the `(n+1)`st remainder is `I` times the `n`th
remainder. -/
lemma expMulIRemainder_hasDerivAt_succ (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ expMulIRemainder (n + 1) x) (Complex.I * expMulIRemainder n t) t := by
  -- Differentiate the exponential term and the Taylor polynomial separately.
  have hlin : HasDerivAt (fun x : ℝ ↦ Complex.I * (x : ℂ)) Complex.I t := by
    simpa only [mul_one] using ((hasDerivAt_id (x := (t : ℂ))).const_mul Complex.I).comp_ofReal
  have hexp : HasDerivAt (fun x : ℝ ↦ Complex.exp (Complex.I * (x : ℂ)))
      (Complex.exp (Complex.I * (t : ℂ)) * Complex.I) t := by
    simpa using hlin.cexp
  simpa [expMulIRemainder, mul_sub, mul_comm, mul_left_comm, mul_assoc] using
    hexp.sub (expMulITaylor_hasDerivAt_succ n t)

/-- Helper for Lemma 15.30: the successor remainder is the unit-interval integral of the previous
remainder along the ray `s ↦ s t`. -/
lemma expMulIRemainder_eq_unitIntervalIntegral_succ (n : ℕ) (t : ℝ) :
    expMulIRemainder (n + 1) t =
      t • ∫ s in (0 : ℝ)..1, Complex.I * expMulIRemainder n (s * t) := by
  -- Apply the unit-interval FTC to the remainder along the segment from `0` to `t`.
  have hcont : ContinuousOn
      (fun s : ℝ ↦ Complex.I * expMulIRemainder n (s * t)) (Set.Icc 0 1) := by
    -- Reuse the continuity of the named remainder instead of unfolding the whole finite sum here.
    exact (Continuous.continuousOn <|
      continuous_const.mul <|
        (continuous_expMulIRemainder n).comp (continuous_id.mul continuous_const))
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ ↦ expMulIRemainder (n + 1) x)
        (Complex.I * expMulIRemainder n (s * t)) (s * t) := by
    intro s hs
    simpa using expMulIRemainder_hasDerivAt_succ n (s * t)
  have hFTC := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (z₀ := (0 : ℝ)) (z₁ := t) (f := fun x : ℝ ↦ expMulIRemainder (n + 1) x)
    (f' := fun x : ℝ ↦ Complex.I * expMulIRemainder n x)
    (by simpa [zero_add, smul_eq_mul] using hcont)
    (by
      intro s hs
      simpa [zero_add, smul_eq_mul] using hderiv s hs)
  have hzero : (fun x : ℝ ↦ expMulIRemainder (n + 1) x) 0 = 0 := expMulIRemainder_succ_zero n
  simpa [hzero, zero_add, one_smul, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    using hFTC.symm

/-- Helper for Lemma 15.30: the Taylor remainder of `exp (i t)` is bounded by `|t| ^ n / n!`. -/
lemma norm_expMulIRemainder_le (n : ℕ) (t : ℝ) :
    ‖expMulIRemainder n t‖ ≤ |t| ^ n / (n.factorial : ℝ) := by
  induction n generalizing t with
  | zero =>
      -- The zeroth remainder is just `exp (i t)`, which has norm `1`.
      simp [expMulIRemainder, expMulITaylor, Complex.norm_exp_I_mul_ofReal t]
  | succ n ih =>
      -- Rewrite the successor remainder as a unit-interval integral and estimate it by induction.
      have hmajorant :
          IntervalIntegrable (fun s : ℝ ↦ (|t| ^ n / (n.factorial : ℝ)) * s ^ n)
            MeasureTheory.volume 0 1 := by
        -- The scalar majorant is a continuous polynomial on the unit interval.
        exact Continuous.intervalIntegrable (by fun_prop) 0 1
      rw [expMulIRemainder_eq_unitIntervalIntegral_succ]
      calc
        ‖t • ∫ s in (0 : ℝ)..1, Complex.I * expMulIRemainder n (s * t)‖
            = |t| * ‖∫ s in (0 : ℝ)..1, Complex.I * expMulIRemainder n (s * t)‖ := by
                convert norm_mul (t : ℂ)
                  (∫ s in (0 : ℝ)..1, Complex.I * expMulIRemainder n (s * t)) using 1
                simp [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |t| * ∫ s in (0 : ℝ)..1, (|t| ^ n / (n.factorial : ℝ)) * s ^ n := by
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
              refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hmajorant
              filter_upwards with s hs
              -- The inductive estimate controls the integrand at each point of the segment.
              have hs_nonneg : 0 ≤ s := hs.1.le
              calc
                ‖Complex.I * expMulIRemainder n (s * t)‖ = ‖expMulIRemainder n (s * t)‖ := by
                  rw [norm_mul, Complex.norm_I, one_mul]
                _ ≤ |s * t| ^ n / (n.factorial : ℝ) := ih (s * t)
                _ = (|t| ^ n / (n.factorial : ℝ)) * s ^ n := by
                    rw [abs_mul, abs_of_nonneg hs_nonneg, mul_pow, div_eq_mul_inv]
                    ring
        _ = |t| * ((|t| ^ n / (n.factorial : ℝ)) * (∫ s in (0 : ℝ)..1, s ^ n)) := by
              rw [intervalIntegral.integral_const_mul]
        _ = |t| * ((|t| ^ n / (n.factorial : ℝ)) * ((1 : ℝ) / (n + 1))) := by
              rw [integral_pow]
              simp
        _ = |t| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
              have hn1 : (n + 1 : ℝ) ≠ 0 := ne_of_gt (by positivity)
              have hfact : (n.factorial : ℝ) ≠ 0 :=
                Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
              rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, div_eq_mul_inv]
              field_simp [hn1, hfact]
              rw [Nat.cast_add, Nat.cast_one]

-- Proof sketch: integrate the derivative identity for `x ↦ Complex.exp ((x : ℂ) * Complex.I)`
-- recursively. The base case is `Real.norm_exp_I_mul_ofReal_sub_one_le`, and each induction step
-- gains a factor `1 / n` from the interval-integral bound on `|x| ^ (n - 1)`.
/-- Lemma 15.30: for `t ∈ ℝ` and `n ∈ ℕ`, the remainder after truncating the Taylor series of
`exp (i t)` at order `n - 1` is bounded by `|t| ^ n / n!`. -/
theorem norm_exp_mul_I_sub_taylor_sum_le (t : ℝ) (n : ℕ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) -
        Finset.sum (Finset.range n) (fun m ↦ (((t : ℂ) * Complex.I) ^ m) / m.factorial)‖ ≤
      |t| ^ n / n.factorial := by
  -- Repackage the target as the norm bound for the named remainder.
  simpa [expMulIRemainder, expMulITaylor, mul_comm] using norm_expMulIRemainder_le n t
