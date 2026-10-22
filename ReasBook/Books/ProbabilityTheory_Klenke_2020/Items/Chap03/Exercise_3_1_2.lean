/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Definition_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open Filter

/-- Two probability generating functions agree on an injective sequence of points in `(0,1)`. -/
def ProbabilityGeneratingFunctionsAgreeOnInjectiveSequence (p q : PMF ℕ) : Prop :=
  ∃ x : ℕ → Set.Ioo (0 : ℝ) 1,
    Function.Injective x ∧
      ∀ n : ℕ,
        probabilityGeneratingFunctionReal p (x n) =
          probabilityGeneratingFunctionReal q (x n)

/-- Helper for Exercise 3.1.2: the oscillatory binomial coefficient sequence coming from
`(1 - z) ^ (2 + Complex.I)`. -/
private noncomputable def oscillatoryCoeffComplex (n : ℕ) : ℂ :=
  Ring.choose ((2 : ℂ) + Complex.I) n * (-1 : ℂ) ^ n

/-- Helper for Exercise 3.1.2: the real-valued coefficient sequence extracted from the oscillatory
complex binomial series. -/
private noncomputable def oscillatoryCoeff (n : ℕ) : ℝ :=
  Complex.re (oscillatoryCoeffComplex n)

/-- Helper for Exercise 3.1.2: the explicit sampling values where the oscillatory closed form
vanishes. -/
private noncomputable def samplingPointValue (n : ℕ) : ℝ :=
  1 - Real.exp (-(Real.pi / 2 + (n : ℝ) * Real.pi))

/-- Helper for Exercise 3.1.2: every explicit sampling value lies in `(0,1)`. -/
private theorem samplingPointValue_mem (n : ℕ) : samplingPointValue n ∈ Set.Ioo (0 : ℝ) 1 := by
  -- The exponential term lies in `(0,1)`, so subtracting it from `1` keeps the value in `(0,1)`.
  constructor
  · dsimp [samplingPointValue]
    have hexp_lt : Real.exp (-(Real.pi / 2 + (n : ℝ) * Real.pi)) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      nlinarith [Real.pi_pos]
    linarith
  · dsimp [samplingPointValue]
    have hexp_pos : 0 < Real.exp (-(Real.pi / 2 + (n : ℝ) * Real.pi)) := Real.exp_pos _
    linarith

/-- Helper for Exercise 3.1.2: the countable witness set packaged as points of `Set.Ioo (0,1)`. -/
private noncomputable def samplingPoint (n : ℕ) : Set.Ioo (0 : ℝ) 1 :=
  ⟨samplingPointValue n, samplingPointValue_mem n⟩

/-- Helper for Exercise 3.1.2: the sampling sequence is strictly increasing, hence injective. -/
private theorem samplingPoint_injective : Function.Injective samplingPoint := by
  -- Monotonicity follows because the exponential term decreases strictly with `n`.
  refine StrictMono.injective ?_
  intro m n hmn
  change samplingPointValue m < samplingPointValue n
  dsimp [samplingPointValue]
  have hexp_lt :
      Real.exp (-(Real.pi / 2 + (n : ℝ) * Real.pi)) <
        Real.exp (-(Real.pi / 2 + (m : ℝ) * Real.pi)) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [show (m : ℝ) < n by exact_mod_cast hmn, Real.pi_pos]
  linarith

/-- Helper for Exercise 3.1.2: evaluating the binomial multilinear series on a constant tuple
recovers the scalar generalized binomial coefficient. -/
private lemma binomialSeriesTermEval {a x : ℂ} (n : ℕ) :
    (binomialSeries ℂ a) n (fun _ : Fin n ↦ x) = Ring.choose a n * x ^ n := by
  -- The multilinear term is the scalar coefficient times the product of the constant tuple.
  rw [binomialSeries_apply]
  simp [smul_eq_mul]

/-- Helper for Exercise 3.1.2: the generalized binomial series sums to the principal complex
power inside the open unit disk. -/
private theorem generalizedBinomialHasSum {a x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ Ring.choose a n * x ^ n) ((1 + x) ^ a) := by
  -- Evaluate the analytic binomial power series at `x` and rewrite its coefficients explicitly.
  have hx' : x ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using hx
  refine
    (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum_sub hx' |>.congr_fun ?_
  intro n
  simpa using (binomialSeriesTermEval (a := a) (x := x) n).symm

/-- Helper for Exercise 3.1.2: for a positive real base, the real part of the complex power
`t ^ (2 + Complex.I)` is `t^2 * cos (log t)`. -/
private theorem positiveBaseCpow_re {t : ℝ} (ht : 0 < t) :
    Complex.re ((t : ℂ) ^ ((2 : ℂ) + Complex.I)) = t ^ (2 : ℕ) * Real.cos (Real.log t) := by
  -- Rewrite the exponent as a product of the integer square and the oscillatory `t ^ I` factor.
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hpow2 : (t : ℂ) ^ (2 : ℂ) = ((t ^ (2 : ℕ) : ℝ) : ℂ) := by
    calc
      (t : ℂ) ^ (2 : ℂ) = (t : ℂ) ^ (2 : ℕ) := by
        simp
      _ = ((t ^ (2 : ℕ) : ℝ) : ℂ) := by
        simp
  rw [Complex.cpow_add _ _ ht0, hpow2]
  -- Normalize the `t ^ I` term using the principal logarithm on the positive real axis.
  rw [Complex.cpow_def_of_ne_zero ht0, ← Complex.ofReal_log ht.le]
  -- The first factor is real, so taking the real part only sees the cosine in `exp (log t * I)`.
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- Helper for Exercise 3.1.2: the oscillatory real power series equals the explicit closed form
`(1 - z)^2 * cos (log (1 - z))` on `(0,1)`. -/
private theorem oscillatorySeries_eq_closedForm {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    (∑' n : ℕ, oscillatoryCoeff n * z ^ n) = (1 - z) ^ (2 : ℕ) * Real.cos (Real.log (1 - z)) := by
  -- Route correction: first stabilize the complex binomial identity, then only take real parts.
  have hnorm : ‖(-(z : ℂ))‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz0] using hz1
  have hsumComplex :
      HasSum
        (fun n : ℕ ↦ Ring.choose ((2 : ℂ) + Complex.I) n * (-(z : ℂ)) ^ n)
        ((1 + (-(z : ℂ))) ^ ((2 : ℂ) + Complex.I)) :=
    generalizedBinomialHasSum (a := (2 : ℂ) + Complex.I) (x := -(z : ℂ)) hnorm
  have hsumReal :
      HasSum
        (fun n : ℕ ↦ Complex.re (Ring.choose ((2 : ℂ) + Complex.I) n * (-(z : ℂ)) ^ n))
        (Complex.re (((1 - z : ℝ) : ℂ) ^ ((2 : ℂ) + Complex.I))) := by
    convert Complex.hasSum_re hsumComplex using 1
    simp [sub_eq_add_neg]
  have hsumConverted :
      HasSum (fun n : ℕ ↦ oscillatoryCoeff n * z ^ n)
        (Complex.re (((1 - z : ℝ) : ℂ) ^ ((2 : ℂ) + Complex.I))) := by
    refine hsumReal.congr_fun ?_
    intro n
    -- Separate the sign oscillation from the positive real factor `z ^ n`.
    rw [show (-(z : ℂ)) ^ n = (-1 : ℂ) ^ n * (z : ℂ) ^ n by
      simpa using (mul_pow (-1 : ℂ) (z : ℂ) n)]
    rw [← Complex.ofReal_pow, ← mul_assoc, Complex.re_mul_ofReal]
    simp [oscillatoryCoeff, oscillatoryCoeffComplex]
  have hpos : 0 < 1 - z := by
    linarith
  -- Finish by rewriting the real part of the complex closed form on the positive real axis.
  calc
    (∑' n : ℕ, oscillatoryCoeff n * z ^ n) =
        Complex.re (((1 - z : ℝ) : ℂ) ^ ((2 : ℂ) + Complex.I)) := hsumConverted.tsum_eq
    _ = (1 - z) ^ (2 : ℕ) * Real.cos (Real.log (1 - z)) := positiveBaseCpow_re hpos

/-- Helper for Exercise 3.1.2: the oscillatory closed form vanishes at every explicit sampling
point. -/
private theorem samplingPoint_closedForm_eq_zero (n : ℕ) :
    (1 - (samplingPoint n : ℝ)) ^ (2 : ℕ) *
        Real.cos (Real.log (1 - (samplingPoint n : ℝ))) = 0 := by
  -- The logarithm becomes `-(π / 2 + nπ)`, so the cosine factor vanishes.
  have hpoint :
      1 - (samplingPoint n : ℝ) = Real.exp (-(Real.pi / 2 + (n : ℝ) * Real.pi)) := by
    simp [samplingPoint, samplingPointValue]
  rw [hpoint]
  have hlog :
      Real.log (Real.exp (-(Real.pi / 2 + (n : ℝ) * Real.pi))) =
        -(Real.pi / 2 + (n : ℝ) * Real.pi) := by
    rw [Real.log_exp]
  have hcos :
      Real.cos
          (Real.log (Real.exp (-(Real.pi / 2 + (n : ℝ) * Real.pi)))) = 0 := by
    have hcos' : Real.cos (Real.pi / 2 + n * Real.pi) = 0 := by
      rw [Real.cos_add_nat_mul_pi, Real.cos_pi_div_two]
      simp
    rw [hlog, Real.cos_neg]
    simpa [add_comm, add_left_comm, add_assoc, mul_comm] using hcos'
  rw [hcos]
  ring

/-- Helper for Exercise 3.1.2: the oscillatory complex coefficients satisfy the one-step
generalized-binomial recurrence after separating the `(-1)^n` sign. -/
private theorem oscillatoryCoeffComplex_step (n : ℕ) :
    oscillatoryCoeffComplex (n + 1) =
      ((((n : ℂ) - ((2 : ℂ) + Complex.I)) / (n + 1 : ℂ)) * oscillatoryCoeffComplex n) := by
  -- Clear the factorial denominator through the descending-Pochhammer recurrence for `choose`.
  have hrec :
      (n + 1 : ℂ) * Ring.choose ((2 : ℂ) + Complex.I) (n + 1) =
        (((2 : ℂ) + Complex.I) - n) * Ring.choose ((2 : ℂ) + Complex.I) n := by
    have hdesc :=
      congrArg (fun p : Polynomial ℤ ↦ p.smeval ((2 : ℂ) + Complex.I))
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
  -- Route correction: prove the `choose` recurrence once, then rewrite the signed coefficient.
  calc
    oscillatoryCoeffComplex (n + 1)
        = Ring.choose ((2 : ℂ) + Complex.I) (n + 1) * ((-1 : ℂ) ^ (n + 1)) := by
            simp [oscillatoryCoeffComplex]
    _ = (Ring.choose ((2 : ℂ) + Complex.I) (n + 1) * (-1 : ℂ)) * (-1 : ℂ) ^ n := by
          rw [pow_succ]
          ring
    _ = ((((n : ℂ) - ((2 : ℂ) + Complex.I)) / (n + 1 : ℂ)) *
          Ring.choose ((2 : ℂ) + Complex.I) n) * (-1 : ℂ) ^ n := by
          have hchoose :
              Ring.choose ((2 : ℂ) + Complex.I) (n + 1) =
                ((((2 : ℂ) + Complex.I) - n) / (n + 1 : ℂ)) *
                  Ring.choose ((2 : ℂ) + Complex.I) n := by
            apply_fun (fun z : ℂ ↦ z * (n + 1 : ℂ)) using mul_left_injective₀ hsucc
            field_simp [hsucc]
            simpa [mul_assoc, mul_left_comm, mul_comm] using hrec
          rw [hchoose]
          ring
    _ = (((n : ℂ) - ((2 : ℂ) + Complex.I)) / (n + 1 : ℂ)) * oscillatoryCoeffComplex n := by
          rw [oscillatoryCoeffComplex]
          ring

/-- Helper for Exercise 3.1.2: for `n ≥ 2`, the oscillatory coefficient ratio is bounded by
`(n - 1) / (n + 1)` in norm. -/
private theorem oscillatoryCoeffComplex_norm_step_bound {n : ℕ} (hn : 2 ≤ n) :
    ‖oscillatoryCoeffComplex (n + 1)‖ ≤
      ((n - 1 : ℝ) / (n + 1)) * ‖oscillatoryCoeffComplex n‖ := by
  -- The multiplier is `((n - 2) - I)/(n + 1)`, whose norm is at most `(n - 1)/(n + 1)`.
  rw [oscillatoryCoeffComplex_step, norm_mul, norm_div]
  have hden : ‖((n + 1 : ℂ))‖ = n + 1 := by
    simpa using (Complex.norm_natCast (n + 1))
  rw [hden]
  have hnum :
      ‖(n : ℂ) - ((2 : ℂ) + Complex.I)‖ ≤ n - 1 := by
    calc
      ‖(n : ℂ) - ((2 : ℂ) + Complex.I)‖
          = ‖(((n - 2 : ℤ) : ℂ) - Complex.I)‖ := by
              congr 1
              norm_num
              simp [sub_eq_add_neg, add_comm, add_left_comm]
      _ ≤ ‖((n - 2 : ℤ) : ℂ)‖ + ‖Complex.I‖ := by
            simpa using norm_sub_le (((n - 2 : ℤ) : ℂ)) Complex.I
      _ = (n - 2 : ℝ) + 1 := by
            have hnonneg : (0 : ℤ) ≤ n - 2 := by omega
            rw [Complex.norm_int_of_nonneg hnonneg]
            norm_num
      _ = n - 1 := by ring
  have hfac_nonneg : 0 ≤ ‖oscillatoryCoeffComplex n‖ := norm_nonneg _
  have hmul :
      ‖(n : ℂ) - ((2 : ℂ) + Complex.I)‖ * ‖oscillatoryCoeffComplex n‖ / (n + 1) ≤
        ((n - 1 : ℝ) / (n + 1)) * ‖oscillatoryCoeffComplex n‖ := by
    have hden_pos : (0 : ℝ) < n + 1 := by positivity
    have hdiv :
        ‖(n : ℂ) - ((2 : ℂ) + Complex.I)‖ / (n + 1) ≤ ((n - 1 : ℝ) / (n + 1)) := by
      exact div_le_div_of_nonneg_right hnum hden_pos.le
    have hmul' := mul_le_mul_of_nonneg_right hdiv hfac_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul'
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Exercise 3.1.2: the comparison constant used to dominate the oscillatory
coefficients by a quadratic tail. -/
private noncomputable def oscillatoryCoeffBoundConstant : ℝ :=
  2 * ‖oscillatoryCoeffComplex 2‖

/-- Helper for Exercise 3.1.2: the comparison constant for the oscillatory coefficients is
nonnegative. -/
private theorem oscillatoryCoeffBoundConstant_nonneg : 0 ≤ oscillatoryCoeffBoundConstant := by
  dsimp [oscillatoryCoeffBoundConstant]
  positivity

/-- Helper for Exercise 3.1.2: the complex oscillatory coefficients satisfy a `1 / (n(n+1))`
tail bound. -/
private theorem oscillatoryCoeffComplex_tail_bound (m : ℕ) :
    ‖oscillatoryCoeffComplex (m + 2)‖ ≤
      oscillatoryCoeffBoundConstant / ((m + 2 : ℝ) * (m + 1 : ℝ)) := by
  induction m with
  | zero =>
      dsimp [oscillatoryCoeffBoundConstant]
      nlinarith [norm_nonneg (oscillatoryCoeffComplex 2)]
  | succ m ih =>
      have hstep :
          ‖oscillatoryCoeffComplex (m + 3)‖ ≤
            ((m + 1 : ℝ) / (m + 3)) * ‖oscillatoryCoeffComplex (m + 2)‖ := by
        have hstep' := oscillatoryCoeffComplex_norm_step_bound (n := m + 2) (by omega)
        norm_num [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] at hstep'
        exact hstep'
      have hmul :
          ((m + 1 : ℝ) / (m + 3)) * ‖oscillatoryCoeffComplex (m + 2)‖ ≤
            ((m + 1 : ℝ) / (m + 3)) *
              (oscillatoryCoeffBoundConstant / ((m + 2 : ℝ) * (m + 1 : ℝ))) := by
        exact mul_le_mul_of_nonneg_left ih (by positivity)
      have hboundSucc :
          ‖oscillatoryCoeffComplex (m + 3)‖ ≤
            oscillatoryCoeffBoundConstant / ((m + 3 : ℝ) * (m + 2 : ℝ)) := by
        calc
          ‖oscillatoryCoeffComplex (m + 3)‖
              ≤ ((m + 1 : ℝ) / (m + 3)) * ‖oscillatoryCoeffComplex (m + 2)‖ := hstep
          _ ≤ ((m + 1 : ℝ) / (m + 3)) *
                (oscillatoryCoeffBoundConstant / ((m + 2 : ℝ) * (m + 1 : ℝ))) := hmul
          _ = oscillatoryCoeffBoundConstant / ((m + 3 : ℝ) * (m + 2 : ℝ)) := by
                have hm1_pos : (0 : ℝ) < m + 1 := by positivity
                have hm2_pos : (0 : ℝ) < m + 2 := by positivity
                have hm3_pos : (0 : ℝ) < m + 3 := by positivity
                field_simp [hm1_pos.ne', hm2_pos.ne', hm3_pos.ne']
      convert hboundSucc using 1
      have hm2_pos : (0 : ℝ) < m + 2 := by positivity
      have hm3_pos : (0 : ℝ) < m + 3 := by positivity
      field_simp [hm2_pos.ne', hm3_pos.ne']
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 3.1.2: the real oscillatory coefficients satisfy a quadratic tail bound. -/
private theorem oscillatoryCoeff_tail_square_bound (m : ℕ) :
    |oscillatoryCoeff (m + 2)| ≤ oscillatoryCoeffBoundConstant / ((m + 1 : ℝ) ^ (2 : ℕ)) := by
  have hre :
      |oscillatoryCoeff (m + 2)| ≤ ‖oscillatoryCoeffComplex (m + 2)‖ := by
    simpa [oscillatoryCoeff] using Complex.abs_re_le_norm (oscillatoryCoeffComplex (m + 2))
  have hprod := oscillatoryCoeffComplex_tail_bound m
  have hdiv :
      oscillatoryCoeffBoundConstant / ((m + 2 : ℝ) * (m + 1 : ℝ)) ≤
        oscillatoryCoeffBoundConstant / ((m + 1 : ℝ) ^ (2 : ℕ)) := by
    have hden : ((m + 1 : ℝ) ^ (2 : ℕ)) ≤ (m + 2 : ℝ) * (m + 1 : ℝ) := by
      nlinarith
    have hm1_sq_pos : (0 : ℝ) < (m + 1 : ℝ) ^ (2 : ℕ) := by positivity
    have hInv :
        ((m + 2 : ℝ) * (m + 1 : ℝ))⁻¹ ≤ ((m + 1 : ℝ) ^ (2 : ℕ))⁻¹ := by
      exact (inv_le_inv₀ (by positivity) hm1_sq_pos).2 hden
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hInv oscillatoryCoeffBoundConstant_nonneg
  exact hre.trans (hprod.trans hdiv)

/-- Helper for Exercise 3.1.2: the oscillatory coefficients are absolutely summable. -/
private theorem oscillatoryCoeffBoundModelSummable :
    Summable
      (fun m : ℕ ↦ oscillatoryCoeffBoundConstant / ((m + 1 : ℝ) ^ (2 : ℕ))) := by
  have hbase : Summable (fun n : ℕ ↦ (((n : ℝ) ^ (2 : ℕ))⁻¹ : ℝ)) := by
    exact Real.summable_nat_pow_inv.mpr (by norm_num)
  have hshift : Summable (fun m : ℕ ↦ ((((m + 1 : ℕ) : ℝ) ^ (2 : ℕ))⁻¹ : ℝ)) := by
    exact (_root_.summable_nat_add_iff 1).2 hbase
  simpa [div_eq_mul_inv] using Summable.mul_left oscillatoryCoeffBoundConstant hshift

/-- Helper for Exercise 3.1.2: the oscillatory coefficients are absolutely summable. -/
private theorem oscillatoryCoeffSummable : Summable (fun n : ℕ ↦ |oscillatoryCoeff n|) := by
  have htail :
      Summable (fun m : ℕ ↦ |oscillatoryCoeff (m + 2)|) := by
    refine oscillatoryCoeffBoundModelSummable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) ?_
    intro m
    exact oscillatoryCoeff_tail_square_bound m
  have htail' : Summable (fun m : ℕ ↦ (fun n : ℕ ↦ |oscillatoryCoeff n|) (m + 2)) := by
    simpa using htail
  exact (_root_.summable_nat_add_iff 2).1 htail'

/-- Helper for Exercise 3.1.2: the explicit zero sequence approaches `1` from the left. -/
private theorem samplingPointValue_tendsto_left :
    Tendsto samplingPointValue atTop (nhdsWithin (1 : ℝ) (Set.Iio 1)) := by
  have hr : |Real.exp (-Real.pi)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hpow : Tendsto (fun n : ℕ ↦ Real.exp (-Real.pi) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  have hscaled :
      Tendsto (fun n : ℕ ↦ Real.exp (-(Real.pi / 2)) * Real.exp (-Real.pi) ^ n) atTop (nhds 0) := by
    simpa using hpow.const_mul (Real.exp (-(Real.pi / 2)))
  have hToOne : Tendsto samplingPointValue atTop (nhds (1 : ℝ)) := by
    have hToOneRaw :
        Tendsto
          (fun n : ℕ ↦ 1 - (Real.exp (-(Real.pi / 2)) * Real.exp (-Real.pi) ^ n))
          atTop (nhds (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub hscaled
    convert hToOneRaw using 1
    ext n
    rw [samplingPointValue]
    congr 1
    rw [show -(Real.pi / 2 + (n : ℝ) * Real.pi) = -(Real.pi / 2) + (n : ℝ) * (-Real.pi) by ring]
    rw [Real.exp_add, Real.exp_nat_mul]
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within samplingPointValue hToOne <|
    Filter.Eventually.of_forall fun n ↦ (samplingPointValue_mem n).2

/-- Helper for Exercise 3.1.2: the oscillatory coefficients have total sum `0`. -/
private theorem oscillatoryCoeff_tsum_zero : ∑' n : ℕ, oscillatoryCoeff n = 0 := by
  have hsummable : Summable (fun n : ℕ ↦ oscillatoryCoeff n) :=
    oscillatoryCoeffSummable.of_abs
  have hAbel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hsummable.hasSum.tendsto_sum_nat
  have hzeroSeq :
      Tendsto
        (fun n : ℕ ↦ ∑' k : ℕ, oscillatoryCoeff k * samplingPointValue n ^ k)
        atTop
        (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with n
    have hz0 : 0 < samplingPointValue n := (samplingPointValue_mem n).1
    have hz1 : samplingPointValue n < 1 := (samplingPointValue_mem n).2
    have hclosed :=
      oscillatorySeries_eq_closedForm (z := samplingPointValue n) hz0 hz1
    have hvanish :
        (1 - samplingPointValue n) ^ (2 : ℕ) *
            Real.cos (Real.log (1 - samplingPointValue n)) = 0 := by
      simpa [samplingPoint, samplingPointValue] using samplingPoint_closedForm_eq_zero n
    exact (hclosed.trans hvanish).symm
  exact tendsto_nhds_unique (hAbel.comp samplingPointValue_tendsto_left) hzeroSeq

/-- Helper for Exercise 3.1.2: the total variation of the oscillatory coefficient sequence. -/
private noncomputable def oscillatoryVariation : ℝ :=
  ∑' n : ℕ, |oscillatoryCoeff n|

/-- Helper for Exercise 3.1.2: the oscillatory variation is strictly positive. -/
private theorem oscillatoryVariation_pos : 0 < oscillatoryVariation := by
  have hone : 1 = Finset.sum ({0} : Finset ℕ) (fun i ↦ |oscillatoryCoeff i|) := by
    simp [oscillatoryCoeff, oscillatoryCoeffComplex]
  have hle : 1 ≤ oscillatoryVariation := by
    calc
      1 = Finset.sum ({0} : Finset ℕ) (fun i ↦ |oscillatoryCoeff i|) := hone
      _ ≤ ∑' n : ℕ, |oscillatoryCoeff n| := by
            exact oscillatoryCoeffSummable.sum_le_tsum {0} fun _ _ ↦ abs_nonneg _
      _ = oscillatoryVariation := rfl
  have hzero_lt_one : (0 : ℝ) < 1 := by norm_num
  exact lt_of_lt_of_le hzero_lt_one hle

/-- Helper for Exercise 3.1.2: the normalized positive part of the oscillatory
coefficient at `n`. -/
private noncomputable def oscillatoryPositiveWeight (n : ℕ) : ℝ :=
  (|oscillatoryCoeff n| + oscillatoryCoeff n) / oscillatoryVariation

/-- Helper for Exercise 3.1.2: the normalized negative part of the oscillatory
coefficient at `n`. -/
private noncomputable def oscillatoryNegativeWeight (n : ℕ) : ℝ :=
  (|oscillatoryCoeff n| - oscillatoryCoeff n) / oscillatoryVariation

/-- Helper for Exercise 3.1.2: the positive normalized oscillatory weights are nonnegative. -/
private theorem oscillatoryPositiveWeight_nonneg (n : ℕ) : 0 ≤ oscillatoryPositiveWeight n := by
  have hnum : 0 ≤ |oscillatoryCoeff n| + oscillatoryCoeff n := by
    linarith [neg_le_abs (oscillatoryCoeff n)]
  exact div_nonneg hnum oscillatoryVariation_pos.le

/-- Helper for Exercise 3.1.2: the negative normalized oscillatory weights are nonnegative. -/
private theorem oscillatoryNegativeWeight_nonneg (n : ℕ) : 0 ≤ oscillatoryNegativeWeight n := by
  have hnum : 0 ≤ |oscillatoryCoeff n| - oscillatoryCoeff n := by
    linarith [le_abs_self (oscillatoryCoeff n)]
  exact div_nonneg hnum oscillatoryVariation_pos.le

/-- Helper for Exercise 3.1.2: the positive normalized oscillatory weights sum to `1`. -/
private theorem oscillatoryPositiveWeight_hasSum :
    HasSum (fun n : ℕ ↦ oscillatoryPositiveWeight n) 1 := by
  have hcoeff :
      HasSum (fun n : ℕ ↦ oscillatoryCoeff n) 0 := by
    simpa [oscillatoryCoeff_tsum_zero] using (oscillatoryCoeffSummable.of_abs.hasSum)
  have hsum := (oscillatoryCoeffSummable.hasSum.add hcoeff).div_const oscillatoryVariation
  have hsum' :
      HasSum
        (fun n : ℕ ↦ oscillatoryPositiveWeight n)
        (oscillatoryVariation / oscillatoryVariation) := by
    simpa [oscillatoryPositiveWeight] using hsum
  simpa [oscillatoryVariation_pos.ne'] using hsum'

/-- Helper for Exercise 3.1.2: the negative normalized oscillatory weights sum to `1`. -/
private theorem oscillatoryNegativeWeight_hasSum :
    HasSum (fun n : ℕ ↦ oscillatoryNegativeWeight n) 1 := by
  have hcoeff :
      HasSum (fun n : ℕ ↦ oscillatoryCoeff n) 0 := by
    simpa [oscillatoryCoeff_tsum_zero] using (oscillatoryCoeffSummable.of_abs.hasSum)
  have hsum := (oscillatoryCoeffSummable.hasSum.sub hcoeff).div_const oscillatoryVariation
  have hsum' :
      HasSum
        (fun n : ℕ ↦ oscillatoryNegativeWeight n)
        (oscillatoryVariation / oscillatoryVariation) := by
    simpa [oscillatoryNegativeWeight, sub_eq_add_neg] using hsum
  simpa [oscillatoryVariation_pos.ne'] using hsum'

/-- Helper for Exercise 3.1.2: the PMF obtained from the positive oscillatory weights. -/
private noncomputable def oscillatoryPositivePMF : PMF ℕ :=
  ⟨fun n ↦ ENNReal.ofReal (oscillatoryPositiveWeight n), by
    apply ENNReal.hasSum_coe.mpr
    simpa using oscillatoryPositiveWeight_hasSum.toNNReal oscillatoryPositiveWeight_nonneg⟩

/-- Helper for Exercise 3.1.2: the PMF obtained from the negative oscillatory weights. -/
private noncomputable def oscillatoryNegativePMF : PMF ℕ :=
  ⟨fun n ↦ ENNReal.ofReal (oscillatoryNegativeWeight n), by
    apply ENNReal.hasSum_coe.mpr
    simpa using oscillatoryNegativeWeight_hasSum.toNNReal oscillatoryNegativeWeight_nonneg⟩

/-- Helper for Exercise 3.1.2: the positive oscillatory PMF evaluates to its defining weight. -/
@[simp] private theorem oscillatoryPositivePMF_apply (n : ℕ) :
    oscillatoryPositivePMF n = ENNReal.ofReal (oscillatoryPositiveWeight n) := rfl

/-- Helper for Exercise 3.1.2: the negative oscillatory PMF evaluates to its defining weight. -/
@[simp] private theorem oscillatoryNegativePMF_apply (n : ℕ) :
    oscillatoryNegativePMF n = ENNReal.ofReal (oscillatoryNegativeWeight n) := rfl

/-- Helper for Exercise 3.1.2: the pgf of the positive oscillatory PMF is its defining series. -/
private theorem oscillatoryPositivePMF_pgf (x : ℝ) :
    probabilityGeneratingFunctionReal oscillatoryPositivePMF x =
      ∑' n : ℕ, oscillatoryPositiveWeight n * x ^ n := by
  rw [probabilityGeneratingFunctionReal_apply]
  congr with n
  rw [oscillatoryPositivePMF_apply]
  rw [ENNReal.toReal_ofReal (oscillatoryPositiveWeight_nonneg n)]

/-- Helper for Exercise 3.1.2: the pgf of the negative oscillatory PMF is its defining series. -/
private theorem oscillatoryNegativePMF_pgf (x : ℝ) :
    probabilityGeneratingFunctionReal oscillatoryNegativePMF x =
      ∑' n : ℕ, oscillatoryNegativeWeight n * x ^ n := by
  rw [probabilityGeneratingFunctionReal_apply]
  congr with n
  rw [oscillatoryNegativePMF_apply]
  rw [ENNReal.toReal_ofReal (oscillatoryNegativeWeight_nonneg n)]

/-- Helper for Exercise 3.1.2: the absolute-value part of the scaled oscillatory series remains
summable on `[0,1]`. -/
private theorem oscillatoryAbsScaledSeriesSummable {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Summable (fun n : ℕ ↦ (|oscillatoryCoeff n| / oscillatoryVariation) * x ^ n) := by
  refine Summable.of_nonneg_of_le ?_ ?_
    (oscillatoryCoeffSummable.div_const oscillatoryVariation)
  · intro n
    exact mul_nonneg (div_nonneg (abs_nonneg _) oscillatoryVariation_pos.le) (pow_nonneg hx0 _)
  · intro n
    exact mul_le_of_le_one_right (div_nonneg (abs_nonneg _) oscillatoryVariation_pos.le)
      (pow_le_one₀ hx0 hx1)

/-- Helper for Exercise 3.1.2: the unscaled oscillatory series remains summable on `[0,1]`. -/
private theorem oscillatorySeriesSummable {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Summable (fun n : ℕ ↦ oscillatoryCoeff n * x ^ n) := by
  apply Summable.of_abs
  refine Summable.of_nonneg_of_le (fun n ↦ abs_nonneg _) ?_ oscillatoryCoeffSummable
  intro n
  simpa [abs_mul, abs_of_nonneg (pow_nonneg hx0 _)] using
    mul_le_of_le_one_right (abs_nonneg (oscillatoryCoeff n)) (pow_le_one₀ hx0 hx1)

/-- Helper for Exercise 3.1.2: the scaled oscillatory series itself remains summable on `[0,1]`. -/
private theorem oscillatoryScaledSeriesSummable {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Summable (fun n : ℕ ↦ (oscillatoryCoeff n / oscillatoryVariation) * x ^ n) := by
  apply Summable.of_abs
  simpa [abs_mul, abs_div, abs_of_nonneg (pow_nonneg hx0 _),
    abs_of_pos oscillatoryVariation_pos] using
      oscillatoryAbsScaledSeriesSummable hx0 hx1

-- Proof sketch: choose two explicit `ℕ`-valued laws whose generating functions have radius of
-- convergence exactly `1`, and use a standard analytic construction so that their difference has
-- infinitely many zeros accumulating only at the boundary point `1`.
/-- Exercise 3.1.2: There exist two distinct real-valued probability generating functions that
agree on an injective sequence of points in `(0,1)`, showing that the extra hypothesis
`ψ z < ∞` for some `z > 1` in Theorem 3.2 (iii) cannot be omitted. -/
theorem distinct_probabilityGeneratingFunctions_agree_on_countably_many_points :
    ∃ p q : PMF ℕ,
      probabilityGeneratingFunctionReal p ≠ probabilityGeneratingFunctionReal q ∧
        ProbabilityGeneratingFunctionsAgreeOnInjectiveSequence p q := by
  refine ⟨oscillatoryPositivePMF, oscillatoryNegativePMF, ?_, ?_⟩
  · intro hEq
    have hzero := congrFun hEq 0
    have hpos :
        probabilityGeneratingFunctionReal oscillatoryPositivePMF 0 =
          2 / oscillatoryVariation := by
      rw [oscillatoryPositivePMF_pgf, tsum_eq_single 0]
      · simp [oscillatoryPositiveWeight, oscillatoryCoeff, oscillatoryCoeffComplex,
          oscillatoryVariation_pos.ne']
        norm_num
      · intro n hn
        simp [hn]
    have hneg :
        probabilityGeneratingFunctionReal oscillatoryNegativePMF 0 = 0 := by
      rw [oscillatoryNegativePMF_pgf, tsum_eq_single 0]
      · simp [oscillatoryNegativeWeight, oscillatoryCoeff, oscillatoryCoeffComplex]
      · intro n hn
        simp [hn]
    have hneq : (2 : ℝ) / oscillatoryVariation ≠ 0 :=
      div_ne_zero (by norm_num) oscillatoryVariation_pos.ne'
    exact hneq <| by simpa [hpos, hneg] using hzero
  · refine ⟨samplingPoint, samplingPoint_injective, ?_⟩
    intro n
    let x : ℝ := samplingPoint n
    have hx0 : 0 ≤ x := le_of_lt (samplingPoint n).2.1
    have hx1 : x ≤ 1 := le_of_lt (samplingPoint n).2.2
    have hAbsSumm := oscillatoryAbsScaledSeriesSummable hx0 hx1
    have hOscSumm := oscillatoryScaledSeriesSummable hx0 hx1
    have hSeriesSumm := oscillatorySeriesSummable hx0 hx1
    have hSeriesZero :
        ∑' k : ℕ, oscillatoryCoeff k * x ^ k = 0 := by
      have hclosed :=
        oscillatorySeries_eq_closedForm (z := x) (samplingPoint n).2.1 (samplingPoint n).2.2
      have hvanish :
          (1 - x) ^ (2 : ℕ) * Real.cos (Real.log (1 - x)) = 0 := by
        simpa [x] using samplingPoint_closedForm_eq_zero n
      exact hclosed.trans hvanish
    have hScaledZero :
        ∑' k : ℕ, (oscillatoryCoeff k / oscillatoryVariation) * x ^ k = 0 := by
      have hSeriesHasSum :
          HasSum (fun k : ℕ ↦ oscillatoryCoeff k * x ^ k) 0 := by
        simpa [hSeriesZero] using hSeriesSumm.hasSum
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (hSeriesHasSum.div_const oscillatoryVariation).tsum_eq
    calc
      probabilityGeneratingFunctionReal oscillatoryPositivePMF x
          =
            ∑' k : ℕ,
              ((|oscillatoryCoeff k| + oscillatoryCoeff k) / oscillatoryVariation) * x ^ k :=
            by simpa [oscillatoryPositiveWeight] using oscillatoryPositivePMF_pgf x
      _ = ∑' k : ℕ,
            ((|oscillatoryCoeff k| / oscillatoryVariation) * x ^ k +
              (oscillatoryCoeff k / oscillatoryVariation) * x ^ k) := by
            have hsplit :
                ∀ i : ℕ,
                  ((|oscillatoryCoeff i| + oscillatoryCoeff i) / oscillatoryVariation) * x ^ i =
                    (|oscillatoryCoeff i| / oscillatoryVariation) * x ^ i +
                      (oscillatoryCoeff i / oscillatoryVariation) * x ^ i := by
              intro i
              ring
            simpa using tsum_congr hsplit
      _ =
            ∑' k : ℕ, (|oscillatoryCoeff k| / oscillatoryVariation) * x ^ k
              + ∑' k : ℕ, (oscillatoryCoeff k / oscillatoryVariation) * x ^ k :=
            hAbsSumm.tsum_add hOscSumm
      _ = ∑' k : ℕ, (|oscillatoryCoeff k| / oscillatoryVariation) * x ^ k := by
            rw [hScaledZero, add_zero]
      _ = ∑' k : ℕ, (|oscillatoryCoeff k| / oscillatoryVariation) * x ^ k -
            ∑' k : ℕ, (oscillatoryCoeff k / oscillatoryVariation) * x ^ k := by
            rw [hScaledZero, sub_zero]
      _ = ∑' k : ℕ,
            ((|oscillatoryCoeff k| / oscillatoryVariation) * x ^ k -
              (oscillatoryCoeff k / oscillatoryVariation) * x ^ k) := by
            rw [hAbsSumm.tsum_sub hOscSumm]
      _ =
            ∑' k : ℕ,
              ((|oscillatoryCoeff k| - oscillatoryCoeff k) / oscillatoryVariation) * x ^ k := by
            have hsplit :
                ∀ i : ℕ,
                  (|oscillatoryCoeff i| / oscillatoryVariation) * x ^ i -
                      (oscillatoryCoeff i / oscillatoryVariation) * x ^ i =
                    ((|oscillatoryCoeff i| - oscillatoryCoeff i) / oscillatoryVariation) *
                      x ^ i := by
              intro i
              ring
            simpa using tsum_congr hsplit
      _ = probabilityGeneratingFunctionReal oscillatoryNegativePMF x := by
            simpa [oscillatoryNegativeWeight] using (oscillatoryNegativePMF_pgf x).symm
