/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Topology

/-- The positive-frequency cosine mode in the half-range Fourier expansion of `1_[0,t]`. -/
def indicator_Icc_zero_t_fourier_cosine_mode (t x : ℝ) (n : ℕ+) : ℝ :=
  (2 * Real.sin ((n : ℝ) * Real.pi * t)) / ((n : ℝ) * Real.pi) *
    Real.cos ((n : ℝ) * Real.pi * x)

/-- The Fourier-cosine term sequence whose sum recovers the indicator of `[0, t]` away from the
jump point. The zeroth term is the constant mode `t`, and the positive terms come from
`indicator_Icc_zero_t_fourier_cosine_mode`. -/
def indicator_Icc_zero_t_fourier_term (t x : ℝ) : ℕ → ℝ
  | 0 => t
  | n + 1 => indicator_Icc_zero_t_fourier_cosine_mode t x ⟨n + 1, Nat.succ_pos _⟩

/-- Helper for Exercise 21.5.6: the ordered partial sums of the Fourier-cosine series for
`1_[0,t]`, indexed by the upper summation bound `N`. -/
def indicator_Icc_zero_t_fourier_partialSum (t x : ℝ) (N : ℕ) : ℝ :=
  Finset.sum (Finset.range (N + 1)) fun n ↦ indicator_Icc_zero_t_fourier_term t x n

@[simp] theorem indicator_Icc_zero_t_fourier_term_zero (t x : ℝ) :
    indicator_Icc_zero_t_fourier_term t x 0 = t :=
  rfl

@[simp] theorem indicator_Icc_zero_t_fourier_term_succ_eq_mode (t x : ℝ) (n : ℕ) :
    indicator_Icc_zero_t_fourier_term t x (n + 1) =
      indicator_Icc_zero_t_fourier_cosine_mode t x ⟨n + 1, Nat.succ_pos _⟩ :=
  rfl

-- Proof sketch: unfold the definition of `indicator_Icc_zero_t_fourier_term`; at index `n + 1`
-- it is exactly the positive-mode cosine coefficient from the exercise statement.
/-- The positive Fourier modes of `indicator_Icc_zero_t_fourier_term` are the cosine coefficients
`2 sin((n + 1)π t) / ((n + 1)π)`. -/
theorem indicator_Icc_zero_t_fourier_term_succ (t x : ℝ) (n : ℕ) :
    indicator_Icc_zero_t_fourier_term t x (n + 1) =
      (2 * Real.sin ((n + 1 : ℝ) * Real.pi * t)) / ((n + 1 : ℝ) * Real.pi) *
        Real.cos ((n + 1 : ℝ) * Real.pi * x) := by
  simp [indicator_Icc_zero_t_fourier_cosine_mode]

/-- Helper for Exercise 21.5.6: unit-modulus geometric partial sums with ratio `q ≠ 1` are
uniformly bounded by `2 / ‖1 - q‖`. -/
lemma normSumRangePowSucc_le_two_div_norm_one_sub {q : ℂ} (hq_norm : ‖q‖ = 1) (hq_ne : q ≠ 1)
    (N : ℕ) :
    ‖∑ i ∈ Finset.range N, q ^ (i + 1)‖ ≤ 2 / ‖1 - q‖ := by
  -- Pull out one factor of `q` so the remaining sum is the standard geometric series.
  have hshift : ∑ i ∈ Finset.range N, q ^ (i + 1) = q * ∑ i ∈ Finset.range N, q ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [pow_succ']
  have hgeom : ∑ i ∈ Finset.range N, q ^ i = (q ^ N - 1) / (q - 1) := geom_sum_eq hq_ne N
  have hpow_norm : ‖q ^ N‖ = 1 := by
    rw [Complex.norm_pow, hq_norm, one_pow]
  have hnum : ‖q ^ N - 1‖ ≤ 2 := by
    calc
      ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hpow_norm, norm_one]; norm_num
  calc
    ‖∑ i ∈ Finset.range N, q ^ (i + 1)‖ = ‖q‖ * ‖∑ i ∈ Finset.range N, q ^ i‖ := by
      rw [hshift, Complex.norm_mul]
    _ = ‖(q ^ N - 1) / (q - 1)‖ := by rw [hq_norm, one_mul, hgeom]
    _ = ‖q ^ N - 1‖ / ‖q - 1‖ := by rw [Complex.norm_div]
    _ ≤ 2 / ‖q - 1‖ := by gcongr
    _ = 2 / ‖1 - q‖ := by rw [norm_sub_rev]

/-- Helper for Exercise 21.5.6: the half-angle `π y / 2` stays in `(0, π)` when `y ∈ (0, 2)`. -/
lemma piMulHalf_mem_Ioo {y : ℝ} (hy : y ∈ Set.Ioo 0 2) :
    Real.pi * y / 2 ∈ Set.Ioo (0 : ℝ) Real.pi := by
  -- The source interval `(0, 2)` scales into `(0, π)` because `π > 0`.
  constructor
  · nlinarith [hy.1, Real.pi_pos]
  · nlinarith [hy.2, Real.pi_pos]

/-- Helper for Exercise 21.5.6: the radial factor in the boundary-value factorization is positive
on `(0, 2)`. -/
lemma twoSin_piMulHalf_pos {y : ℝ} (hy : y ∈ Set.Ioo 0 2) :
    0 < 2 * Real.sin (Real.pi * y / 2) := by
  -- The half-angle lies in `(0, π)`, so the sine factor is strictly positive.
  have hy' : Real.pi * y / 2 ∈ Set.Ioo (0 : ℝ) Real.pi := piMulHalf_mem_Ioo hy
  have hsin : 0 < Real.sin (Real.pi * y / 2) := Real.sin_pos_of_mem_Ioo hy'
  linarith

/-- Helper for Exercise 21.5.6: the target argument lies in the principal interval `(-π, π]`. -/
lemma piMulHalf_sub_piDivTwo_mem_Ioc {y : ℝ} (hy : y ∈ Set.Ioo 0 2) :
    Real.pi * y / 2 - Real.pi / 2 ∈ Set.Ioc (-Real.pi) Real.pi := by
  -- The lower bound is equivalent to `0 ≤ π y / 2`, and the upper bound follows from `y < 2`.
  constructor
  · have hy0 : 0 ≤ y := hy.1.le
    nlinarith [Real.pi_pos]
  · nlinarith [hy.2, Real.pi_pos]

/-- Helper for Exercise 21.5.6: the target argument also matches the interval spelling required by
`toIocMod_eq_self`. -/
lemma piMulHalf_sub_piDivTwo_mem_Ioc_periodic {y : ℝ} (hy : y ∈ Set.Ioo 0 2) :
    Real.pi * y / 2 - Real.pi / 2 ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
  -- This is the same principal-interval fact, rewritten with endpoint `-π + 2π`.
  simpa [sub_eq_add_neg, two_mul, add_assoc, add_left_comm] using
    piMulHalf_sub_piDivTwo_mem_Ioc hy

/-- Helper for Exercise 21.5.6: the `(n + 1)`st sine coefficient is the imaginary part of the
matching complex exponential harmonic term. -/
lemma sinNatSuccDivNatSucc_eq_imExponentialTerm (y : ℝ) (n : ℕ) :
    Complex.im (Complex.exp (Real.pi * y * Complex.I) ^ (n + 1) / (n + 1 : ℂ)) =
      Real.sin ((n + 1 : ℝ) * Real.pi * y) / (n + 1 : ℝ) := by
  -- Move the real denominator outside the imaginary-part map so the remaining term is a pure
  -- exponential on the unit circle.
  rw [div_eq_mul_inv,
    show ((n + 1 : ℂ)⁻¹) = (((n + 1 : ℝ)⁻¹ : ℝ) : ℂ) by simp,
    mul_comm, Complex.im_ofReal_mul]
  -- Rewrite the power as one exponential at frequency `(n + 1) π y`.
  rw [show Complex.exp (Real.pi * y * Complex.I) ^ (n + 1) =
      Complex.exp (((n + 1 : ℝ) * Real.pi * y) * Complex.I) by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Complex.exp_nat_mul (Real.pi * y * Complex.I) (n + 1)).symm]
  -- The imaginary part of `exp (θ I)` is exactly `sin θ`.
  rw [show (Complex.exp (((n + 1 : ℝ) * Real.pi * y) * Complex.I)).im =
      Real.sin ((n + 1 : ℝ) * Real.pi * y) by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        Complex.exp_ofReal_mul_I_im ((n + 1 : ℝ) * Real.pi * y)]
  ring

/-- Helper for Exercise 21.5.6: the real sine partial sums are the imaginary parts of the complex
harmonic partial sums divided by `π`. -/
lemma sinPartialSum_eq_im_complexExponentialHarmonic (y : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, Real.sin ((n + 1 : ℝ) * Real.pi * y) / ((n + 1 : ℝ) * Real.pi) =
      Complex.im (∑ n ∈ Finset.range (N + 1), Complex.exp (Real.pi * y * Complex.I) ^ n / (n : ℂ)) /
        Real.pi := by
  -- Peel off the zero term on the complex side; it vanishes because `1 / 0 = 0` in `ℂ`.
  have him :
      Complex.im
        (∑ n ∈ Finset.range (N + 1), Complex.exp (Real.pi * y * Complex.I) ^ n / (n : ℂ)) =
        ∑ n ∈ Finset.range N, Real.sin ((n + 1 : ℝ) * Real.pi * y) / (n + 1 : ℝ) := by
    rw [Finset.sum_range_succ']
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    -- Identify each summand with the previous helper and then sum termwise.
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sinNatSuccDivNatSucc_eq_imExponentialTerm]
  -- Divide the already-matched imaginary-part identity by `π` to recover the textbook scaling.
  have hdiv := congrArg (fun r : ℝ ↦ r / Real.pi) him.symm
  simpa [div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- Helper for Exercise 21.5.6: the real part of `1 - exp(x I)` is `1 - cos x`. -/
lemma oneSubExpOfRealMulI_re (x : ℝ) :
    Complex.re (1 - Complex.exp (x * Complex.I)) = 1 - Real.cos x := by
  -- Project to the real part and use the standard unit-circle exponential formula.
  simp [Complex.exp_ofReal_mul_I_re]

/-- Helper for Exercise 21.5.6: the imaginary part of `1 - exp(x I)` is `-sin x`. -/
lemma oneSubExpOfRealMulI_im (x : ℝ) :
    Complex.im (1 - Complex.exp (x * Complex.I)) = -Real.sin x := by
  -- Project to the imaginary part and use the standard unit-circle exponential formula.
  simp [Complex.exp_ofReal_mul_I_im]

/-- Helper for Exercise 21.5.6: `1 - exp(x I)` has the half-angle polar form needed for the
argument computation. -/
lemma oneSubExpOfRealMulI_eq_twoSinMulCosAddSin (x : ℝ) :
    1 - Complex.exp (x * Complex.I) =
      (((2 * Real.sin (x / 2) : ℝ) : ℂ)) *
        (Real.cos (x / 2 - Real.pi / 2) + Real.sin (x / 2 - Real.pi / 2) * Complex.I) := by
  -- Route correction: match real and imaginary parts separately instead of normalizing one large
  -- complex identity in a single cast-heavy step.
  refine Complex.ext ?_ ?_
  · -- The real parts both simplify to the half-angle formula for `1 - cos x`.
    rw [oneSubExpOfRealMulI_re]
    rw [Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
    have hx : x = 2 * (x / 2) := by
      ring
    rw [hx, Real.cos_two_mul_eq_one_sub]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, zero_mul, sub_zero, add_zero, mul_zero, zero_add]
    ring
  · -- The imaginary parts both simplify to the half-angle formula for `- sin x`.
    rw [oneSubExpOfRealMulI_im]
    rw [Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
    have hx : x = 2 * (x / 2) := by
      ring
    rw [hx, Real.sin_two_mul]
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, zero_mul, add_zero, mul_zero, zero_add]
    ring

/-- Helper for Exercise 21.5.6: `1 - exp(π y I)` already has the polar normal form needed by the
`Complex.arg` API. -/
lemma oneSubExpPiMulI_eq_twoSinMulCosAddSin (y : ℝ) :
    1 - Complex.exp (Real.pi * y * Complex.I) =
      (((2 * Real.sin (Real.pi * y / 2) : ℝ) : ℂ)) *
        (Real.cos (Real.pi * y / 2 - Real.pi / 2) +
          Real.sin (Real.pi * y / 2 - Real.pi / 2) * Complex.I) := by
  -- Specialize the general half-angle factorization to the `π y` phase used downstream.
  simpa [mul_assoc] using oneSubExpOfRealMulI_eq_twoSinMulCosAddSin (Real.pi * y)

/-- Helper for Exercise 21.5.6: the principal argument of `1 - exp(π y I)` on `(0, 2)` is the
expected half-angle `π y / 2 - π / 2`. -/
lemma arg_oneSubExpPiMulI {y : ℝ} (hy : y ∈ Set.Ioo 0 2) :
    Complex.arg (1 - Complex.exp (Real.pi * y * Complex.I)) = Real.pi * y / 2 - Real.pi / 2 := by
  -- Route correction: rewrite directly into the polar form consumed by the argument API.
  rw [oneSubExpPiMulI_eq_twoSinMulCosAddSin]
  -- The radius is positive and the angle already lies in the principal interval.
  simpa using
    Complex.arg_mul_cos_add_sin_mul_I (twoSin_piMulHalf_pos hy) (piMulHalf_sub_piDivTwo_mem_Ioc hy)

/-- Helper for Exercise 21.5.6: the shifted complex exponential harmonic series converges to the
boundary logarithm value on the unit circle. -/
lemma tendstoShiftedExponentialHarmonicSeries {y : ℝ} (hy : y ∈ Set.Ioo 0 2) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ∑ n ∈ Finset.range N,
          Complex.exp (Real.pi * y * Complex.I) ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
      Filter.atTop
      (nhds (-Complex.log (1 - Complex.exp (Real.pi * y * Complex.I)))) := by
  let q : ℂ := Complex.exp (Real.pi * y * Complex.I)
  let a : ℕ → ℂ := fun n ↦ q ^ (n + 1) / ((n + 1 : ℕ) : ℂ)
  have hq_norm : ‖q‖ = 1 := by
    simpa [q, mul_assoc, mul_left_comm, mul_comm] using Complex.norm_exp_I_mul_ofReal (y * Real.pi)
  have hone_sub_ne : 1 - q ≠ 0 := by
    -- The boundary point factors into a positive real radius times a nonzero point on the unit
    -- circle, so it cannot vanish.
    change 1 - Complex.exp (Real.pi * y * Complex.I) ≠ 0
    rw [oneSubExpPiMulI_eq_twoSinMulCosAddSin]
    refine mul_ne_zero ?_ ?_
    · exact Complex.ofReal_ne_zero.mpr (twoSin_piMulHalf_pos hy).ne'
    · intro hz
      have hphase :
          Complex.exp ((Real.pi * y / 2 - Real.pi / 2 : ℝ) * Complex.I) =
            Real.cos (Real.pi * y / 2 - Real.pi / 2) +
              Real.sin (Real.pi * y / 2 - Real.pi / 2) * Complex.I := by
        simpa using Complex.exp_ofReal_mul_I (Real.pi * y / 2 - Real.pi / 2)
      have harg :
          ((↑Real.pi * ↑y / 2 - ↑Real.pi / 2 : ℂ)) =
            (((Real.pi * y / 2 - Real.pi / 2 : ℝ)) : ℂ) := by
        simp
      have hargI :
          ((↑Real.pi * ↑y / 2 - ↑Real.pi / 2 : ℂ) * Complex.I) =
            ((((Real.pi * y / 2 - Real.pi / 2 : ℝ)) : ℂ) * Complex.I) := by
        rw [harg]
      have : Complex.exp ((Real.pi * y / 2 - Real.pi / 2) * Complex.I) = 0 := by
        rw [hargI, hphase]
        exact hz
      exact Complex.exp_ne_zero _ this
  have hq_ne : q ≠ 1 := by
    intro hq1
    apply hone_sub_ne
    simpa [hq1]
  have hanti : Antitone fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹) := by
    intro m n hmn
    have hmn' : (m + 1 : ℝ) ≤ n + 1 := by
      have hm : (m : ℝ) ≤ n := by exact_mod_cast hmn
      nlinarith
    simpa [one_div] using
      (one_div_le_one_div_of_le
      (by positivity : 0 < (m + 1 : ℝ))
      hmn')
  have hzero :
      Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹)) Filter.atTop (nhds 0) := by
    have hnat :
        Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [one_div] using tendsto_inv_atTop_zero.comp hnat
  have hcauchy_raw :
      CauchySeq
        (fun N : ℕ ↦
          ∑ n ∈ Finset.range N, ((n + 1 : ℝ)⁻¹) • q ^ (n + 1)) :=
    hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero
      (normSumRangePowSucc_le_two_div_norm_one_sub hq_norm hq_ne)
  have hcauchy :
      CauchySeq (fun N : ℕ ↦ ∑ n ∈ Finset.range N, a n) := by
    convert hcauchy_raw using 1
    funext N
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [a, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  have habel :
      Filter.Tendsto
        (fun x : ℝ ↦ ∑' n : ℕ, a n * (x : ℂ) ^ n)
        (𝓝[<] (1 : ℝ)) (nhds l) := by
    have habel' := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hl
    rw [Filter.tendsto_map'_iff] at habel'
    simpa using habel'
  let r : ℕ → ℝ := fun N ↦ 1 - 1 / (N + 2 : ℝ)
  have hr_to_one_real : Filter.Tendsto r Filter.atTop (nhds (1 : ℝ)) := by
    have hnat :
        Filter.Tendsto (fun n : ℕ ↦ ((n + 2 : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 2)
    simpa [r, sub_eq_add_neg] using
      (tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp hnat))
  have hr_tendsto :
      Filter.Tendsto r Filter.atTop (𝓝[<] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within r hr_to_one_real ?_
    exact Filter.Eventually.of_forall fun N ↦ by
      have : (0 : ℝ) < 1 / (N + 2 : ℝ) := by positivity
      simpa [r] using sub_lt_self (1 : ℝ) this
  have hpower :
      Filter.Tendsto (fun N : ℕ ↦ ∑' n : ℕ, a n * (r N : ℂ) ^ n) Filter.atTop (nhds l) :=
    habel.comp hr_tendsto
  have hcontinuous_ofReal : ContinuousAt (fun x : ℝ ↦ (x : ℂ)) 1 :=
    Complex.continuous_ofReal.continuousAt
  have hr_to_one :
      Filter.Tendsto (fun N : ℕ ↦ (r N : ℂ)) Filter.atTop (nhds (1 : ℂ)) :=
    hcontinuous_ofReal.tendsto.comp hr_to_one_real
  have hmul_limit :
      Filter.Tendsto
        (fun N : ℕ ↦ (r N : ℂ) * ∑' n : ℕ, a n * (r N : ℂ) ^ n)
        Filter.atTop (nhds l) := by
    simpa using hr_to_one.mul hpower
  have hslit : 1 - q ∈ Complex.slitPlane := by
    refine (Complex.mem_slitPlane_iff_arg).2 ?_
    constructor
    · rw [arg_oneSubExpPiMulI hy]
      nlinarith [hy.2, Real.pi_pos]
    · exact hone_sub_ne
  have hlog_limit :
      Filter.Tendsto
        (fun N : ℕ ↦ -Complex.log (1 - (r N : ℂ) * q))
        Filter.atTop
        (nhds (-Complex.log (1 - q))) := by
    -- The logarithm branch stays stable because the limiting boundary point lies in the slit plane.
    have hinside :
        Filter.Tendsto (fun N : ℕ ↦ 1 - (r N : ℂ) * q) Filter.atTop (nhds (1 - q)) := by
      simpa using tendsto_const_nhds.sub (hr_to_one.mul tendsto_const_nhds)
    exact (Filter.Tendsto.clog hinside hslit).neg
  have hmul_limit' :
      Filter.Tendsto
        (fun N : ℕ ↦ -Complex.log (1 - (r N : ℂ) * q))
        Filter.atTop (nhds l) := by
    convert hmul_limit using 1
    ext N
    have hr_pos : 0 < r N := by
      have hle : (1 : ℝ) / (N + 2 : ℝ) ≤ 1 / 2 := by
        have hden : (2 : ℝ) ≤ N + 2 := by
          have hN : (0 : ℝ) ≤ N := by positivity
          nlinarith
        exact one_div_le_one_div_of_le (by positivity) hden
      nlinarith [hle]
    have hr_ne : (r N : ℂ) ≠ 0 := by exact_mod_cast hr_pos.ne'
    have hr_lt : r N < 1 := by
      have hpos : (0 : ℝ) < 1 / (N + 2 : ℝ) := by positivity
      simpa [r] using sub_lt_self (1 : ℝ) hpos
    have hnorm : ‖((r N : ℂ) * q)‖ < 1 := by
      calc
        ‖((r N : ℂ) * q)‖ = ‖(r N : ℂ)‖ * ‖q‖ := by rw [Complex.norm_mul]
        _ = r N := by rw [hq_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
        _ < 1 := hr_lt
    have hs :
        HasSum (fun n : ℕ ↦ (((r N : ℂ) * q) ^ n) / (n : ℂ))
          (-Complex.log (1 - (r N : ℂ) * q)) :=
      Complex.hasSum_taylorSeries_neg_log hnorm
    have hs_shift :
        HasSum
          (fun n : ℕ ↦ (((r N : ℂ) * q) ^ (n + 1)) / ((n + 1 : ℕ) : ℂ))
          (-Complex.log (1 - (r N : ℂ) * q)) := by
      simpa using (hasSum_nat_add_iff' 1).mpr hs
    have hs_div :
        HasSum
          (fun n : ℕ ↦
            ((((r N : ℂ) * q) ^ (n + 1)) / ((n + 1 : ℕ) : ℂ)) / (r N : ℂ))
          ((-Complex.log (1 - (r N : ℂ) * q)) / (r N : ℂ)) :=
      hs_shift.div_const (r N : ℂ)
    have hs_a :
        HasSum
          (fun n : ℕ ↦ a n * (r N : ℂ) ^ n)
          ((-Complex.log (1 - (r N : ℂ) * q)) / (r N : ℂ)) := by
      convert hs_div using 1
      ext n
      have hn_ne : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      dsimp [a]
      field_simp [hr_ne, hn_ne]
      ring_nf
    rw [hs_a.tsum_eq]
    field_simp [hr_ne]
  have hl_eq :
      l = -Complex.log (1 - q) := tendsto_nhds_unique hmul_limit' hlog_limit
  change Filter.Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, a n) Filter.atTop
    (nhds (-Complex.log (1 - q)))
  exact hl_eq ▸ hl

theorem hasSumSinNatSuccMulPiDivNatSuccPi {y : ℝ} (hy : y ∈ Set.Ioo 0 2) :
      Filter.Tendsto
      (fun N : ℕ ↦
        Finset.sum (Finset.range N) fun n ↦
          Real.sin ((n + 1 : ℝ) * Real.pi * y) / ((n + 1 : ℝ) * Real.pi))
      Filter.atTop (nhds ((1 - y) / 2)) := by
  let q : ℂ := Complex.exp (Real.pi * y * Complex.I)
  have hcomplex := tendstoShiftedExponentialHarmonicSeries hy
  have him :
      Filter.Tendsto
        (fun N : ℕ ↦
          Complex.im (∑ n ∈ Finset.range N, q ^ (n + 1) / ((n + 1 : ℕ) : ℂ)))
        Filter.atTop
        (nhds (Complex.im (-Complex.log (1 - q)))) := by
    have him0 : ContinuousAt (fun z : ℂ ↦ Complex.im z) (-Complex.log (1 - q)) :=
      Complex.continuous_im.continuousAt
    exact him0.tendsto.comp hcomplex
  have hscaled :
      Filter.Tendsto
        (fun N : ℕ ↦
          Complex.im (∑ n ∈ Finset.range N, q ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) / Real.pi)
        Filter.atTop
        (nhds (Complex.im (-Complex.log (1 - q)) / Real.pi)) := by
    exact him.div tendsto_const_nhds Real.pi_ne_zero
  have hrewrite :
      (fun N : ℕ ↦
        ∑ n ∈ Finset.range N,
          Real.sin ((n + 1 : ℝ) * Real.pi * y) / ((n + 1 : ℝ) * Real.pi)) =
        (fun N : ℕ ↦
          Complex.im (∑ n ∈ Finset.range N, q ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) / Real.pi) := by
    funext N
    rw [sinPartialSum_eq_im_complexExponentialHarmonic]
    rw [Finset.sum_range_succ']
    simp [q]
  have hlimit :
      -(Complex.log (1 - q)).im / Real.pi = (1 - y) / 2 := by
    dsimp [q]
    rw [Complex.log_im, arg_oneSubExpPiMulI hy]
    calc
      -(Real.pi * y / 2 - Real.pi / 2) / Real.pi = (Real.pi * (1 - y) / 2) / Real.pi := by ring
      _ = (1 - y) / 2 := by field_simp [Real.pi_ne_zero]
  rw [hrewrite]
  simpa [Complex.neg_im, hlimit] using hscaled

/-- Helper for Exercise 21.5.6: each positive cosine Fourier mode splits into the sum of two sine
terms with arguments `t + x` and `t - x`. -/
theorem indicatorIccZeroTFourierTermSuccEqSinePair (t x : ℝ) (n : ℕ) :
    indicator_Icc_zero_t_fourier_term t x (n + 1) =
      Real.sin ((n + 1 : ℝ) * Real.pi * (t + x)) / ((n + 1 : ℝ) * Real.pi) +
        Real.sin ((n + 1 : ℝ) * Real.pi * (t - x)) / ((n + 1 : ℝ) * Real.pi) := by
  -- Rewrite the cosine coefficient with the product-to-sum identity and package the two angles as
  -- `(t + x)` and `(t - x)`.
  calc
    indicator_Icc_zero_t_fourier_term t x (n + 1)
        = (2 * Real.sin ((n + 1 : ℝ) * Real.pi * t) * Real.cos ((n + 1 : ℝ) * Real.pi * x)) /
            ((n + 1 : ℝ) * Real.pi) := by
              rw [indicator_Icc_zero_t_fourier_term_succ]
              ring
    _ =
        (Real.sin (((n + 1 : ℝ) * Real.pi * t) + ((n + 1 : ℝ) * Real.pi * x)) +
            Real.sin (((n + 1 : ℝ) * Real.pi * t) - ((n + 1 : ℝ) * Real.pi * x))) /
          ((n + 1 : ℝ) * Real.pi) := by
            rw [Real.two_mul_sin_mul_cos, add_comm]
    _ =
        Real.sin ((n + 1 : ℝ) * Real.pi * (t + x)) / ((n + 1 : ℝ) * Real.pi) +
          Real.sin ((n + 1 : ℝ) * Real.pi * (t - x)) / ((n + 1 : ℝ) * Real.pi) := by
            rw [add_div]
            congr 1 <;> ring_nf

/-- Helper for Exercise 21.5.6: when `x < t`, the ordered partial sums of the positive-frequency
tail converge to `1 - t`. -/
theorem indicatorIccZeroTFourierTailHasSumOfLt {t x : ℝ}
    (ht : t ∈ Set.Ioo 0 1) (hx : x ∈ Set.Ioo 0 1) (hxt : x < t) :
    Filter.Tendsto
      (fun N : ℕ ↦
        Finset.sum (Finset.range N) fun n ↦ indicator_Icc_zero_t_fourier_term t x (n + 1))
      Filter.atTop (nhds (1 - t)) := by
  -- The sine-pair decomposition turns the tail into two copies of the scalar sawtooth series.
  have htx_add : t + x ∈ Set.Ioo (0 : ℝ) 2 := by
    constructor <;> linarith [ht.1, ht.2, hx.1, hx.2]
  have htx_sub : t - x ∈ Set.Ioo (0 : ℝ) 2 := by
    constructor <;> linarith [ht.1, ht.2, hx.1, hx.2, hxt]
  have hplus := hasSumSinNatSuccMulPiDivNatSuccPi htx_add
  have hminus := hasSumSinNatSuccMulPiDivNatSuccPi htx_sub
  have hrewrite :
      (fun N : ℕ ↦
        ∑ n ∈ Finset.range N, indicator_Icc_zero_t_fourier_term t x (n + 1)) =
        (fun N : ℕ ↦
          (∑ n ∈ Finset.range N,
              Real.sin ((n + 1 : ℝ) * Real.pi * (t + x)) / ((n + 1 : ℝ) * Real.pi)) +
            ∑ n ∈ Finset.range N,
              Real.sin ((n + 1 : ℝ) * Real.pi * (t - x)) / ((n + 1 : ℝ) * Real.pi)) := by
    funext N
    simp_rw [indicatorIccZeroTFourierTermSuccEqSinePair]
    rw [Finset.sum_add_distrib]
  -- Add the two scalar limits and simplify the resulting affine expression.
  have hsum :
      Filter.Tendsto
        (fun N : ℕ ↦
          (∑ n ∈ Finset.range N,
              Real.sin ((n + 1 : ℝ) * Real.pi * (t + x)) / ((n + 1 : ℝ) * Real.pi)) +
            ∑ n ∈ Finset.range N,
              Real.sin ((n + 1 : ℝ) * Real.pi * (t - x)) / ((n + 1 : ℝ) * Real.pi))
        Filter.atTop
        (nhds (((1 - (t + x)) / 2) + ((1 - (t - x)) / 2))) :=
    hplus.add hminus
  rw [hrewrite]
  convert hsum using 1
  ring

/-- Helper for Exercise 21.5.6: when `t < x`, the ordered partial sums of the positive-frequency
tail converge to `-t`. -/
theorem indicatorIccZeroTFourierTailHasSumOfGt {t x : ℝ}
    (ht : t ∈ Set.Ioo 0 1) (hx : x ∈ Set.Ioo 0 1) (hxt : t < x) :
    Filter.Tendsto
      (fun N : ℕ ↦
        Finset.sum (Finset.range N) fun n ↦ indicator_Icc_zero_t_fourier_term t x (n + 1))
      Filter.atTop (nhds (-t)) := by
  -- The second sine term has negative argument, so rewrite it using `sin (-u) = -sin u`.
  have htx_add : t + x ∈ Set.Ioo (0 : ℝ) 2 := by
    constructor <;> linarith [ht.1, ht.2, hx.1, hx.2]
  have hxt_sub : x - t ∈ Set.Ioo (0 : ℝ) 2 := by
    constructor <;> linarith [ht.1, ht.2, hx.1, hx.2, hxt]
  have hplus := hasSumSinNatSuccMulPiDivNatSuccPi htx_add
  have hminus :
      Filter.Tendsto
        (fun N : ℕ ↦
          ∑ n ∈ Finset.range N,
            -(Real.sin ((n + 1 : ℝ) * Real.pi * (x - t)) / ((n + 1 : ℝ) * Real.pi)))
        Filter.atTop (nhds (-((1 - (x - t)) / 2))) := by
    simpa [Finset.sum_neg_distrib] using (hasSumSinNatSuccMulPiDivNatSuccPi hxt_sub).neg
  -- After the sign change, the two sawtooth limits collapse to `-t`.
  have hsum :
      Filter.Tendsto
        (fun N : ℕ ↦
          (∑ n ∈ Finset.range N,
              Real.sin ((n + 1 : ℝ) * Real.pi * (t + x)) / ((n + 1 : ℝ) * Real.pi)) +
            ∑ n ∈ Finset.range N,
              -(Real.sin ((n + 1 : ℝ) * Real.pi * (x - t)) / ((n + 1 : ℝ) * Real.pi)))
        Filter.atTop
        (nhds (((1 - (t + x)) / 2) + -((1 - (x - t)) / 2))) :=
    hplus.add hminus
  have hrewrite :
      (fun N : ℕ ↦
        ∑ n ∈ Finset.range N, indicator_Icc_zero_t_fourier_term t x (n + 1)) =
        (fun N : ℕ ↦
          (∑ n ∈ Finset.range N,
              Real.sin ((n + 1 : ℝ) * Real.pi * (t + x)) / ((n + 1 : ℝ) * Real.pi)) +
            ∑ n ∈ Finset.range N,
              -(Real.sin ((n + 1 : ℝ) * Real.pi * (x - t)) / ((n + 1 : ℝ) * Real.pi))) := by
    funext N
    simp_rw [indicatorIccZeroTFourierTermSuccEqSinePair]
    rw [Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [show ((n + 1 : ℝ) * Real.pi * (t - x)) = -((n + 1 : ℝ) * Real.pi * (x - t)) by ring,
      Real.sin_neg]
    ring
  rw [hrewrite]
  convert hsum using 1
  ring

-- Proof sketch: identify `indicator_Icc_zero_t_fourier_term t x` as the cosine Fourier series of
-- the step function `1_[0,t]`, use the classical pointwise convergence theorem for Fourier series
-- of piecewise smooth functions on `(0,1)`, and evaluate away from the jump point `x = t`.
-- Semantic recall: the source exercise asks for convergence of the ordered partial sums on `ℕ`,
-- not unconditional `HasSum`.
/-- Exercise 21.5.6: for `t ∈ (0, 1)` and `x ∈ (0, 1) \ {t}`, the ordered partial sums of the
Fourier-cosine series with zeroth term `t` and coefficients `2 sin(nπ t) / (nπ)` converge to the
indicator of `[0, t]` at `x`. -/
theorem indicator_Icc_zero_t_hasSum_fourier_cosine_series {t x : ℝ}
    (ht : t ∈ Set.Ioo 0 1) (hx : x ∈ Set.Ioo 0 1) (hxt : x ≠ t) :
    Filter.Tendsto (indicator_Icc_zero_t_fourier_partialSum t x) Filter.atTop
      (nhds ((Set.Icc 0 t).indicator (fun _ ↦ (1 : ℝ)) x)) := by
  -- Split the ordered partial sums into the constant zeroth mode `t` and the positive-frequency
  -- tail, then use the branch-specific tail limit depending on the order of `x` and `t`.
  have hsplit :
      indicator_Icc_zero_t_fourier_partialSum t x =
        fun N ↦
          t + ∑ n ∈ Finset.range N, indicator_Icc_zero_t_fourier_term t x (n + 1) := by
    funext N
    rw [indicator_Icc_zero_t_fourier_partialSum, Finset.sum_range_succ']
    simp [add_comm, add_left_comm, add_assoc]
  rcases lt_or_gt_of_ne hxt with hlt | hgt
  · have htail := indicatorIccZeroTFourierTailHasSumOfLt ht hx hlt
    have hx_mem : x ∈ Set.Icc (0 : ℝ) t := ⟨hx.1.le, hlt.le⟩
    -- In the `x < t` branch, the indicator equals `1`.
    have hind :
        (Set.Icc (0 : ℝ) t).indicator (fun _ ↦ (1 : ℝ)) x = 1 := by
      rw [Set.indicator_of_mem hx_mem]
    rw [hsplit]
    convert (tendsto_const_nhds.add htail) using 1
    simp [hind]
  · have htail := indicatorIccZeroTFourierTailHasSumOfGt ht hx hgt
    have hx_not_mem : x ∉ Set.Icc (0 : ℝ) t := by
      intro hx_mem
      exact not_lt_of_ge hx_mem.2 hgt
    -- In the `t < x` branch, the indicator vanishes.
    have hind :
        (Set.Icc (0 : ℝ) t).indicator (fun _ ↦ (1 : ℝ)) x = 0 := by
      rw [Set.indicator_of_notMem hx_not_mem]
    rw [hsplit]
    convert (tendsto_const_nhds.add htail) using 1
    simp [hind]
