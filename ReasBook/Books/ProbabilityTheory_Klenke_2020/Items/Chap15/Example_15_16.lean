/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open MeasureTheory

noncomputable section

/-- Helper for Example 15.16: the cosine Dirichlet series at exponent `2` is the quadratic
Bernoulli polynomial on `[0, 1]`. -/
private theorem cosineSquareSeries_hasSum {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * x))
      (Real.pi ^ 2 * (x ^ 2 - x + 1 / 6)) := by
  -- Proof comment: specialize the zeta-value cosine-series formula at `k = 1`, then simplify the
  -- Bernoulli polynomial `B₂(x) = x² - x + 1 / 6`.
  have hraw :
      HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * x))
        (((-1 : ℝ) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1) / 2 / ((2 * 1).factorial : ℝ)) *
          Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2))) := by
    simpa using (hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx)
  have hBernoulli :
      x ^ 2 - x + 1 / 6 =
        Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2)) := by
      simpa [bernoulliFun] using (bernoulliFun_two x).symm
  have hsumm :
      Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * x)) := hraw.summable
  refine hsumm.hasSum_iff.mpr ?_
  calc
    ∑' n : ℕ, 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * x)
        =
          (((-1 : ℝ) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1) / 2 / ((2 * 1).factorial : ℝ)) *
            Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2))) :=
          hraw.tsum_eq
    _ = Real.pi ^ 2 * (x ^ 2 - x + 1 / 6) := by
        rw [← hBernoulli]
        ring

/-- Helper for Example 15.16: the odd positive masses `4 / (π² n²)` sum to `1 / 2`. -/
private theorem oddNatSquareMassReal_hasSum :
    HasSum (fun n : ℕ => if Odd n then 4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) else 0) (1 / 2 : ℝ) := by
  -- Route correction: instead of splitting the Basel series into even and odd tails directly,
  -- compare the cosine series at `x = 0` and `x = 1 / 2`; their difference isolates the odd
  -- coefficients in one step.
  have hzero :
      HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * (0 : ℝ)))
        (Real.pi ^ 2 * (0 ^ 2 - 0 + 1 / 6)) :=
    cosineSquareSeries_hasSum (x := 0) (by simp)
  have hhalf :
      HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * (1 / 2 : ℝ)))
        (Real.pi ^ 2 * ((1 / 2 : ℝ) ^ 2 - 1 / 2 + 1 / 6)) :=
    cosineSquareSeries_hasSum (x := 1 / 2) (by constructor <;> norm_num)
  convert (hzero.sub hhalf).mul_left (2 / Real.pi ^ 2) using 1
  · ext n
    by_cases hn : Odd n
    · -- Proof comment: on odd indices the cosine difference is `1 - (-1) = 2`.
      have hcos0 : Real.cos (2 * Real.pi * n * (0 : ℝ)) = 1 := by simp
      have hcos : Real.cos (2 * Real.pi * n * (1 / 2 : ℝ)) = -1 := by
        calc
          Real.cos (2 * Real.pi * n * (1 / 2 : ℝ)) = Real.cos (n * Real.pi) := by ring_nf
          _ = (-1 : ℝ) ^ n := Real.cos_nat_mul_pi n
          _ = -1 := hn.neg_one_pow
      have hnz : (n : ℝ) ≠ 0 := by
        intro hn0
        have : n = 0 := by exact_mod_cast hn0
        simp [this] at hn
      have hn0 : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hnz
      rw [if_pos hn, hcos0, hcos]
      field_simp [Real.pi_ne_zero, hn0]
      ring
    · -- Proof comment: on even indices the cosine difference is `1 - 1 = 0`.
      have hcos0 : Real.cos (2 * Real.pi * n * (0 : ℝ)) = 1 := by simp
      have hcos : Real.cos (2 * Real.pi * n * (1 / 2 : ℝ)) = 1 := by
        have hEven : Even n := Nat.not_odd_iff_even.mp hn
        calc
          Real.cos (2 * Real.pi * n * (1 / 2 : ℝ)) = Real.cos (n * Real.pi) := by ring_nf
          _ = (-1 : ℝ) ^ n := Real.cos_nat_mul_pi n
          _ = 1 := hEven.neg_one_pow
      rw [if_neg hn, hcos0, hcos]
      ring
  · -- Proof comment: the two Bernoulli evaluations differ by exactly `π² / 4`.
    norm_num
    field_simp [Real.pi_ne_zero]
    ring

/-- Helper for Example 15.16: the real odd-square coefficients on `ℤ` sum to `1`. -/
private theorem oddSquareMassReal_hasSum :
    HasSum (fun x : ℤ => if Odd x then 4 / (Real.pi ^ 2 * (x : ℝ) ^ 2) else 0) 1 := by
  -- Proof comment: the coefficient function is even on `ℤ`, so the positive and negative
  -- branches contribute the same sum and the value at `0` vanishes.
  let f : ℤ → ℝ := fun x ↦ if Odd x then 4 / (Real.pi ^ 2 * (x : ℝ) ^ 2) else 0
  have hnat : HasSum (fun n : ℕ ↦ f n) (1 / 2 : ℝ) := by
    simpa [f] using oddNatSquareMassReal_hasSum
  have hneg : HasSum (fun n : ℕ ↦ f (-n)) (1 / 2 : ℝ) := by
    -- Proof comment: negating an integer preserves oddness and the square in the denominator.
    convert oddNatSquareMassReal_hasSum using 1
    ext n
    simp [f, odd_neg]
  have hf0 : f 0 = 0 := by simp [f]
  have hsum : HasSum f ((1 / 2 : ℝ) + 1 / 2 - f 0) := HasSum.of_nat_of_neg hnat hneg
  have hsum' : HasSum f 1 := by
    convert hsum using 0
    norm_num [hf0]
  simpa [f] using hsum'

/-- Helper for Example 15.16: the explicit odd-square masses are nonnegative. -/
private theorem oddSquareMassReal_nonneg (x : ℤ) :
    0 ≤ if Odd x then 4 / (Real.pi ^ 2 * (x : ℝ) ^ 2) else 0 := by
  -- Proof comment: an odd integer is nonzero, so the denominator is a positive square.
  by_cases hx : Odd x
  · have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hsq : 0 < (x : ℝ) ^ 2 := by
      exact sq_pos_of_ne_zero (by exact_mod_cast hx0)
    rw [if_pos hx]
    exact div_nonneg (by positivity) (le_of_lt (mul_pos (sq_pos_of_ne_zero Real.pi_ne_zero) hsq))
  · simp [hx]

-- Proof sketch: split the series over odd and even integers, rewrite the odd part as the classical
-- Basel-type sum over `(2n + 1)⁻²`, and use `∑' n, 8 / (π^2 * (2n + 1)^2) = 1`.
private theorem oddSquarePMF_hasSum :
    HasSum (fun x : ℤ ↦ ENNReal.ofReal
      (if Odd x then 4 / (Real.pi ^ 2 * (x : ℝ) ^ 2) else 0)) 1 := by
  -- Proof comment: the real normalization transfers to `ENNReal` because every mass is
  -- nonnegative.
  apply ENNReal.hasSum_coe.mpr
  rw [← Real.toNNReal_one]
  exact oddSquareMassReal_hasSum.toNNReal oddSquareMassReal_nonneg

/-- The probability mass function on `ℤ` whose odd masses are proportional to `x⁻²` and whose
even masses vanish. -/
def oddSquarePMF : PMF ℤ :=
  ⟨fun x ↦ ENNReal.ofReal
      (if Odd x then 4 / (Real.pi ^ 2 * (x : ℝ) ^ 2) else 0),
    oddSquarePMF_hasSum⟩

-- Proof sketch: unfold `oddSquarePMF`; the singleton masses are definitionally
-- the odd-square formula used to build the PMF.
/-- The masses of `oddSquarePMF` are `4 / (π^2 x^2)` on odd integers and `0` on even integers. -/
theorem oddSquarePMF_apply (x : ℤ) :
    oddSquarePMF x = ENNReal.ofReal (if Odd x then 4 / (Real.pi ^ 2 * (x : ℝ) ^ 2) else 0) := rfl

/-- The `2π`-periodic tent function from Example 15.16, written using reduction to the
fundamental domain `[-π, π)`. -/
def periodicTentFunction (t : ℝ) : ℝ :=
  1 - 2 * |toIcoMod Real.two_pi_pos (-Real.pi) t| / Real.pi

-- Proof sketch: reduce `t + 2π` and `t` to `[-π, π)` using the periodicity of `toIcoMod` with
-- period `2π`, then unfold `periodicTentFunction`.
/-- The tent function of Example 15.16 is `2π`-periodic. -/
theorem periodicTentFunction_periodic : Function.Periodic periodicTentFunction (2 * Real.pi) :=
  by
  intro t
  -- Proof comment: `toIcoMod` is already `2π`-periodic, so the tent profile inherits that
  -- periodicity immediately.
  rw [periodicTentFunction, periodicTentFunction, toIcoMod_periodic Real.two_pi_pos (-Real.pi) t]

-- Proof sketch: if `t ∈ [-π, π)`, then `toIcoMod Real.two_pi_pos (-π) t = t`; substitute this into
-- the definition of `periodicTentFunction`.
/-- On the fundamental interval `[-π, π)`, the periodic tent function is `t ↦ 1 - 2 |t| / π`. -/
theorem periodicTentFunction_eq_on_fundamentalDomain {t : ℝ}
    (ht : t ∈ Set.Ico (-Real.pi) Real.pi) :
    periodicTentFunction t = 1 - 2 * |t| / Real.pi := by
  -- Proof comment: on the fundamental interval, `toIcoMod` fixes the point.
  have ht' : t ∈ Set.Ico (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    refine ⟨ht.1, ?_⟩
    linarith [ht.2]
  rw [periodicTentFunction, (toIcoMod_eq_self Real.two_pi_pos).2 ht']

/-- Helper for Example 15.16: the real masses of `oddSquarePMF` are the odd-square coefficients. -/
private theorem oddSquarePMF_toReal_apply (x : ℤ) :
    (oddSquarePMF x).toReal = if Odd x then 4 / (Real.pi ^ 2 * (x : ℝ) ^ 2) else 0 := by
  -- Proof comment: `oddSquarePMF` was defined from the explicit odd-square masses, so only the
  -- nonnegativity needed for `ENNReal.toReal_ofReal` remains.
  rw [oddSquarePMF_apply]
  exact ENNReal.toReal_ofReal (oddSquareMassReal_nonneg x)

/-- Helper for Example 15.16: the odd-square coefficients are symmetric under `x ↦ -x`. -/
private theorem oddSquarePMF_toReal_neg (x : ℤ) :
    (oddSquarePMF (-x)).toReal = (oddSquarePMF x).toReal := by
  -- Proof comment: oddness is invariant under negation, and the coefficient only depends on the
  -- square of the integer.
  rw [oddSquarePMF_toReal_apply, oddSquarePMF_toReal_apply]
  by_cases hx : Odd x
  · simp [hx, odd_neg]
  · simp [hx, odd_neg]

/-- Helper for Example 15.16: the pushed-forward odd-square PMF has the expected Fourier series
expansion. -/
private theorem charFunIntCastMap_eq_tsum (t : ℝ) :
    charFun (oddSquarePMF.toMeasure.map fun x : ℤ ↦ (x : ℝ)) t =
      ∑' n : ℤ, (((oddSquarePMF n).toReal : ℂ) * Complex.exp ((t * (n : ℝ)) * Complex.I)) := by
  -- Proof comment: first pull the real-valued characteristic-function integral back through the
  -- map `ℤ → ℝ`, then expand the discrete `PMF` integral as a `tsum` of singleton masses.
  rw [MeasureTheory.charFun_apply_real]
  rw [integral_map ((measurable_of_countable ((↑) : ℤ → ℝ)).aemeasurable) (by fun_prop)]
  have hInt :
      Integrable (fun n : ℤ ↦ Complex.exp ((t * (n : ℝ)) * Complex.I)) oddSquarePMF.toMeasure := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards with n
    simpa using
      (show ‖Complex.exp (((t * (n : ℝ)) : ℝ) * Complex.I)‖ ≤ (1 : ℝ) from
        le_of_eq (Complex.norm_exp_ofReal_mul_I (t * (n : ℝ))))
  simpa [Measure.real, Complex.real_smul] using
    (PMF.integral_eq_tsum oddSquarePMF
      (fun n : ℤ ↦ Complex.exp ((t * (n : ℝ)) * Complex.I)) hInt)

/-- Helper for Example 15.16: the odd-square characteristic function is `2π`-periodic. -/
private theorem charFunOddSquarePMF_periodic :
    Function.Periodic
      (fun t ↦ charFun (oddSquarePMF.toMeasure.map fun x : ℤ ↦ (x : ℝ)) t)
      (2 * Real.pi) := by
  -- Proof comment: after expanding the characteristic function as an integer Fourier series, the
  -- shift by `2π` contributes the factor `exp (n * 2π i) = 1` to each summand.
  intro t
  change charFun (oddSquarePMF.toMeasure.map fun x : ℤ ↦ (x : ℝ)) (t + 2 * Real.pi) =
    charFun (oddSquarePMF.toMeasure.map fun x : ℤ ↦ (x : ℝ)) t
  rw [charFunIntCastMap_eq_tsum, charFunIntCastMap_eq_tsum]
  refine tsum_congr fun n ↦ ?_
  have hexp :
      Complex.exp (↑(t + 2 * Real.pi) * (n : ℂ) * Complex.I) =
        Complex.exp (↑t * (n : ℂ) * Complex.I) := by
    calc
      Complex.exp (↑(t + 2 * Real.pi) * (n : ℂ) * Complex.I) =
          Complex.exp (↑t * (n : ℂ) * Complex.I + ((n : ℤ) * (2 * Real.pi * Complex.I))) := by
            congr 1
            calc
              ↑(t + 2 * Real.pi) * (n : ℂ) * Complex.I =
                  (↑t + 2 * ↑Real.pi) * (n : ℂ) * Complex.I := by norm_num
              _ = ↑t * (n : ℂ) * Complex.I + 2 * ↑Real.pi * (n : ℂ) * Complex.I := by ring
              _ = ↑t * (n : ℂ) * Complex.I + ((n : ℤ) * (2 * Real.pi * Complex.I)) := by ring
      _ = Complex.exp (↑t * (n : ℂ) * Complex.I) *
          Complex.exp ((n : ℤ) * (2 * Real.pi * Complex.I)) := by
            rw [Complex.exp_add]
      _ = Complex.exp (↑t * (n : ℂ) * Complex.I) := by
            rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simpa using congrArg (fun z ↦ (((oddSquarePMF n).toReal : ℂ) * z)) hexp

/-- Helper for Example 15.16: pairing the `n` and `-n` Fourier terms produces one cosine
coefficient. -/
private theorem oddSquareFourierPair_eq_cos (t : ℝ) (n : ℕ) :
    (((oddSquarePMF n).toReal : ℂ) * Complex.exp ((t * (n : ℝ)) * Complex.I) +
        (((oddSquarePMF (-n)).toReal : ℂ) * Complex.exp ((t * (-(n : ℤ) : ℝ)) * Complex.I))) =
      (((if Odd n then 8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.cos ((n : ℝ) * t) else 0 : ℝ)) :
        ℂ) := by
  -- Proof comment: the masses are symmetric under `n ↦ -n`, so the exponential pair collapses to
  -- the standard `2 cos` expression.
  rw [oddSquarePMF_toReal_neg (x := (n : ℤ))]
  have hpair :
      Complex.exp ((t * (n : ℝ)) * Complex.I) +
          Complex.exp ((t * (-(n : ℤ) : ℝ)) * Complex.I) =
        (((2 * Real.cos ((n : ℝ) * t) : ℝ)) : ℂ) := by
    have hfirst : (t * (n : ℝ)) * Complex.I = ((n : ℝ) * t) * Complex.I := by ring
    have hsecond : (t * (-(n : ℤ) : ℝ)) * Complex.I = -((t * (n : ℝ)) * Complex.I) := by
      calc
        (t * (-(n : ℤ) : ℝ)) * Complex.I = (t * (-(n : ℝ))) * Complex.I := by norm_num
        _ = (-(t * (n : ℝ))) * Complex.I := by ring
        _ = -((t * (n : ℝ)) * Complex.I) := by ring
    have hnegfirst : -((t * (n : ℝ)) * Complex.I) = -(((n : ℝ) * t) * Complex.I) := by
      rw [hfirst]
    have hnegmul : -(((n : ℝ) * t) * Complex.I) = (-((n : ℝ) * t)) * Complex.I := by
      ring
    calc
      Complex.exp ((t * (n : ℝ)) * Complex.I) + Complex.exp ((t * (-(n : ℤ) : ℝ)) * Complex.I) =
          Complex.exp (((n : ℝ) * t) * Complex.I) + Complex.exp ((-((n : ℝ) * t)) * Complex.I) := by
            rw [hfirst, hsecond, hnegfirst, hnegmul]
      _ = 2 * Complex.cos ((n : ℝ) * t) := (Complex.two_cos ((n : ℝ) * t)).symm
      _ = (((2 * Real.cos ((n : ℝ) * t) : ℝ)) : ℂ) := by
            simp [Complex.ofReal_cos]
  by_cases hn : Odd n
  · have hcoeff :
        ((oddSquarePMF n).toReal : ℂ) =
          (((4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) : ℝ)) : ℂ) := by
        simp [oddSquarePMF_toReal_apply, hn]
    rw [hcoeff]
    calc
      (((4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) : ℝ)) : ℂ) * Complex.exp ((t * (n : ℝ)) * Complex.I) +
          (((4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) : ℝ)) : ℂ) *
            Complex.exp ((t * (-(n : ℤ) : ℝ)) * Complex.I) =
        (((4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) : ℝ)) : ℂ) *
          (Complex.exp ((t * (n : ℝ)) * Complex.I) +
            Complex.exp ((t * (-(n : ℤ) : ℝ)) * Complex.I)) := by
          ring
      _ =
          (((4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) : ℝ)) : ℂ) *
            ((((2 * Real.cos ((n : ℝ) * t) : ℝ)) : ℂ)) := by
          rw [hpair]
      _ = (((8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.cos ((n : ℝ) * t) : ℝ)) : ℂ) := by
          simp
          ring
      _ = (((if Odd n then 8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.cos ((n : ℝ) * t) else
            0 : ℝ)) : ℂ) := by
          simp [hn]
  · have hcoeff : ((oddSquarePMF n).toReal : ℂ) = 0 := by
      simp [oddSquarePMF_toReal_apply, hn]
    rw [hcoeff]
    simp [hn]

/-- Helper for Example 15.16: the odd-square characteristic function equals the odd cosine
series. -/
private theorem charFunIntCastMap_eq_oddCosineSeries (t : ℝ) :
    charFun (oddSquarePMF.toMeasure.map fun x : ℤ ↦ (x : ℝ)) t =
      (((∑' n : ℕ, if Odd n then 8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.cos ((n : ℝ) * t) else
          0 : ℝ)) : ℂ) := by
  -- Route correction: normalize the symmetric `ℤ`-indexed exponential series first, so the
  -- closing argument can use the real cosine series API directly.
  let f : ℤ → ℂ := fun n ↦
    (((oddSquarePMF n).toReal : ℂ) * Complex.exp ((t * (n : ℝ)) * Complex.I))
  have hcoeff :
      Summable (fun n : ℤ ↦ (oddSquarePMF n).toReal) := by
    simpa [oddSquarePMF_toReal_apply] using oddSquareMassReal_hasSum.summable
  have hf : Summable f := by
    refine Summable.of_norm_bounded hcoeff ?_
    intro n
    have hnonneg : 0 ≤ (oddSquarePMF n).toReal := by
      simpa [oddSquarePMF_toReal_apply] using oddSquareMassReal_nonneg n
    dsimp [f]
    have hexp : ‖Complex.exp (↑t * ↑n * Complex.I)‖ = 1 := by
      simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (t * (n : ℝ))
    rw [norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_eq_abs]
    simp [abs_of_nonneg hnonneg]
  have hzero : f 0 = 0 := by
    simp [f, oddSquarePMF_toReal_apply]
  rw [charFunIntCastMap_eq_tsum]
  calc
    ∑' n : ℤ, (((oddSquarePMF n).toReal : ℂ) * Complex.exp ((t * (n : ℝ)) * Complex.I)) =
        ∑' n : ℕ, (f n + f (-n)) := by
          have htsum := tsum_nat_add_neg hf
          rw [hzero, add_zero] at htsum
          simpa [f] using htsum.symm
    _ = ∑' n : ℕ, (((if Odd n then 8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.cos ((n : ℝ) * t) else
          0 : ℝ)) : ℂ) := by
          refine tsum_congr fun n ↦ ?_
          simpa [f] using oddSquareFourierPair_eq_cos t n
    _ = (((∑' n : ℕ, if Odd n then 8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.cos ((n : ℝ) * t) else
          0 : ℝ)) : ℂ) := by
          rw [← Complex.ofReal_tsum]

/-- Helper for Example 15.16: on `[-π, π)`, the odd cosine series equals the affine tent profile.
-/
private theorem oddCosineSeries_eq_tent_on_fundamentalDomain {t : ℝ}
    (ht : t ∈ Set.Ico (-Real.pi) Real.pi) :
    (∑' n : ℕ, if Odd n then 8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.cos ((n : ℝ) * t) else 0) =
      1 - 2 * |t| / Real.pi := by
  -- Proof comment: subtract the full cosine-square series at `|t| / (2π)` and at the `1 / 2`
  -- translate; the difference kills the even modes and keeps the odd ones.
  let x : ℝ := |t| / (2 * Real.pi)
  let y : ℝ := x + 1 / 2
  have habs : |t| ≤ Real.pi := by
    exact abs_le.mpr ⟨ht.1, le_of_lt ht.2⟩
  have hx_le_half : x ≤ 1 / 2 := by
    have hdiv : |t| / (2 * Real.pi) ≤ Real.pi / (2 * Real.pi) :=
      div_le_div_of_nonneg_right habs (le_of_lt Real.two_pi_pos)
    have hhalf : Real.pi / (2 * Real.pi) = (1 / 2 : ℝ) := by
      field_simp [Real.pi_ne_zero]
    simpa [x, hhalf] using hdiv
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    linarith
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    dsimp [y]
    linarith
  have hxsum := cosineSquareSeries_hasSum (x := x) hx
  have hysum := cosineSquareSeries_hasSum (x := y) hy
  have hsum :
      HasSum (fun n : ℕ =>
        if Odd n then 8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.cos ((n : ℝ) * t) else 0)
        (1 - 2 * |t| / Real.pi) := by
    convert (hxsum.sub hysum).mul_left (4 / Real.pi ^ 2) using 1
    · ext n
      have hcosAbs : Real.cos ((n : ℝ) * |t|) = Real.cos ((n : ℝ) * t) := by
        calc
          Real.cos ((n : ℝ) * |t|) = Real.cos |(n : ℝ) * t| := by
            rw [abs_mul, abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)]
          _ = Real.cos ((n : ℝ) * t) := by rw [Real.cos_abs]
      have hcosx : Real.cos (2 * Real.pi * n * x) = Real.cos ((n : ℝ) * t) := by
        calc
          Real.cos (2 * Real.pi * n * x) = Real.cos ((n : ℝ) * |t|) := by
            dsimp [x]
            congr 1
            field_simp [Real.pi_ne_zero]
          _ = Real.cos ((n : ℝ) * t) := hcosAbs
      have hcosy : Real.cos (2 * Real.pi * n * y) = (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * t) := by
        calc
          Real.cos (2 * Real.pi * n * y) = Real.cos ((n : ℝ) * |t| + n * Real.pi) := by
            dsimp [y, x]
            congr 1
            field_simp [Real.pi_ne_zero]
          _ = (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * |t|) := Real.cos_add_nat_mul_pi _ n
          _ = (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * t) := by rw [hcosAbs]
      by_cases hn : Odd n
      · rw [if_pos hn, hcosx, hcosy, hn.neg_one_pow]
        ring
      · have hEven : Even n := Nat.not_odd_iff_even.mp hn
        rw [if_neg hn, hcosx, hcosy, hEven.neg_one_pow]
        ring
    · dsimp [x, y]
      field_simp [Real.pi_ne_zero]
      ring
  exact hsum.tsum_eq

/-- Helper for Example 15.16: on `[-π, π)`, the odd-square characteristic function collapses to the
affine tent formula. -/
private theorem charFunOddSquarePMF_eq_on_fundamentalDomain {t : ℝ}
    (ht : t ∈ Set.Ico (-Real.pi) Real.pi) :
    charFun (oddSquarePMF.toMeasure.map fun x : ℤ ↦ (x : ℝ)) t =
      (1 - 2 * |t| / Real.pi : ℂ) := by
  -- Proof comment: the new bridge lemma puts the characteristic function into the same odd cosine
  -- normal form as the real tent-series computation.
  simpa [oddCosineSeries_eq_tent_on_fundamentalDomain ht] using
    charFunIntCastMap_eq_oddCosineSeries t

-- Proof sketch: apply the discrete Fourier inversion formula on `ℤ` to the periodic tent function,
-- compute the singleton masses by partial integration, and identify the resulting probability law
-- with the pushforward of `oddSquarePMF.toMeasure` along `ℤ → ℝ`.
/-- Example 15.16: the `2π`-periodic tent function is the characteristic function of the
probability measure on `ℤ` with masses `4 / (π^2 x^2)` on odd integers and `0` on even integers. -/
theorem periodicTentFunction_eq_charFun_oddSquarePMF (t : ℝ) :
    charFun (oddSquarePMF.toMeasure.map fun x : ℤ ↦ (x : ℝ)) t =
      (periodicTentFunction t : ℂ) := by
  -- Proof comment: write `t` as its `[-π, π)` representative plus an integral multiple of `2π`,
  -- then apply the fundamental-domain identity and transport it back by periodicity.
  set u : ℝ := toIcoMod Real.two_pi_pos (-Real.pi) t with hu_def
  have hu' : u ∈ Set.Ico (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    simpa [hu_def] using toIcoMod_mem_Ico Real.two_pi_pos (-Real.pi) t
  have hu : u ∈ Set.Ico (-Real.pi) Real.pi := by
    refine ⟨hu'.1, ?_⟩
    have hupper : u < -Real.pi + 2 * Real.pi := hu'.2
    linarith
  rcases ((toIcoMod_eq_iff Real.two_pi_pos).1 hu_def.symm) with ⟨_, ⟨z, hz⟩⟩
  rw [hz]
  calc
    charFun (oddSquarePMF.toMeasure.map fun x : ℤ ↦ (x : ℝ)) (u + z • (2 * Real.pi)) =
        charFun (oddSquarePMF.toMeasure.map fun x : ℤ ↦ (x : ℝ)) u := by
          simpa using (charFunOddSquarePMF_periodic.zsmul z) u
    _ = (1 - 2 * |u| / Real.pi : ℂ) := charFunOddSquarePMF_eq_on_fundamentalDomain hu
    _ = (periodicTentFunction u : ℂ) := by
          norm_num [periodicTentFunction_eq_on_fundamentalDomain hu]
    _ = (periodicTentFunction (u + z • (2 * Real.pi)) : ℂ) := by
          symm
          simpa using congrArg (fun r : ℝ ↦ (r : ℂ)) ((periodicTentFunction_periodic.zsmul z) u)
