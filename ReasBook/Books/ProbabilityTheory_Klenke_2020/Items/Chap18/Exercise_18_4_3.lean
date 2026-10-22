/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

-- Declarations for this item will be appended below by the statement pipeline.

open Real intervalIntegral MeasureTheory

noncomputable section

namespace Polynomial.Chebyshev

/-- The probability measure on `[-1, 1]` with density `(2 / π) * √(1 - x ^ 2)` with respect to
Lebesgue measure, expressed canonically as a reweighting of `measureT`. -/
noncomputable def measureU : Measure ℝ :=
  measureT.withDensity (fun x ↦ ENNReal.ofReal ((2 / π) * (1 - x ^ 2)))

-- Proof sketch: expand `measureU` as a weighted Lebesgue measure and then apply the substitution
-- `x = cos θ` on `[-1, 1]`, using `dx = - sin θ dθ` and `√(1 - cos θ ^ 2) = sin θ` for
-- `θ ∈ [0, π]`.
/-- Integrating against `measureU` is the same as integrating along `x = cos θ` on `[0, π]` with
weight `(2 / π) * sin θ ^ 2`. -/
theorem integral_measureU_eq_integral_cos {f : ℝ → ℝ} :
    ∫ x, f x ∂ measureU = ∫ θ in 0..π, f (cos θ) * ((2 / π) * sin θ ^ 2) := by
  -- First rewrite the weighted measure integral back over `measureT`.
  rw [measureU,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by filter_upwards with x; simp)]
  simp_rw [smul_eq_mul]
  -- Then use the existing `x = cos θ` substitution for `measureT`.
  rw [integral_measureT_eq_integral_cos]
  refine integral_congr ?_
  intro θ hθ
  have htrig : 1 - cos θ ^ 2 = sin θ ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq θ]
  have hnonneg : 0 ≤ (2 / π) * (1 - cos θ ^ 2) := by
    rw [htrig]
    positivity
  -- The density becomes `sin θ ^ 2` after the trigonometric normalization.
  change (ENNReal.ofReal ((2 / π) * (1 - cos θ ^ 2))).toReal * f (cos θ) =
    f (cos θ) * ((2 / π) * sin θ ^ 2)
  rw [ENNReal.toReal_ofReal hnonneg, htrig]
  ring

/-- Helper for Exercise 18.4.3: the interval integral of `cos (k * θ)` over `[0, π]` vanishes for
every nonzero integer frequency `k`. -/
lemma integral_cos_int_mul_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ θ in 0..π, Real.cos (k * θ) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hcomp :
      ∫ θ in 0..π, Real.cos (k * θ) = (k : ℝ)⁻¹ • ∫ θ in 0..(k : ℝ) * π, Real.cos θ := by
    simpa using (intervalIntegral.integral_comp_mul_left (f := Real.cos) (a := (0 : ℝ))
      (b := π) (c := (k : ℝ)) hk')
  -- Rescale the interval so that the primitive of `cos` can be evaluated at `k * π`.
  rw [hcomp, smul_eq_zero_iff_right (inv_ne_zero hk')]
  trans ∫ θ in 0..(k : ℝ) * π, (deriv sin) θ
  · refine integral_congr ?_
    intro x hx
    exact (congrFun deriv_sin x).symm
  by_cases hk_nonneg : 0 ≤ k
  · rw [integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn]
    · simp [Real.sin_int_mul_pi]
    · have hk_nonneg' : 0 ≤ (k : ℝ) := by exact_mod_cast hk_nonneg
      exact mul_nonneg hk_nonneg' pi_nonneg
  · rw [integral_symm, integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn]
    · simp [Real.sin_int_mul_pi]
    · have hk_nonpos' : (k : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hk_nonneg
      exact mul_nonpos_of_nonpos_of_nonneg hk_nonpos' pi_nonneg

/-- Helper for Exercise 18.4.3: the normalized product of two sine modes can be rewritten as a
difference of cosine modes. -/
lemma twoDivPi_mul_sin_int_mul_sin_int (a b : ℤ) (θ : ℝ) :
    (2 / π) * sin (a * θ) * sin (b * θ) =
      (1 / π) * (Real.cos ((a - b) * θ) - Real.cos ((a + b) * θ)) := by
  have hsub : (a : ℝ) * θ - (b : ℝ) * θ = ((a : ℝ) - (b : ℝ)) * θ := by
    ring
  have hadd : (a : ℝ) * θ + (b : ℝ) * θ = ((a : ℝ) + (b : ℝ)) * θ := by
    ring
  calc
    (2 / π) * sin (a * θ) * sin (b * θ) =
        (1 / π) * (2 * sin (a * θ) * sin (b * θ)) := by
          ring
    _ = (1 / π) * (Real.cos (((a : ℝ) * θ) - ((b : ℝ) * θ)) -
        Real.cos (((a : ℝ) * θ) + ((b : ℝ) * θ))) := by
          rw [Real.two_mul_sin_mul_sin]
    _ = (1 / π) * (Real.cos ((a - b) * θ) - Real.cos ((a + b) * θ)) := by
          rw [hsub, hadd]

/-- Helper for Exercise 18.4.3: the normalized sine family
`θ ↦ √(2 / π) * sin (((n : ℤ) + 1) * θ)` is orthonormal on `[0, π]`. -/
lemma integral_sin_succ_mul_sin_succ (m n : ℕ) :
    ∫ θ in 0..π,
      ((2 / π) * sin ((((m : ℤ) + 1 : ℤ)) * θ) * sin ((((n : ℤ) + 1 : ℤ)) * θ)) =
      if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst hmn
    let a : ℤ := (m : ℤ) + 1
    have hm_pos : 0 < ((m : ℤ) + 1) := by
      exact_mod_cast Nat.succ_pos m
    have hsum_ne : a + a ≠ 0 := by
      dsimp [a]
      linarith
    have hconst_int : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume 0 π := by
      exact Continuous.intervalIntegrable continuous_const 0 π
    have hcos_int : IntervalIntegrable (fun θ : ℝ ↦ Real.cos ((a + a) * θ)) volume 0 π := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hcos_sum_zero : ∫ θ in 0..π, Real.cos ((↑a + ↑a) * θ) = 0 := by
      simpa [Int.cast_add] using integral_cos_int_mul_eq_zero (k := a + a) hsum_ne
    -- Rewrite the square of a sine using the product-to-sum identity.
    calc
      ∫ θ in 0..π, (2 / π) * sin ((((m : ℤ) + 1 : ℤ)) * θ) * sin ((((m : ℤ) + 1 : ℤ)) * θ) =
          ∫ θ in 0..π, (1 / π) * (1 - Real.cos ((a + a) * θ)) := by
            refine integral_congr ?_
            intro θ hθ
            simpa [a] using twoDivPi_mul_sin_int_mul_sin_int a a θ
      _ = if m = m then 1 else 0 := by
            rw [intervalIntegral.integral_const_mul]
            rw [intervalIntegral.integral_sub hconst_int hcos_int]
            -- The zero-frequency term is constant, while the positive doubled frequency vanishes.
            rw [hcos_sum_zero, intervalIntegral.integral_const]
            simp [Real.pi_ne_zero]
  · have hmn_int : (m : ℤ) ≠ (n : ℤ) := by
      exact_mod_cast hmn
    let a : ℤ := (m : ℤ) + 1
    let b : ℤ := (n : ℤ) + 1
    have hsub_ne : a - b ≠ 0 := by
      apply sub_ne_zero.mpr
      intro hEq
      apply hmn_int
      simpa [a, b] using hEq
    have hm_pos : 0 < a := by
      dsimp [a]
      exact_mod_cast Nat.succ_pos m
    have hn_pos : 0 < b := by
      dsimp [b]
      exact_mod_cast Nat.succ_pos n
    have hsum_ne : a + b ≠ 0 := by
      linarith
    have hcos_sub_int : IntervalIntegrable (fun θ : ℝ ↦ Real.cos ((a - b) * θ)) volume 0 π := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hcos_sum_int : IntervalIntegrable (fun θ : ℝ ↦ Real.cos ((a + b) * θ)) volume 0 π := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hcos_sub_zero : ∫ θ in 0..π, Real.cos ((↑a - ↑b) * θ) = 0 := by
      simpa [Int.cast_sub] using integral_cos_int_mul_eq_zero (k := a - b) hsub_ne
    have hcos_sum_zero : ∫ θ in 0..π, Real.cos ((↑a + ↑b) * θ) = 0 := by
      simpa [Int.cast_add] using integral_cos_int_mul_eq_zero (k := a + b) hsum_ne
    -- Off the diagonal, both cosine frequencies are nonzero and therefore integrate to zero.
    calc
      ∫ θ in 0..π, (2 / π) * sin ((((m : ℤ) + 1 : ℤ)) * θ) * sin ((((n : ℤ) + 1 : ℤ)) * θ) =
          ∫ θ in 0..π, (1 / π) *
            (Real.cos ((a - b) * θ) - Real.cos ((a + b) * θ)) := by
            refine integral_congr ?_
            intro θ hθ
            simpa [a, b] using twoDivPi_mul_sin_int_mul_sin_int a b θ
      _ = if m = n then 1 else 0 := by
            rw [intervalIntegral.integral_const_mul,
              intervalIntegral.integral_sub hcos_sub_int hcos_sum_int, hcos_sub_zero, hcos_sum_zero]
            simp [hmn]

-- Proof sketch: rewrite the `measureU` integral using `integral_measureU_eq_integral_cos`, then
-- use `U_real_cos` to convert each evaluated Chebyshev polynomial into a sine quotient. The
-- factor `sin θ ^ 2` from the measure cancels the denominators, leaving the normalized sine
-- orthogonality integral on `[0, π]`.
/-- Exercise 18.4.3: the Chebyshev polynomials of the second kind are orthonormal with respect to
the measure `measureU`, equivalently
`∫ x, (U_m x) * (U_n x) dν = 1` when `m = n` and `0` otherwise. -/
theorem integral_eval_U_real_mul_eval_U_real_measureU (m n : ℕ) :
    ∫ x, (U ℝ m).eval x * (U ℝ n).eval x ∂ measureU = if m = n then 1 else 0 := by
  -- Rewrite the `measureU` integral in `θ`-coordinates so the trigonometric evaluation formula
  -- for `U` can be applied directly.
  rw [integral_measureU_eq_integral_cos]
  calc
    ∫ θ in 0..π,
        (U ℝ m).eval (cos θ) * (U ℝ n).eval (cos θ) * ((2 / π) * sin θ ^ 2) =
        ∫ θ in 0..π,
          (2 / π) * sin ((((m : ℤ) + 1 : ℤ)) * θ) * sin ((((n : ℤ) + 1 : ℤ)) * θ) := by
            refine integral_congr ?_
            intro θ hθ
            have hUm := U_real_cos (θ := θ) (n := (m : ℤ))
            have hUn := U_real_cos (θ := θ) (n := (n : ℤ))
            -- The `sin θ ^ 2` weight absorbs the two `sin θ` factors from `U_real_cos`.
            calc
              (U ℝ m).eval (cos θ) * (U ℝ n).eval (cos θ) * ((2 / π) * sin θ ^ 2) =
                  (2 / π) *
                    (((U ℝ m).eval (cos θ) * sin θ) * ((U ℝ n).eval (cos θ) * sin θ)) := by
                      ring
              _ =
                  (2 / π) *
                    (sin ((((m : ℤ) + 1 : ℤ)) * θ) * sin ((((n : ℤ) + 1 : ℤ)) * θ)) := by
                      rw [hUm, hUn]
                      norm_num
              _ = (2 / π) * sin ((((m : ℤ) + 1 : ℤ)) * θ) * sin ((((n : ℤ) + 1 : ℤ)) * θ) := by
                      ring
    _ = if m = n then 1 else 0 := integral_sin_succ_mul_sin_succ m n

end Polynomial.Chebyshev
