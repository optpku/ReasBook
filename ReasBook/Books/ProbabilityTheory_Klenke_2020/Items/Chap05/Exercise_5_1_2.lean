/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- Helper for Exercise 5.1.2: the real-valued Beta density integrates to `1`. -/
private lemma integral_betaPDF_toReal_eq_one (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ x, (betaPDF a b x).toReal = 1 := by
  -- Convert the `ENNReal` normalization of `betaPDF` into an ordinary real integral.
  rw [MeasureTheory.integral_toReal]
  · simp [lintegral_betaPDF_eq_one ha hb]
  · simpa [betaPDF] using
      (ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)).aemeasurable
  · exact Filter.Eventually.of_forall fun x ↦ by simp [betaPDF]

/-- Helper for Exercise 5.1.2: multiplying the Beta density by `x ^ n` shifts the first parameter
from `r` to `r + n`. -/
private lemma betaMomentIntegrand_eq_ratio_mul_shiftedDensity
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (n : ℕ) (x : ℝ) :
    (betaPDF r s x).toReal * x ^ n =
      (beta (r + n) s / beta r s) * (betaPDF (r + n) s x).toReal := by
  rcases le_or_gt x 0 with hx_nonpos | hx_pos
  · -- Outside `(0, 1)` on the left, both Beta densities vanish.
    rw [betaPDF_eq_zero_of_nonpos hx_nonpos, betaPDF_eq_zero_of_nonpos hx_nonpos]
    simp
  · rcases le_or_gt 1 x with hx_one | hx_lt
    · -- Outside `(0, 1)` on the right, both Beta densities vanish.
      rw [betaPDF_eq_zero_of_one_le hx_one, betaPDF_eq_zero_of_one_le hx_one]
      simp
    · have hrn : 0 < r + n := by positivity
      have hmem : 0 < x ∧ x < 1 := ⟨hx_pos, hx_lt⟩
      have h_density :
          0 ≤ (1 / beta r s) * x ^ (r - 1) * (1 - x) ^ (s - 1) :=
        by
          have hpos := (betaPDFReal_pos hx_pos hx_lt hr hs).le
          rw [betaPDFReal, if_pos hmem] at hpos
          exact hpos
      have h_shifted :
          0 ≤ (1 / beta (r + n) s) * x ^ (r + n - 1) * (1 - x) ^ (s - 1) :=
        by
          have hpos := (betaPDFReal_pos hx_pos hx_lt hrn hs).le
          rw [betaPDFReal, if_pos hmem] at hpos
          exact hpos
      have hconst :
          (1 / beta r s) =
            (beta (r + n) s / beta r s) * (1 / beta (r + n) s) := by
        field_simp [ne_of_gt (beta_pos hr hs), ne_of_gt (beta_pos hrn hs)]
      have hpow : x ^ (r - 1) * x ^ (n : ℝ) = x ^ (r + n - 1) := by
        rw [← Real.rpow_add hx_pos]
        congr 1
        ring
      -- On `(0, 1)`, both densities are given by the explicit formula.
      rw [betaPDF_of_pos_lt_one hx_pos hx_lt, betaPDF_of_pos_lt_one hx_pos hx_lt]
      rw [ENNReal.toReal_ofReal h_density, ENNReal.toReal_ofReal h_shifted]
      rw [← Real.rpow_natCast x n]
      calc
        ((1 / beta r s) * x ^ (r - 1) * (1 - x) ^ (s - 1)) * x ^ (n : ℝ)
            = (1 / beta r s) * (x ^ (r - 1) * x ^ (n : ℝ)) * (1 - x) ^ (s - 1) := by
                ac_rfl
        _ = (1 / beta r s) * x ^ (r + n - 1) * (1 - x) ^ (s - 1) := by rw [hpow]
        _ = ((beta (r + n) s / beta r s) * (1 / beta (r + n) s)) *
              x ^ (r + n - 1) * (1 - x) ^ (s - 1) := by rw [hconst]
        _ = (beta (r + n) s / beta r s) *
              ((1 / beta (r + n) s) * x ^ (r + n - 1) * (1 - x) ^ (s - 1)) := by
                ac_rfl

/-- Helper for Exercise 5.1.2: shifting the first Beta parameter multiplies `beta a s` by
`a / (a + s)`. -/
private lemma beta_add_one_eq_mul_beta (a s : ℝ) (ha : 0 < a) (hs : 0 < s) :
    beta (a + 1) s = (a / (a + s)) * beta a s := by
  have has : a + s ≠ 0 := by linarith
  -- Rewrite both Beta functions in terms of Gamma functions and apply the Gamma recurrence.
  rw [beta, beta, Real.Gamma_add_one ha.ne']
  rw [show a + 1 + s = (a + s) + 1 by ring]
  rw [Real.Gamma_add_one has]
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos ha), ne_of_gt (Real.Gamma_pos_of_pos hs),
    ne_of_gt (Real.Gamma_pos_of_pos (add_pos ha hs))]

/-- Helper for Exercise 5.1.2: the `n`th power moment under `betaMeasure r s` is the corresponding
ratio of Beta functions. -/
private lemma integral_pow_eq_beta_ratio_betaMeasure
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    ∫ x, x ^ n ∂betaMeasure r s = beta (r + n) s / beta r s := by
  have h_meas :
      Measurable (betaPDF r s) := by
    simpa [betaPDF] using ENNReal.measurable_ofReal.comp (measurable_betaPDFReal r s)
  -- Rewrite the expectation against `betaMeasure` as an ordinary integral against Lebesgue measure.
  calc
    ∫ x, x ^ n ∂betaMeasure r s = ∫ x, (betaPDF r s x).toReal * x ^ n := by
      rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul h_meas]
      · simp only [smul_eq_mul]
      · exact Filter.Eventually.of_forall fun x : ℝ ↦ by simp [betaPDF]
    _ = ∫ x, (beta (r + n) s / beta r s) * (betaPDF (r + n) s x).toReal := by
      refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦
        betaMomentIntegrand_eq_ratio_mul_shiftedDensity r s hr hs n x
    _ = beta (r + n) s / beta r s := by
      rw [integral_const_mul, integral_betaPDF_toReal_eq_one (r + n) s (by positivity) hs, mul_one]

/-- Helper for Exercise 5.1.2: the Beta-function ratio equals the finite product from the exercise
statement. -/
private lemma beta_ratio_eq_prod (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    beta (r + n) s / beta r s = ∏ k ∈ Finset.range n, (r + k) / (r + s + k) := by
  induction n with
  | zero =>
      -- The empty product matches the trivial Beta ratio.
      simp [ne_of_gt (beta_pos hr hs)]
  | succ n ih =>
      have hrn : 0 < r + n := by positivity
      have hsucc :
          beta (r + n + 1) s / beta r s
            = ∏ k ∈ Finset.range (n + 1), (r + k) / (r + s + k) := by
        calc
          beta (r + n + 1) s / beta r s
              = (((r + n) / (r + n + s)) * beta (r + n) s) / beta r s := by
                  rw [beta_add_one_eq_mul_beta (r + n) s hrn hs]
          _ = ((r + n) / (r + n + s)) * (beta (r + n) s / beta r s) := by
                simp_rw [div_eq_mul_inv]
                ac_rfl
          _ = ((r + n) / (r + n + s)) * ∏ k ∈ Finset.range n, (r + k) / (r + s + k) := by
                rw [ih]
          _ = ((r + n) / (r + s + n)) * ∏ k ∈ Finset.range n, (r + k) / (r + s + k) := by
                congr 1
                ring
          _ = ∏ k ∈ Finset.range (n + 1), (r + k) / (r + s + k) := by
                rw [Finset.prod_range_succ, mul_comm]
      simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hsucc

-- Proof sketch: transport the canonical beta-ratio moment formula for `betaMeasure r s` along
-- `HasLaw.integral_comp`, then rewrite the ratio with `beta_ratio_eq_prod`.
/-- Exercise 5.1.2: If a real random variable has Beta law with parameters `r, s > 0`, then its
`n`th moment is `∏_{k=0}^{n-1} (r + k) / (r + s + k)`. -/
theorem beta_moment_formula (r s : ℝ) (hr : 0 < r) (hs : 0 < s) {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (betaMeasure r s) P) (n : ℕ) :
    P[fun ω ↦ X ω ^ n] = ∏ k ∈ Finset.range n, (r + k) / (r + s + k) := by
  -- Transport the moment from `P` to the canonical Beta law, then simplify the resulting ratio.
  calc
    P[fun ω ↦ X ω ^ n] = ∫ x, x ^ n ∂betaMeasure r s := by
      simpa [Function.comp_apply] using
        hX.integral_comp
          (f := fun x : ℝ ↦ x ^ n)
          ((continuous_id.pow n).aestronglyMeasurable)
    _ = beta (r + n) s / beta r s := integral_pow_eq_beta_ratio_betaMeasure r s hr hs n
    _ = ∏ k ∈ Finset.range n, (r + k) / (r + s + k) := beta_ratio_eq_prod r s hr hs n
