/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BoundedContinuousFunction ComplexConjugate

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable section

-- Proof sketch: rewrite `charFun μ t - charFun μ s` as the integral of
-- `(Complex.exp (⟪x, t - s⟫ * Complex.I) - 1) * Complex.exp (⟪x, s⟫ * Complex.I)`, apply the
-- Cauchy--Schwarz inequality, use that the exponential factor has norm `1`, and identify the
-- remaining integral with `2 * (1 - Complex.re (charFun μ (t - s)))`.
/-- Helper for Lemma 15.19: rewrite the characteristic-function increment as one oscillatory
integral with a shifted phase factor. -/
lemma charFunSub_eq_integral_incrementKernelMulPhase
    (μ : Measure E) [IsProbabilityMeasure μ] (s t : E) :
    charFun μ t - charFun μ s =
      ∫ x,
        (((BoundedContinuousFunction.innerProbChar (t - s) -
              BoundedContinuousFunction.const E (1 : ℂ)) *
            BoundedContinuousFunction.innerProbChar s) x : ℂ) ∂μ := by
  rw [charFun_eq_integral_innerProbChar, charFun_eq_integral_innerProbChar,
    ← integral_sub (BoundedContinuousFunction.integrable μ _)
      (BoundedContinuousFunction.integrable μ _)]
  refine integral_congr_ae <| Filter.Eventually.of_forall fun x => ?_
  calc
    (BoundedContinuousFunction.innerProbChar t x : ℂ) -
        BoundedContinuousFunction.innerProbChar s x
      = Complex.exp (inner ℝ x t * Complex.I) - Complex.exp (inner ℝ x s * Complex.I) := by
          simp [BoundedContinuousFunction.innerProbChar_apply]
    _ = (((BoundedContinuousFunction.innerProbChar (t - s) -
            BoundedContinuousFunction.const E (1 : ℂ)) *
          BoundedContinuousFunction.innerProbChar s) x : ℂ) := by
          simp only [BoundedContinuousFunction.innerProbChar_apply,
            BoundedContinuousFunction.const_apply, BoundedContinuousFunction.sub_apply,
            BoundedContinuousFunction.mul_apply]
          rw [sub_mul]
          have hphase :
              Complex.exp (inner ℝ x (t - s) * Complex.I) *
                  Complex.exp (inner ℝ x s * Complex.I) =
                Complex.exp (inner ℝ x t * Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            rw [inner_sub_right]
            have hsub :
                (((inner ℝ x t - inner ℝ x s : ℝ) : ℂ)) =
                  (inner ℝ x t : ℂ) - (inner ℝ x s : ℂ) := by
              norm_num
            rw [hsub, sub_mul]
            ring
          rw [hphase, one_mul]

/-- Helper for Lemma 15.19: removing the unimodular phase leaves the standard
`|z - 1|² = 2 (1 - Re z)` identity for the character increment. -/
lemma incrementKernelMulPhase_normSq_eq_two_mul_one_sub_re
    (s t x : E) :
    Complex.normSq
        ((((BoundedContinuousFunction.innerProbChar (t - s) -
                BoundedContinuousFunction.const E (1 : ℂ)) *
              BoundedContinuousFunction.innerProbChar s) x : ℂ)) =
      2 * (1 - Complex.re (BoundedContinuousFunction.innerProbChar (t - s) x)) := by
  simp only [BoundedContinuousFunction.innerProbChar_apply,
    BoundedContinuousFunction.const_apply, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.mul_apply]
  rw [Complex.normSq_mul]
  have hphase : Complex.normSq (Complex.exp (inner ℝ x s * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  rw [hphase, mul_one, Complex.normSq_sub, Complex.normSq_one]
  have hkernel : Complex.normSq (Complex.exp (inner ℝ x (t - s) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  rw [hkernel]
  simp
  ring

/-- Helper for Lemma 15.19: the real part of the integrated Fourier kernel is the real part of the
characteristic function. -/
lemma integral_re_innerProbChar_eq_re_charFun
    (μ : Measure E) [IsProbabilityMeasure μ] (u : E) :
    ∫ x, Complex.re (BoundedContinuousFunction.innerProbChar u x) ∂μ =
      Complex.re (charFun μ u) := by
  have hint : Integrable (BoundedContinuousFunction.innerProbChar u) μ :=
    BoundedContinuousFunction.integrable μ _
  -- Move `Complex.re` through the integral and then read the result as `charFun`.
  rw [charFun_eq_integral_innerProbChar]
  simpa using integral_re hint

/-- Helper for Lemma 15.19: Jensen's inequality for the convex function `x ↦ x²` bounds the square
of the expected pointwise norm by the expected squared norm. -/
lemma sq_integral_norm_le_integral_norm_sq
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E →ᵇ ℂ) :
    (∫ x, ‖f x‖ ∂μ) ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hnorm_mem : MemLp (fun x ↦ ‖f x‖) 2 μ :=
    MeasureTheory.MemLp.of_bound f.continuous.norm.measurable.aestronglyMeasurable ‖f‖ <|
      Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using f.norm_coe_le_norm x
  have hvariance :
      ProbabilityTheory.variance (fun x ↦ ‖f x‖) μ =
        ∫ x, ‖f x‖ ^ 2 ∂μ - (∫ x, ‖f x‖ ∂μ) ^ 2 := by
    simpa using ProbabilityTheory.variance_eq_sub (μ := μ) hnorm_mem
  have hvariance_nonneg : 0 ≤
      ∫ x, ‖f x‖ ^ 2 ∂μ - (∫ x, ‖f x‖ ∂μ) ^ 2 := by
    rw [← hvariance]
    exact ProbabilityTheory.variance_nonneg (fun x ↦ ‖f x‖) μ
  linarith

/-- Helper for Lemma 15.19: Cauchy--Schwarz in `L²(μ)` bounds the squared modulus of the integral
of a bounded complex kernel by the integral of its pointwise squared modulus. -/
lemma complexNormSq_integral_le_integral_normSq
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E →ᵇ ℂ) :
    Complex.normSq (∫ x, f x ∂μ) ≤ ∫ x, Complex.normSq (f x) ∂μ := by
  calc
    Complex.normSq (∫ x, f x ∂μ) = ‖∫ x, f x ∂μ‖ ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
    _ ≤ (∫ x, ‖f x‖ ∂μ) ^ 2 := by
      exact
        (sq_le_sq₀ (Complex.norm_nonneg _) (integral_nonneg fun x => norm_nonneg (f x))).2
          (norm_integral_le_integral_norm _)
    _ ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := sq_integral_norm_le_integral_norm_sq μ f
    _ = ∫ x, Complex.normSq (f x) ∂μ := by
      refine integral_congr_ae <| Filter.Eventually.of_forall fun x => ?_
      simp [Complex.normSq_eq_norm_sq]

/-- Lemma 15.19: For a probability measure on `ℝ^d`, the squared modulus of the increment of the
characteristic function is bounded by twice the real-part defect at the difference frequency. -/
theorem sq_norm_charFun_sub_le_two_mul_one_sub_re_charFun_sub
    (μ : Measure E) [IsProbabilityMeasure μ] (s t : E) :
    Complex.normSq (charFun μ t - charFun μ s) ≤
      2 * (1 - Complex.re (charFun μ (t - s))) := by
  let incrementKernel : E →ᵇ ℂ :=
    (BoundedContinuousFunction.innerProbChar (t - s) -
        BoundedContinuousFunction.const E (1 : ℂ)) *
      BoundedContinuousFunction.innerProbChar s
  have hre :
      Integrable (fun x ↦ Complex.re (BoundedContinuousFunction.innerProbChar (t - s) x)) μ := by
    simpa using
      (BoundedContinuousFunction.integrable μ
        (BoundedContinuousFunction.innerProbChar (t - s))).re
  -- Route correction: instead of pointwise Hölder bookkeeping, pass through the shifted kernel and
  -- apply Cauchy--Schwarz once in `L²(μ)`.
  calc
    Complex.normSq (charFun μ t - charFun μ s)
      = Complex.normSq (∫ x, incrementKernel x ∂μ) := by
          rw [charFunSub_eq_integral_incrementKernelMulPhase]
    _ ≤ ∫ x, Complex.normSq (incrementKernel x) ∂μ := by
          exact complexNormSq_integral_le_integral_normSq μ incrementKernel
    _ = ∫ x, 2 * (1 - Complex.re (BoundedContinuousFunction.innerProbChar (t - s) x)) ∂μ := by
          -- Normalize the pointwise squared modulus of the shifted kernel.
          refine integral_congr_ae <| Filter.Eventually.of_forall fun x => ?_
          simpa [incrementKernel] using
            incrementKernelMulPhase_normSq_eq_two_mul_one_sub_re (s := s) (t := t) (x := x)
    _ = 2 * (1 - Complex.re (charFun μ (t - s))) := by
          -- Integrate the normalized identity and translate it back to `charFun`.
          rw [integral_const_mul]
          congr 1
          calc
            ∫ x, (1 - Complex.re (BoundedContinuousFunction.innerProbChar (t - s) x)) ∂μ
              = ∫ x, (1 : ℝ) ∂μ -
                  ∫ x, Complex.re (BoundedContinuousFunction.innerProbChar (t - s) x) ∂μ := by
                    rw [← integral_sub (integrable_const 1) hre]
            _ = 1 - Complex.re (charFun μ (t - s)) := by
                  rw [integral_re_innerProbChar_eq_re_charFun]
                  simp
