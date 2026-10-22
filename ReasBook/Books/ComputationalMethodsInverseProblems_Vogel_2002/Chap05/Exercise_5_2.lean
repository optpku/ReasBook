/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Notation_5_2_1

public section

noncomputable section

open scoped BigOperators FourierTransform RealInnerProductSpace

namespace FourierApproximation

/-- The sampled spatial point `x_j = ((j : ℕ) : ℝ) * h` from Exercise 5.2. -/
def samplePoint (h : ℝ) (j : ℕ) : ℝ :=
  ((j : ℕ) : ℝ) * h

/-- The sampled frequency `ξ_i = ((i : ℕ) : ℝ) / (n * h)` from Exercise 5.2. -/
def sampleFrequency (n : ℕ) [NeZero n] (h : ℝ) (i : Fin n) : ℝ :=
  ((i : ℕ) : ℝ) / (n * h)

/-- The truncated continuous Fourier kernel `exp(-2π i x ξ)` used in Exercise 5.2. -/
def truncatedKernel (ξ x : ℝ) : ℂ :=
  Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I)

/-- The left-endpoint quadrature sum for the truncated Fourier transform on the sample grid from
Exercise 5.2. -/
def truncatedQuadrature (n : ℕ) [NeZero n] (h : ℝ) (f : ℝ → ℂ) (i : Fin n) : ℂ :=
  ∑ j : Fin n,
    (h : ℂ) * truncatedKernel (sampleFrequency n h i) (samplePoint h j) * f (samplePoint h j)

/-- Helper for Exercise 5.2: the sampled Fourier kernel always has unit modulus. -/
lemma norm_truncatedKernel (ξ x : ℝ) : ‖truncatedKernel ξ x‖ = 1 := by
  -- Rewrite the kernel to the standard `exp (t * I)` form and use the unit-modulus formula.
  rw [truncatedKernel]
  simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (-2 * Real.pi * x * ξ)

/-- Helper for Exercise 5.2: after multiplying by the grid spacing, the sampled continuous kernel
matches the Chapter 5 DFT phase. -/
lemma scaledSampleKernel_eq_fftPhase
    (n : ℕ) [NeZero n] (h : ℝ) (i j : Fin n) :
    (h : ℂ) * truncatedKernel (sampleFrequency n h i) (samplePoint h j) =
      (h : ℂ) * Complex.exp (-Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n)) := by
  by_cases h0 : h = 0
  · -- When `h = 0`, the outer prefactor makes both sides vanish.
    simp [h0, truncatedKernel]
  · have hn : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.pos_of_neZero n).ne'
    have hnh : (n : ℝ) * h ≠ 0 := mul_ne_zero hn h0
    have hphase :
        -2 * Real.pi * samplePoint h j * sampleFrequency n h i =
          -2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℝ) / n) := by
      -- The sampled location/frequency pair collapses to the discrete phase `ij / n`.
      dsimp [samplePoint, sampleFrequency]
      field_simp [hnh, hn]
    have hcast :
        ((((i : ℕ) * (j : ℕ) : ℝ) / n : ℝ) : ℂ) =
          (((i : ℕ) * (j : ℕ) : ℂ) / n) := by
      norm_num [Nat.cast_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    -- Replace the sampled real exponent by the discrete complex phase.
    rw [truncatedKernel]
    congr 1
    congr 1
    calc
      (((-2 * Real.pi * samplePoint h j * sampleFrequency n h i : ℝ) : ℂ) * Complex.I)
          = (((-2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℝ) / n) : ℝ) : ℂ) * Complex.I) := by
              rw [hphase]
      _ = (((-2 * Real.pi : ℝ) : ℂ) * (((i : ℕ) * (j : ℕ) : ℂ) / n)) * Complex.I := by
            simp [Complex.ofReal_mul, hcast, mul_assoc]
      _ = (-(2 * Real.pi : ℂ) * (((i : ℕ) * (j : ℕ) : ℂ) / n)) * Complex.I := by
            simp
      _ = -Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n) := by
            ring

/-- Helper for Exercise 5.2: the continuous Fourier transform splits into the truncation window
integral plus the complementary tail integral. -/
lemma fourier_eq_windowIntegral_add_tail
    (f : ℝ → ℂ) (hf : MeasureTheory.Integrable f) (ξ T : ℝ) :
    𝓕 f ξ =
      (∫ x in Set.Icc (0 : ℝ) T, truncatedKernel ξ x • f x) +
        ∫ x in (Set.Icc (0 : ℝ) T)ᶜ, truncatedKernel ξ x • f x := by
  have hcont : Continuous (fun x : ℝ ↦ truncatedKernel ξ x) := by
    -- The sampled kernel is a smooth exponential in the real variable.
    unfold truncatedKernel
    fun_prop
  have hkernelIntegrable :
      MeasureTheory.Integrable (fun x : ℝ ↦ truncatedKernel ξ x • f x) := by
    -- The Fourier kernel is bounded by `1`, so multiplying by it preserves integrability.
    refine hf.bdd_smul 1 hcont.aestronglyMeasurable ?_
    filter_upwards with x
    simp [norm_truncatedKernel]
  -- Rewrite the Fourier transform into the kernel integral and split the domain into the
  -- truncation window and its complement.
  calc
    𝓕 f ξ = ∫ x : ℝ, truncatedKernel ξ x • f x := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      simp only [truncatedKernel]
    _ =
        (∫ x in Set.Icc (0 : ℝ) T, truncatedKernel ξ x • f x) +
          ∫ x in (Set.Icc (0 : ℝ) T)ᶜ, truncatedKernel ξ x • f x := by
            symm
            exact MeasureTheory.integral_add_compl
              (s := Set.Icc (0 : ℝ) T) measurableSet_Icc hkernelIntegrable

/-- Helper for Exercise 5.2: on any measurable set, the truncated Fourier integral is controlled
by the `L¹` mass of `‖f‖` because the kernel has unit modulus. -/
lemma norm_windowIntegral_truncatedKernel_le
    (f : ℝ → ℂ) {s : Set ℝ} (hf : MeasureTheory.IntegrableOn f s) (ξ : ℝ) :
    ‖∫ x in s, truncatedKernel ξ x • f x‖ ≤ ∫ x in s, ‖f x‖ := by
  have hcont : Continuous (fun x : ℝ ↦ truncatedKernel ξ x) := by
    -- The same continuity argument works after restricting the measure.
    unfold truncatedKernel
    fun_prop
  have hkernelIntegrable :
      MeasureTheory.Integrable (fun x : ℝ ↦ truncatedKernel ξ x • f x)
        (MeasureTheory.volume.restrict s) := by
    -- Restricting the measure keeps the same bounded-modulus argument available on `s`.
    refine hf.bdd_smul 1 hcont.aestronglyMeasurable ?_
    filter_upwards with x
    simp [norm_truncatedKernel]
  -- Apply the standard Bochner integral norm bound on the restricted measure.
  simpa [norm_smul, norm_truncatedKernel] using
    (MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict s)
      (f := fun x : ℝ ↦ truncatedKernel ξ x • f x))

end FourierApproximation

open FourierApproximation

/-- Exercise 5.2 (1). For mesh width `h`, sample points
`x_j = ((j : ℕ) : ℝ) * h`, and discrete frequencies
`ξ_i = ((i : ℕ) : ℝ) / (n * h)`, the source-facing Chapter 5 transform
`Matrix.fft` from `(5.17)` gives exactly the left-endpoint quadrature sum for
the truncated continuous Fourier kernel on `[0, n * h]`. -/
theorem dft_eq_truncatedFourierQuadrature
    (n : ℕ) [NeZero n] (h : ℝ) (f : ℝ → ℂ) (i : Fin n) :
    (h : ℂ) * Matrix.fft n (fun j ↦ f (samplePoint h j)) i = truncatedQuadrature n h f i := by
  -- Expand the source-facing FFT coordinate formula and rewrite each sampled phase factor.
  have hfft :
      Matrix.fft n (fun j ↦ f (samplePoint h j)) i =
        ∑ j : Fin n,
          f (samplePoint h j) *
            Complex.exp (-Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n)) := by
    simpa using
      (Matrix.fft_apply n (WithLp.toLp 2 (fun j ↦ f (samplePoint h j))) i)
  rw [hfft]
  rw [truncatedQuadrature, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  calc
    (h : ℂ) *
        (f (samplePoint h j) *
          Complex.exp (-Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n)))
      =
        ((h : ℂ) *
          Complex.exp (-Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n))) *
          f (samplePoint h j) := by
            ring
    _ =
        ((h : ℂ) * truncatedKernel (sampleFrequency n h i) (samplePoint h j)) *
          f (samplePoint h j) := by
            rw [← scaledSampleKernel_eq_fftPhase]
    _ =
        (h : ℂ) * truncatedKernel (sampleFrequency n h i) (samplePoint h j) *
          f (samplePoint h j) := by
          ring

/-- Exercise 5.2 (2). At the frequency
`ξ_i = ((i : ℕ) : ℝ) / (n * h)`, the error between the scaled Chapter 5 DFT and
the continuous Fourier transform is bounded by the quadrature error on the
truncation window `[0, n * h]` plus the tail integral of `‖f‖` outside that
window. -/
theorem dft_truncatedFourierApproximation_error_le
    (n : ℕ) [NeZero n] (h : ℝ) (_hh : 0 < h) (f : ℝ → ℂ)
    (hf : MeasureTheory.Integrable f) (i : Fin n) :
    ‖(h : ℂ) * Matrix.fft n (fun j ↦ f (samplePoint h j)) i - 𝓕 f (sampleFrequency n h i)‖ ≤
      ‖truncatedQuadrature n h f i -
        ∫ x in Set.Icc (0 : ℝ) (n * h),
          truncatedKernel (sampleFrequency n h i) x • f x‖ +
      ∫ x in (Set.Icc (0 : ℝ) (n * h))ᶜ, ‖f x‖ := by
  have htail :
      ‖∫ x in (Set.Icc (0 : ℝ) (n * h))ᶜ,
          truncatedKernel (sampleFrequency n h i) x • f x‖ ≤
        ∫ x in (Set.Icc (0 : ℝ) (n * h))ᶜ, ‖f x‖ := by
    -- Control the complement integral by the `L¹` tail of `f`.
    simpa using
      norm_windowIntegral_truncatedKernel_le
        (f := f) (s := (Set.Icc (0 : ℝ) (n * h))ᶜ) hf.integrableOn (sampleFrequency n h i)
  calc
    ‖(h : ℂ) * Matrix.fft n (fun j ↦ f (samplePoint h j)) i - 𝓕 f (sampleFrequency n h i)‖
      = ‖truncatedQuadrature n h f i - 𝓕 f (sampleFrequency n h i)‖ := by
          rw [dft_eq_truncatedFourierQuadrature]
    _ =
        ‖truncatedQuadrature n h f i -
            ((∫ x in Set.Icc (0 : ℝ) (n * h),
                truncatedKernel (sampleFrequency n h i) x • f x) +
              ∫ x in (Set.Icc (0 : ℝ) (n * h))ᶜ,
                truncatedKernel (sampleFrequency n h i) x • f x)‖ := by
            exact congrArg
              (fun z : ℂ ↦ ‖truncatedQuadrature n h f i - z‖)
              (fourier_eq_windowIntegral_add_tail
                (f := f) hf (sampleFrequency n h i) (n * h))
    _ =
        ‖(truncatedQuadrature n h f i -
              ∫ x in Set.Icc (0 : ℝ) (n * h),
                truncatedKernel (sampleFrequency n h i) x • f x) -
            ∫ x in (Set.Icc (0 : ℝ) (n * h))ᶜ,
              truncatedKernel (sampleFrequency n h i) x • f x‖ := by
            congr 1
            ring
    -- A single triangle inequality plus the tail estimate finishes the bound.
    _ 
      ≤
        ‖truncatedQuadrature n h f i -
            ∫ x in Set.Icc (0 : ℝ) (n * h), truncatedKernel (sampleFrequency n h i) x • f x‖ +
          ‖∫ x in (Set.Icc (0 : ℝ) (n * h))ᶜ,
              truncatedKernel (sampleFrequency n h i) x • f x‖ := by
                exact norm_sub_le _ _
    _ ≤
        ‖truncatedQuadrature n h f i -
            ∫ x in Set.Icc (0 : ℝ) (n * h), truncatedKernel (sampleFrequency n h i) x • f x‖ +
          ∫ x in (Set.Icc (0 : ℝ) (n * h))ᶜ, ‖f x‖ := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left htail
                ‖truncatedQuadrature n h f i -
                    ∫ x in Set.Icc (0 : ℝ) (n * h),
                      truncatedKernel (sampleFrequency n h i) x • f x‖

end
