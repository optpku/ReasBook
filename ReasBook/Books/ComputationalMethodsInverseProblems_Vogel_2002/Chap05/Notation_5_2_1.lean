/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_3
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_4
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Notation_5_2.Coordinates
import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_6

public section

open scoped BigOperators Matrix Complex.FiniteDimensional

noncomputable section

namespace Matrix

/-- The source forward `fft` notation from Chapter 5, written as the source-facing
rescaling of the canonical normalized DFT owner `Matrix.dft`. -/
abbrev fft (n : ℕ) [NeZero n] : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  (Real.sqrt n : ℂ) • Matrix.dft n

/-- `Matrix.fft` is the source-facing rescaling of the canonical normalized DFT
owner `Matrix.dft`. -/
theorem fft_def (n : ℕ) [NeZero n] :
    Matrix.fft n = (Real.sqrt n : ℂ) • Matrix.dft n :=
  rfl

/-- The source inverse `ifft` notation from Chapter 5, written as the
source-facing rescaling of the canonical normalized inverse DFT owner
`Matrix.invDFT`. -/
abbrev ifft (n : ℕ) [NeZero n] : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  ((Real.sqrt n : ℂ)⁻¹) • Matrix.invDFT n

/-- `Matrix.ifft` is the source-facing rescaling of the canonical normalized
inverse DFT owner `Matrix.invDFT`. -/
theorem ifft_def (n : ℕ) [NeZero n] :
    Matrix.ifft n = ((Real.sqrt n : ℂ)⁻¹) • Matrix.invDFT n :=
  rfl

/-- Notation 5.2.2-extra-2 (1). The source forward transform `Matrix.fft` has the
textbook coordinate formula from equation `(5.36)`. -/
theorem fft_apply (n : ℕ) [NeZero n] (f : ℂ^[n]) (i : Fin n) :
    Matrix.fft n f.ofLp i =
      ∑ j : Fin n,
        f j *
          Complex.exp (-Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n)) := by
  have hn : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_neZero n).ne'
  have hsqrt : (Real.sqrt n : ℂ) ≠ 0 := by
    simpa using
      (Real.sqrt_ne_zero'.2 (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_neZero n))
  calc
    Matrix.fft n f.ofLp i = (Real.sqrt n : ℂ) * Matrix.dft n f.ofLp i := by
      simp [Matrix.fft]
    _ =
        (Real.sqrt n : ℂ) *
          ∑ j : Fin n,
            (Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) /
                Real.sqrt n *
              f.ofLp j := by
          rw [Matrix.dft_apply_exp]
    _ =
        ∑ j : Fin n,
          (Real.sqrt n : ℂ) *
            (((Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) /
                  Real.sqrt n) *
              f.ofLp j) := by
          rw [Finset.mul_sum]
    _ =
        ∑ j : Fin n,
          f j *
            Complex.exp (-Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n)) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          have hexp :
              (Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) =
                Complex.exp (-Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n)) := by
            rw [← Complex.exp_nat_mul]
            congr 1
            rw [Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv]
            ring
          calc
            (Real.sqrt n : ℂ) *
                (((Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) /
                      Real.sqrt n) *
                  f.ofLp j)
              =
                ((Real.sqrt n : ℂ) *
                    ((Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) /
                      Real.sqrt n)) *
                  f.ofLp j := by ring
            _ = (Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) * f.ofLp j := by
                  rw [div_eq_mul_inv]
                  have hsqrt_cancel :
                      (Real.sqrt n : ℂ) *
                          ((Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) *
                            (Real.sqrt n : ℂ)⁻¹) =
                        (Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) := by
                    calc
                      (Real.sqrt n : ℂ) *
                          ((Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) *
                            (Real.sqrt n : ℂ)⁻¹)
                        =
                          ((Real.sqrt n : ℂ) * (Real.sqrt n : ℂ)⁻¹) *
                            (Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) := by
                              ring
                      _ =
                          (Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) := by
                            simp [hsqrt]
                  rw [hsqrt_cancel]
            _ =
                f j *
                  (Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) := by
                  simp [mul_comm, mul_left_comm]
            _ =
                f j *
                  Complex.exp (-Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n)) := by
                  rw [hexp]

/-- Notation 5.2.2-extra-2 (2). The source inverse transform `Matrix.ifft` has the
textbook coordinate formula from equation `(5.37)`. -/
theorem ifft_apply (n : ℕ) [NeZero n] (f : ℂ^[n]) (i : Fin n) :
    Matrix.ifft n f.ofLp i =
      (n : ℂ)⁻¹ *
        ∑ j : Fin n,
          f j *
            Complex.exp (Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n)) := by
  simpa [Matrix.ifft] using Matrix.invDFT_apply_exp n f.ofLp i

/-- Notation 5.2.2-extra-2 (3). The convolution identity `(5.38)` rewrites
Proposition 5.6 through the source-facing operators `Matrix.fft` and
`Matrix.ifft`. -/
theorem periodicExtension_discreteConvolution_eq_ifft_mul_fft
    (n : ℕ) [NeZero n] (t f : ℂ^[n]) :
    Matrix.discreteConvolution (DiscreteSignal.periodicExtensionOfNeZero t.ofLp) f.ofLp =
      Matrix.ifft n (Matrix.fft n t.ofLp * Matrix.fft n f.ofLp) := by
  have hsqrt : (Real.sqrt n : ℂ) ≠ 0 := by
    simpa using
      (Real.sqrt_ne_zero'.2 (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_neZero n))
  have hsqrt_sq : ((Real.sqrt n : ℂ) * Real.sqrt n) = n := by
    exact_mod_cast (Real.mul_self_sqrt (show (0 : ℝ) ≤ n by exact_mod_cast Nat.zero_le n))
  have hscaled :=
    congrArg ((Real.sqrt n : ℂ) • ·)
      (Matrix.periodicExtension_discreteConvolution_eq_invDFT_mul_dft n t.ofLp f.ofLp)
  have hfft_mul :
      Matrix.fft n t.ofLp * Matrix.fft n f.ofLp =
        (n : ℂ) • (Matrix.dft n t.ofLp * Matrix.dft n f.ofLp) := by
    ext i
    simp [Matrix.fft, hsqrt_sq, mul_assoc, mul_left_comm, mul_comm]
  have hifft_smul_n (g : Fin n → ℂ) :
      Matrix.ifft n ((n : ℂ) • g) = (Real.sqrt n : ℂ) • Matrix.invDFT n g := by
    ext i
    rw [Matrix.ifft, LinearMap.smul_apply, map_smul]
    have hscalar : ((Real.sqrt n : ℂ)⁻¹ * (n : ℂ)) = (Real.sqrt n : ℂ) := by
      rw [← hsqrt_sq]
      field_simp [hsqrt]
    simp [Pi.smul_apply, smul_eq_mul, ← mul_assoc, hscalar]
  calc
    Matrix.discreteConvolution (DiscreteSignal.periodicExtensionOfNeZero t.ofLp) f.ofLp =
        (Real.sqrt n : ℂ) • Matrix.invDFT n (Matrix.dft n t.ofLp * Matrix.dft n f.ofLp) := by
          simpa [one_div, smul_smul, hsqrt, mul_assoc, mul_left_comm, mul_comm] using hscaled
    _ = Matrix.ifft n ((n : ℂ) • (Matrix.dft n t.ofLp * Matrix.dft n f.ofLp)) := by
          simpa using (hifft_smul_n (Matrix.dft n t.ofLp * Matrix.dft n f.ofLp)).symm
    _ = Matrix.ifft n (Matrix.fft n t.ofLp * Matrix.fft n f.ofLp) := by
          rw [hfft_mul]

end Matrix
