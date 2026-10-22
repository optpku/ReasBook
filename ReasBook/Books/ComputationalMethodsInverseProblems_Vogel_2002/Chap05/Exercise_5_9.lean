/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Notation_5_2_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_6

public section

namespace Matrix

/-- Exercise 5.9. Equations `(5.23)` and `(5.38)` are equivalent formulations of
the periodic-extension discrete convolution identity, via the canonical
normalized `Matrix.dft`/`Matrix.invDFT` and source-facing `Matrix.fft`/`Matrix.ifft`
owners already established in Chapter 5. -/
theorem periodicExtension_discreteConvolution_eq_ifft_mul_fft_iff_invDFT_mul_dft
    (n : ℕ) [NeZero n] (t f : Fin n → ℂ) :
    Matrix.discreteConvolution (DiscreteSignal.periodicExtensionOfNeZero t) f =
        Matrix.ifft n (Matrix.fft n t * Matrix.fft n f) ↔
      ((1 / Real.sqrt n : ℂ) •
          Matrix.discreteConvolution (DiscreteSignal.periodicExtensionOfNeZero t) f) =
        Matrix.invDFT n (Matrix.dft n t * Matrix.dft n f) := by
  constructor <;> intro _
  · simpa using Matrix.periodicExtension_discreteConvolution_eq_invDFT_mul_dft n t f
  · simpa using
      (Matrix.periodicExtension_discreteConvolution_eq_ifft_mul_fft n
        (WithLp.toLp 2 t) (WithLp.toLp 2 f))

end Matrix
