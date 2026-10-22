/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_11.Toeplitz

public section

open scoped BigOperators Matrix

namespace Matrix

/-- Definition 5.3. The discrete convolution product of a centered kernel
`t : ℤ → ℂ` and a finite complex vector `f : Fin n → ℂ`. -/
@[expose]
def discreteConvolution {n : ℕ} (t : ℤ → ℂ) (f : Fin n → ℂ) : Fin n → ℂ :=
  toeplitzByDiag n t *ᵥ f

/-- The Toeplitz-matrix backend for `Matrix.discreteConvolution`. -/
theorem discreteConvolution_def {n : ℕ} (t : ℤ → ℂ) (f : Fin n → ℂ) :
    discreteConvolution t f = toeplitzByDiag n t *ᵥ f := rfl

/-- The coordinate formula for `Matrix.discreteConvolution` as the finite sum in `(5.20)`. -/
theorem discreteConvolution_apply {n : ℕ} (t : ℤ → ℂ) (f : Fin n → ℂ) (i : Fin n) :
    discreteConvolution t f i = ∑ j : Fin n, t (((i : ℕ) : ℤ) - (j : ℕ)) * f j := by
  simpa [discreteConvolution, toeplitzByDiag_apply] using
    mulVec_apply_eq_sum (toeplitzByDiag n t) f i

end Matrix
