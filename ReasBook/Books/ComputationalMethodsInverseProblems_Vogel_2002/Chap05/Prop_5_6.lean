/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_3
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_4
import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_6.Diagonalization
import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_6.Comparison

public section

open scoped Matrix
open DiscreteSignal

noncomputable section

namespace Matrix

/-- Proposition 5.6. Convolving `f` with the periodic extension `t^ext` of the
length-`n` signal `t` is the inverse normalized DFT of the pointwise product
`dft n t * dft n f`. -/
theorem periodicExtension_discreteConvolution_eq_invDFT_mul_dft
    (n : ℕ) [NeZero n] (t f : Fin n → ℂ) :
    ((1 / Real.sqrt n : ℂ) • discreteConvolution (periodicExtensionOfNeZero t) f) =
      invDFT n (dft n t * dft n f) := by
  rw [discreteConvolution_def, toeplitzByDiag_periodicExtension_eq_circulant]
  exact circulant_mulVec_eq_invDFT_mul_dft n t f

end Matrix
