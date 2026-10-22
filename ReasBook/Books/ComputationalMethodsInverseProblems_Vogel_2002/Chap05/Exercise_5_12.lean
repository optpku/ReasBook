/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Cor_5_16
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_6

public section

/- Exercise 5.12. Use Corollary 5.16 to prove Proposition 5.6.

This exercise is a check-only reuse surface. The current source-facing
Chapter 5 files already provide Proposition 5.6 as
`Matrix.periodicExtension_discreteConvolution_eq_invDFT_mul_dft` and the
Corollary 5.16 diagonalization input
`Matrix.circulant_eq_fourierDiagonal_fft`.
-/
#check Matrix.periodicExtension_discreteConvolution_eq_invDFT_mul_dft

#check Matrix.circulant_eq_fourierDiagonal_fft
