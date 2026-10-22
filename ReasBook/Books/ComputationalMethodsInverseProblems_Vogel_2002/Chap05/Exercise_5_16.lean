/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Exercise_5_15
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Lemma_5_21
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Remark_5_17

public section

/- Exercise 5.16. Prove Lemma 5.21.

This exercise is a check-only reuse surface: Lemma 5.21 is already formalized
in `Book.Ch5.Lemma_5_21` as
`Matrix.bestCirculantApproximation_eq_fourierDiagonalProjection`.

The textbook hint is also already exposed by the source-facing results
`Matrix.circulant_eq_fourierDiagonal_fft` and
`Matrix.frobenius_norm_mul_eq_of_mem_unitary`.
-/
#check Matrix.bestCirculantApproximation_eq_fourierDiagonalProjection

#check Matrix.circulant_eq_fourierDiagonal_fft

#check Matrix.frobenius_norm_mul_eq_of_mem_unitary
