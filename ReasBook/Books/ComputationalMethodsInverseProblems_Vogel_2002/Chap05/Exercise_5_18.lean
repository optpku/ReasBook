/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Cor_5_23

public section

/- Exercise 5.18. Prove Corollary 5.23.

This exercise is a check-only reuse surface: Corollary 5.23 is already
formalized in `Book.Ch5.Cor_5_23` as
`Matrix.bestCirculantApproximation_toeplitzByDiag_eq_circulant`, identifying
`Matrix.bestCirculantApproximation (Matrix.toeplitzByDiag n t)` with the
corresponding circulant matrix of weighted diagonal-average coefficients.
-/
#check Matrix.bestCirculantApproximation_toeplitzByDiag_eq_circulant
