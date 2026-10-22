/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_10

public section

/- Exercise 5.7. Prove Proposition 5.10.

This exercise is a check-only reuse surface: Proposition 5.10 is already
formalized in `Book.Ch5.Prop_5_10` as
`Matrix.periodicExtension_discreteConvolution2D_eq_invDFT2D_hadamard_dft2D`.
-/
#check Matrix.periodicExtension_discreteConvolution2D_eq_invDFT2D_hadamard_dft2D
