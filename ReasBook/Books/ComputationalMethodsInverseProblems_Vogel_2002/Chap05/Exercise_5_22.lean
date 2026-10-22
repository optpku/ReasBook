/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_30

public section

/- Exercise 5.22. Prove Proposition 5.30.

This exercise is a check-only reuse surface: Proposition 5.30 is already
formalized in `Book.Ch5.Prop_5_30` as the source-facing theorem
`Matrix.dft2D_eq_of_kronFourier_mulVec`.
-/
#check Matrix.dft2D_eq_of_kronFourier_mulVec
