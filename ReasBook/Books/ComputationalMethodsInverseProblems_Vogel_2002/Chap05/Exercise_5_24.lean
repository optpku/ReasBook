/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_31

public section

/- Exercise 5.24. Prove Proposition 5.31.

This exercise is a check-only reuse surface: Proposition 5.31 is already
formalized in `Book.Ch5.Prop_5_31` as two source-facing theorem clauses.
-/
#check Matrix.bccb_eq_fourierDiagonalization

#check Matrix.bccb_hasEigenvalue_iff
