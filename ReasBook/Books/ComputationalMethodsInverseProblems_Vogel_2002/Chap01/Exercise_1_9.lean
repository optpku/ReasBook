/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2_1

public section

/- Exercise 1.9 (1).

The right-hand side of `(1.27)` is minimized by the a priori choice `(1.28)`.
This exercise clause is already formalized by the imported Chapter 1 theorem
below, so the source-facing entry is direct canonical reuse.
-/

#check tsvdSourceCondition_aPrioriAlpha

/- Exercise 1.9 (2).

Substituting the a priori choice `(1.28)` into `(1.27)` yields the estimate
`(1.29)`. This exercise clause is already formalized by the imported Chapter 1
theorem below, so the source-facing entry is direct canonical reuse.
-/

#check tsvdSourceCondition_error_le_of_aPrioriAlpha
