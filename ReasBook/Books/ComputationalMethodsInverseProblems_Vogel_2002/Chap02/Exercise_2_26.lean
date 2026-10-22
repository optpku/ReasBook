/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_42

public section

/- Exercise 2.26 (1). The source asks only for a proof of Theorem 2.42. Its
first clause is already formalized canonically in Chapter 2 as
`convexOn_iff_hessian_isPositive`. -/

#check convexOn_iff_hessian_isPositive

/- Exercise 2.26 (2). The source asks only for a proof of Theorem 2.42. Its
second clause is already formalized canonically in Chapter 2 as
`strictConvexOn_of_hessian_inner_pos`. -/

#check strictConvexOn_of_hessian_inner_pos

/- Exercise 2.26 (3). The source asks only for a proof of Theorem 2.42. Its
third clause is already formalized canonically in Chapter 2 as
`secondOrderTaylorFormulaAt_of_contDiffAt`. -/

#check secondOrderTaylorFormulaAt_of_contDiffAt
