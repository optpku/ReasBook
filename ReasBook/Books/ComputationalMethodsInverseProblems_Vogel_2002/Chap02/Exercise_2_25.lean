/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_39

public section

/- Exercise 2.25 (1). The source asks only for a proof of Theorem 2.39. Its
first clause is already formalized canonically in Chapter 2 as
`convexOn_iff_inner_gradient_sub_nonneg`. -/

#check convexOn_iff_inner_gradient_sub_nonneg

/- Exercise 2.25 (2). The source asks only for a proof of Theorem 2.39. Its
second clause is already formalized canonically in Chapter 2 as
`strictConvexOn_iff_inner_gradient_sub_pos`. -/

#check strictConvexOn_iff_inner_gradient_sub_pos
