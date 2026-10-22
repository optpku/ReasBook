/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_12

public section

/- Exercise 2.8. The source asks to show that the diagonal operator `D` from
Example 2.8 is a compact operator on `ℓ²(ℝ)`.

This is already formalized in Chapter 2 by the existing theorem
`RealL2.harmonicDiagonal_isCompactOperator`, whose operator is exactly the
diagonal operator from Example 2.8. -/

#check RealL2.harmonicDiagonal_isCompactOperator
