/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_19

public section

/- Exercise 2.15 (1). The source asks only for a proof of Theorem 2.19. Its
first clause is already formalized canonically in Chapter 2 as
`ContinuousLinearMap.SingularSystem.reconstructionOperator_isLinear`. -/

#check ContinuousLinearMap.SingularSystem.reconstructionOperator_isLinear

/- Exercise 2.15 (2). The source asks only for a proof of Theorem 2.19. Its
second clause is already formalized canonically in Chapter 2 as
`ContinuousLinearMap.SingularSystem.reconstructionOperator_convergesToRangePseudoInverse`. -/

#check ContinuousLinearMap.SingularSystem.reconstructionOperator_convergesToRangePseudoInverse
