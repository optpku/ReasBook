/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Remark_9_10

public section

/- Exercise 9.5. Confirm the first statement in Remark 9.10. The Chapter 9
counterexample is already formalized by the existing theorem
`NonnegativeOrthant.criticalPointNeedNotBeMinimizer`, so this exercise file
records direct reuse of that canonical owner rather than introducing an
exercise-specific alias theorem. -/

#check NonnegativeOrthant.criticalPointNeedNotBeMinimizer
