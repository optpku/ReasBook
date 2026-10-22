/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_14

public section

/- Exercise 9.8. The source asks for a proof of Proposition 9.14. That
proposition is already formalized in Chapter 9 by
`NonnegativeOrthant.isCriticalPoint_iff_projectedGradient_eq_zero`, so this
exercise file records direct reuse of the existing theorem owner rather than
introducing an exercise-specific wrapper theorem. -/

#check NonnegativeOrthant.isCriticalPoint_iff_projectedGradient_eq_zero
