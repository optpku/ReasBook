/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_38
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_8

public section

/- Exercise 9.4. The source asks for a proof of Proposition 9.8 using
Theorem 2.38, whose formalized owner is
`inner_gradient_sub_nonneg_of_isLocalMinOn`. Proposition 9.8 is already
formalized in Chapter 9 as the three source-facing clause theorems below, so
this exercise file records direct reuse of both that Chapter 2 proof-route
owner and the existing Chapter 9 theorem owners rather than introducing an
exercise-specific wrapper theorem. -/

#check inner_gradient_sub_nonneg_of_isLocalMinOn

#check NonnegativeOrthant.gradient_nonneg

#check NonnegativeOrthant.coordinate_nonneg

#check NonnegativeOrthant.complementarity
