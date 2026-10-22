/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_20

public section

/- Exercise 7.16. Verify equation `(7.73)` from `(7.70)` using the
substitution `t = 1 / (1 + u^p)`.

In this repository, that source-facing beta-integral identity is already
formalized by `KernelMoment.integral_eq_betaIntegral` in Proposition 7.20, so
this exercise is recorded by direct reuse of the existing Chapter 7 API rather
than by an exercise-specific wrapper theorem. -/
#check KernelMoment.integral_eq_betaIntegral

end
