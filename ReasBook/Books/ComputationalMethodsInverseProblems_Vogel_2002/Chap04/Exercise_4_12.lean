/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Prop_4_29

public section

/- Exercise 4.12. Prove Proposition 4.29.

This exercise is direct canonical reuse of the existing source-facing theorem
`ProbabilityTheory.expected_sqNorm_eq_trace_secondMomentMatrix` formalizing
Proposition 4.29.
-/
#check ProbabilityTheory.expected_sqNorm_eq_trace_secondMomentMatrix
