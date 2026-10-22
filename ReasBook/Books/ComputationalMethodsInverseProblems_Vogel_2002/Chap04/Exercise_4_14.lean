/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Prop_4_35

public section

open ProbabilityTheory.MinimumVarianceLinear

/- Exercise 4.14. Equation (4.38) is the trace-form expansion of the
minimum-variance linear objective from Definition 4.34. -/
#check coefficientObjective_eq_trace_quadratic
