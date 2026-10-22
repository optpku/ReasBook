/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_27

public section

/- Exercise 7.22. The source asks the reader to prove Theorem 7.27. In this
repository, Theorem 7.27 is already formalized as the three source-facing
Chapter 7 discrepancy-principle clauses below, so this exercise is recorded by
direct reuse of that existing surface rather than by introducing an
exercise-specific wrapper theorem.
-/
#check TikhonovDiscrepancy.isEquivalent_nonsaturated
#check TikhonovDiscrepancy.isEquivalent_critical
#check TikhonovDiscrepancy.isEquivalent_saturated
