/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Theorem_4_24

public section

/- Exercise 4.8. Prove Theorem 4.24.

This exercise asks for the proof of the already formalized discrete Bayes-rule theorem
for reverse conditional PMFs.
-/
#check ProbabilityTheory.JointPmf.condFstGivenSnd_apply_bayes
