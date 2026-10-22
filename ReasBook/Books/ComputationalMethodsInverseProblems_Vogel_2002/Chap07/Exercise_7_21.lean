/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_25

public section

/- Exercise 7.21. The source asks the reader to prove Theorem 7.25. In this
repository, that theorem is recorded directly by the TSVD discrepancy-choice
comparison below, so the exercise is formalized by direct reuse of the
theorem-level Chapter 7 surface rather than by repeating its statement. -/
#check TsvdDiscrepancy.isEquivalent_indexBenchmark
#check TsvdDiscrepancy.isTheta_indexBenchmark

end
