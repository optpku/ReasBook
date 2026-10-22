/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Theorem_9_7

public section

/- Exercise 9.2. The source asks for proofs of the two clauses of Theorem 9.7.
Those clauses are already formalized in Chapter 9 as the source-facing theorem
owners below, so this exercise file records direct reuse rather than
introducing an exercise-specific wrapper theorem. -/

/- Exercise 9.2 (1).

The existence-and-uniqueness clause of Theorem 9.7 is formalized by
`existsUniqueMetricProjection`.
-/
#check existsUniqueMetricProjection

/- Exercise 9.2 (2).

The continuity clause of Theorem 9.7 is formalized by
`continuousMetricProjection`.
-/
#check continuousMetricProjection
