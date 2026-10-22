/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_1_1.Iterates

public section

/-
Algorithm 3.1.1. Steepest descent with exact line search.

The reusable steepest-descent recurrence is owned by
`SteepestDescent.iterates`. The per-iteration exact line-search clause from the
algorithm is kept as the companion predicate
`SteepestDescent.IsExactLineSearch`, so downstream files can import the
iterative owner directly from `Book.Ch3.Algorithm_3_1_1.Iterates` without
pulling in the numbered item wrapper.
-/
#check SteepestDescent.iterates
