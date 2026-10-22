/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_17

public section

/- The textbook pseudoinverse notation `K†` is represented in this repository
by the canonical owner `ContinuousLinearMap.pseudoInverse`. When `K` has closed
range, the corresponding source-facing bounded operator is exposed without
extra instance plumbing as `ContinuousLinearMap.pseudoInverseOfClosedRange`. -/
#check ContinuousLinearMap.pseudoInverse
#check ContinuousLinearMap.pseudoInverseOfClosedRange
#check ContinuousLinearMap.isLeastSquaresMinimumNormSolution_pseudoInverseOfClosedRange

/- Exercise 2.11. The source asks to use the open mapping theorem to show that
`K†` is bounded if and only if `K` has closed range.

In this repository, that statement is already formalized canonically by
`ContinuousLinearMap.exists_bounded_pseudoInverse_iff_isClosed_range`. -/
#check ContinuousLinearMap.exists_bounded_pseudoInverse_iff_isClosed_range
