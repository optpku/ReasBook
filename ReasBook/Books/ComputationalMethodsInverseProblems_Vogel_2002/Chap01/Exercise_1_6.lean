/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2

public section

/-!
Statement-stage canonical reuse for Exercise 1.6.
-/

/- Exercise 1.6. Using `(1.18)` and Exercise 1.5, equation `(1.22)` is the
canonical Chapter 1 noise-amplification bound already formalized as
`FilterRegularization.noiseError_norm_le`. -/
#check FilterRegularization.noiseError_norm_le
