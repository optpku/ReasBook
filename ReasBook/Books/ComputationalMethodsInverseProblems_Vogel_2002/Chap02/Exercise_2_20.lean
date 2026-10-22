/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_28

public section

/- Exercise 2.20 (1). The set in Example 2.28 is convex. -/
#check RealL2.aeNonneg_isConvex

/- Exercise 2.20 (2). The set in Example 2.28 is closed. -/
#check RealL2.aeNonneg_isClosed
