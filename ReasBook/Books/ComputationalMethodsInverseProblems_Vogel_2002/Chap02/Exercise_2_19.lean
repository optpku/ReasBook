/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Exercise_2_19.EuclideanQuadrant

public section

/- Exercise 2.19 (1). The nonnegative orthant in `EuclideanSpace ℝ (Fin n)` is convex. -/
#check EuclideanQuadrant.convex

/- Exercise 2.19 (2). The nonnegative orthant in `EuclideanSpace ℝ (Fin n)` is closed. -/
#check EuclideanQuadrant.isClosed_nonnegativeOrthant
