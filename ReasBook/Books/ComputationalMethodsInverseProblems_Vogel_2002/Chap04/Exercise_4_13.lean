/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Prop_4_30

public section

/- Exercise 4.13.

This exercise is direct canonical reuse of the existing real-symmetric
trace-eigenvalue identity. The orthogonal eigendecomposition mentioned in the
text is a proof route, not part of the public statement surface for this item.
-/
#check Matrix.IsSymm.trace_eq_sum_eigenvalues
