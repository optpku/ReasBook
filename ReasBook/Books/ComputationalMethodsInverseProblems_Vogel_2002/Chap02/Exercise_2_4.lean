/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_4.Operator

public section

namespace RealL2

/- Exercise 2.4. The source asks to show that the adjoint `K*` of the Fredholm
kernel operator `K` from Example 2.4 is given by equation `(2.8)`.

The source-facing theorem is `IsKernelOperator.adjoint_isKernelOperator_swap`,
which states directly that the adjoint of a Fredholm realization again realizes
the swapped kernel. The equality theorem `kernelOperator_adjoint_eq_swap` is the
companion bridge obtained after fixing any realization of the swapped kernel. -/

#check IsKernelOperator.adjoint_isKernelOperator_swap

end RealL2
