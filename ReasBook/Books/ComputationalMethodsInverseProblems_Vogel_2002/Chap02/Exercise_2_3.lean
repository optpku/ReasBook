/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_4.Operator

public section

/- Exercise 2.3. The source asks for boundedness of the Fredholm kernel
operator from Example 2.4 under the square-integrable-kernel hypothesis and
for the estimate `‖K‖ ≤ √B`, where `B` is the kernel energy integral on
`Ω × Ω`.

This is already formalized in the canonical owner module by
`RealL2.kernelOperator_norm_le`, which gives the bound for any realization
`K : L²(Ω) →L[ℝ] L²(Ω)` of that Fredholm kernel. -/

#check RealL2.kernelOperator_norm_le
