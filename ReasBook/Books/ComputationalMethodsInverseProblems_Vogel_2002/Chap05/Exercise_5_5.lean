/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Exercise_5_4

public section

/- Exercise 5.5. The Chapter 5 Fourier matrix `Matrix.fourierMatrix n` is already
formalized as unitary by `Matrix.fourierMatrix_mem_unitaryGroup`, with canonical
packaging as `Matrix.fourierUnitary n`. The hint's equation view is the existing
theorem `Matrix.fourierMatrix_conjTranspose_mul`, and the finite geometric-sum
step is supplied by `Matrix.fourierRoot_orthogonality` from Exercise 5.4. -/

#check Matrix.fourierMatrix_mem_unitaryGroup
#check Matrix.fourierUnitary
#check Matrix.fourierMatrix_conjTranspose_mul
#check Matrix.fourierRoot_orthogonality
