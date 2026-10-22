/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Example_6_2.DiffusionMatrices

public section

/- Exercise 6.6

Verify the matrix decomposition `(6.29)`, namely the weighted Gram factorization
of `OneDimensionalDiffusion.stiffnessMatrix`.
-/

#check OneDimensionalDiffusion.stiffnessMatrix_eqWeightedGram
