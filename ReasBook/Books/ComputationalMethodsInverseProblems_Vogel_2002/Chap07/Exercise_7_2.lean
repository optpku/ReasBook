/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Exercise_7_1

public section

/- Exercise 7.2. Use the results of Exercise 7.1 to verify equations `(7.17)`
and `(7.18)`.

Equation `(7.17)` is verified by `influenceMatrix_eq_spectralRep`, and
equation `(7.18)` is verified by `influenceMatrix_isSymm_of_filterRep`. -/

#check influenceMatrix_eq_spectralRep
#check influenceMatrix_isSymm_of_filterRep

end
