/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_25.Array

public section

/-!
Definition 5.25 is the matrix reconstruction operation inverse to `Matrix.vec`.
Its canonical owner is the existing matrix constructor `Matrix.of`; the
reusable foundation module `Book.Ch5.Definition_5_25.Array` only records the
swapped-product bridge the source uses for column-stacked arrays.
-/

/- Definition 5.25. Source-facing bridge to the canonical reconstruction owner
`Matrix.of` and the immediate companion API relating it to `Matrix.vec` for
column-stacked arrays indexed by `Fin n_y × Fin n_x`. -/
#check Matrix.of
#check Matrix.of_apply
#check Matrix.of_vec
#check Matrix.vec_of_swap
