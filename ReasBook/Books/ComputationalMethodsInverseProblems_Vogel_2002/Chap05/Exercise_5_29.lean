/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Exercise_5_28.Permutation
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_30
public import Mathlib.LinearAlgebra.Matrix.Reindex

public section

/-!
Exercise 5.29. Refine-stage source-facing blocker.

The local Chapter 5 source around equation `(5.83)` prints the matrix identity
`((I_y ⊗ F_y) P (I_y ⊗ F_x)) = F_y ⊗ F_x`. In the current repository's
`n_x × n_y` setup, that left factor is dimensionally inconsistent as written,
so this item cannot be promoted to a faithful theorem by silently correcting
the factor order or by inferring a reindexed rowwise Fourier action.

Accordingly this file remains a labeled blocker until a verified source
correction, or a trusted indexing convention that makes `(5.83)` precise, is
available. The checks below record only verified nearby owners already present
in the repository.
-/

/- Exercise 5.29. Main labeled blocker/check entry.

Equation `(5.83)` remains blocked in the current snapshot because the printed
matrix product is not a faithful well-typed identity under the repository's
Chapter 5 vectorization and permutation conventions. Once the source equation
is corrected or its indexing convention is anchored from trusted material,
replace this blocker/check surface with exactly one thin source-faithful
theorem over the existing Chapter 5 Fourier, Kronecker, permutation, and
reindex owners.

The `#check` entries below record only those verified owners. They preserve the
exercise's intended mathematical neighborhood without asserting a guessed
equation or weakening the item to a vacuous proposition. -/
#check Matrix.fourierMatrix

#check Matrix.kronecker

#check Matrix.columnToRowPermMatrix

#check Matrix.columnToRowPermMatrix_mulVec

#check Matrix.reindex

#check Matrix.dft2D_eq_of_kronFourier_mulVec

end
