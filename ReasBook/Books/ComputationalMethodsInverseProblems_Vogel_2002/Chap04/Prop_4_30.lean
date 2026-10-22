/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Matrix.Spectrum

public section

universe u

namespace Matrix.IsSymm

variable {n : Type u} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- Proposition 4.30. If `A` is symmetric, then `Matrix.trace A` is the sum of
the eigenvalues of `A`, indexed by the matrix index type through
`(Matrix.isHermitian_iff_isSymm.2 hA).eigenvalues`. -/
theorem trace_eq_sum_eigenvalues (hA : A.IsSymm) :
    A.trace = ∑ i, (Matrix.isHermitian_iff_isSymm.2 hA).eigenvalues i := by
  simpa using (Matrix.isHermitian_iff_isSymm.2 hA).trace_eq_sum_eigenvalues

end Matrix.IsSymm
