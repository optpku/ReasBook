/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_1.Spectrum
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_1.Positive
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Topology.Algebra.Module.FiniteDimension

public section

universe u

section

variable {n : Type u} [Fintype n] [DecidableEq n]

/-!
Example 2.1. Clauses (1) through (6) are direct checks of the canonical
mathlib owners for the Euclidean inner product, the induced norm, boundedness
of linear maps in finite dimension, orthonormal-basis matrix coefficients,
adjoints, and the matrix criterion for self-adjointness. Clauses (7) through
(9) reuse the Example 2.1 item-owned foundations
`Book.Ch2.Example_2_1.Spectrum` and `Book.Ch2.Example_2_1.Positive` for the
source quantities `λ_min(A)`, `λ_max(A)`, and the positive-definite/operator
comparison.
-/

/- Clause (1): `EuclideanSpace ℝ n` carries the Euclidean inner product. -/
#check EuclideanSpace.inner_eq_star_dotProduct

/- Clause (2): the induced norm is the Euclidean norm. -/
#check EuclideanSpace.norm_eq

/- Clause (3): every linear operator on `ℝ^n` is bounded. -/
#check LinearMap.continuous_of_finiteDimensional

/- Clause (4): the orthonormal-basis matrix entries are given by the inner-product formula. -/
#check LinearMap.toMatrixOrthonormal_apply_apply

/- Clause (5): `LinearMap.toMatrix_adjoint` is the canonical orthonormal-basis
formula; over `ℝ` it specializes to the transpose statement from the source. -/
#check LinearMap.toMatrix_adjoint

/- Clause (6): `LinearMap.isHermitian_toMatrix_iff` gives the orthonormal-basis
matrix characterization of self-adjointness; over `ℝ`, Hermitian means
symmetric. -/
#check LinearMap.isHermitian_toMatrix_iff

/- Clause (7): the source quantity `λ_min(A)` is owned by `Matrix.lambdaMin`; for symmetric real
matrices it is an eigenvalue of `A.toEuclideanLin`. -/
#check Matrix.lambdaMin
#check Matrix.IsHermitian.hasEigenvalue_lambdaMin

/- Clause (8): the source quantity `λ_max(A)` is owned by `Matrix.lambdaMax`; for symmetric real
matrices it is an eigenvalue of `A.toEuclideanLin`. -/
#check Matrix.lambdaMax
#check Matrix.IsHermitian.hasEigenvalue_lambdaMax

/- Clause (9): for real matrices, positive definiteness is equivalent to the induced continuous
operator being self-adjoint and strongly positive. -/
#check Matrix.posDef_iff_selfAdjointStronglyPositive_toEuclideanCLM

/-- Example 2.1. A Hermitian real matrix on `EuclideanSpace ℝ n` has both
`λ_min(A)` and `λ_max(A)` as eigenvalues of the induced linear operator. -/
theorem hermitian_hasEigenvalue_lambdaMin_and_lambdaMax [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    Module.End.HasEigenvalue (A.toEuclideanLin) (Matrix.lambdaMin A) ∧
      Module.End.HasEigenvalue (A.toEuclideanLin) (Matrix.lambdaMax A) := by
  -- Clause (7) and clause (8) are imported from the item-owned spectral API.
  exact ⟨by simpa using hA.hasEigenvalue_lambdaMin, by simpa using hA.hasEigenvalue_lambdaMax⟩

end
