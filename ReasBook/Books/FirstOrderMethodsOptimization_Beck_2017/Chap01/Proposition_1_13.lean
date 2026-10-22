/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_16
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_29

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix Matrix.Norms.Frobenius RealInnerProductSpace

noncomputable section

section

variable {m n k : ℕ}

/-- The canonical linear map `X ↦ (Tr(Aᵢᵀ X))ᵢ` from `ℝ^{m × n}` to `ℝ^k`. -/
def matrixTraceRepresentation (A : Fin k → Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin k) where
  toFun X := (EuclideanSpace.equiv (Fin k) ℝ).symm fun i ↦ Matrix.trace ((A i)ᵀ * X)
  map_add' X Y := by
    ext i
    simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by
    ext i
    simp [Matrix.mul_smul, Matrix.trace_smul]

/-- Evaluating `matrixTraceRepresentation A` at `X` gives the coordinate family
`i ↦ Tr(Aᵢᵀ X)`. -/
@[simp] theorem matrixTraceRepresentation_apply
    (A : Fin k → Matrix (Fin m) (Fin n) ℝ)
    (X : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin k) :
    matrixTraceRepresentation A X i = Matrix.trace ((A i)ᵀ * X) := by
  change
    ((EuclideanSpace.equiv (Fin k) ℝ)
      ((EuclideanSpace.equiv (Fin k) ℝ).symm fun j ↦ Matrix.trace ((A j)ᵀ * X))) i =
      Matrix.trace ((A i)ᵀ * X)
  simp

/-- Helper for Proposition 1.13: the trace of `((∑ i, y i • A i)ᵀ) * X` expands to the matching
finite coordinate sum. -/
private theorem trace_sum_smul_transpose_mul
    (A : Fin k → Matrix (Fin m) (Fin n) ℝ)
    (X : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin k)) :
    Matrix.trace (((∑ i, y i • A i)ᵀ) * X) =
      ∑ i, y i * Matrix.trace ((A i)ᵀ * X) := by
  rw [show (∑ i, y i • A i) = ∑ i ∈ Finset.univ, y i • A i by simp]
  rw [Matrix.transpose_sum, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul]
  simp [smul_eq_mul]

/-- The coordinate formula `𝒜 X i = Tr(Aᵢᵀ X)` identifies `𝒜` with the canonical owner
`matrixTraceRepresentation A`. -/
theorem eq_matrixTraceRepresentation
    {𝒜 : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {A : Fin k → Matrix (Fin m) (Fin n) ℝ}
    (h𝒜 : ∀ X i, 𝒜 X i = Matrix.trace ((A i)ᵀ * X)) :
    𝒜 = matrixTraceRepresentation A := by
  ext X i
  simpa using h𝒜 X i

/-- The canonical owner `matrixTraceRepresentation A` satisfies the defining adjoint identity
against the Euclidean inner product on `ℝ^k` and the Frobenius pairing on `ℝ^{m × n}`. -/
theorem matrixTraceRepresentation_adjoint
    (A : Fin k → Matrix (Fin m) (Fin n) ℝ)
    (X : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin k)) :
    ⟪matrixTraceRepresentation A X, y⟫ =
      Matrix.trace (((∑ i, y i • A i)ᵀ) * X) := by
  rw [euclideanSpace_inner_eq_sum_mul]
  trans ∑ i, y i * Matrix.trace ((A i)ᵀ * X)
  · refine Finset.sum_congr rfl ?_
    intro i hi
    rw [matrixTraceRepresentation_apply, mul_comm]
  · exact (trace_sum_smul_transpose_mul A X y).symm

/-- The adjoint of `matrixTraceRepresentation A` is the matrix combination `∑ i, yᵢ • Aᵢ`. -/
theorem matrixTraceRepresentation_adjoint_eq
    (A : Fin k → Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin k)) :
    (matrixTraceRepresentation A).adjoint y = ∑ i, y i • A i := by
  apply ext_inner_left ℝ
  intro X
  rw [LinearMap.adjoint_inner_right, Matrix.inner_eq_trace_transpose_mul]
  exact matrixTraceRepresentation_adjoint A X y

-- Proof sketch: expand the coordinate formula for `𝒜 X`, rewrite the Euclidean inner product with
-- `y` using `euclideanSpace_inner_eq_sum_mul`, and use linearity of `Matrix.trace` to identify the
-- resulting sum with the Frobenius pairing against `∑ i, y i • A i`.
/-- Proposition 1.13: if a linear map from `ℝ^{m × n}` to `ℝ^k` is given coordinatewise by the
trace pairings `X ↦ Tr(A_iᵀ X)`, then the matrix `∑ i, y_i • A_i` satisfies the defining adjoint
identity against the canonical Euclidean inner product on `ℝ^k` and the Frobenius pairing on
`ℝ^{m × n}`. -/
theorem matrix_trace_representation_adjoint
    {𝒜 : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {A : Fin k → Matrix (Fin m) (Fin n) ℝ}
    (h𝒜 : ∀ X i, 𝒜 X i = Matrix.trace ((A i)ᵀ * X))
    (X : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin k)) :
    ⟪𝒜 X, y⟫ = Matrix.trace (((∑ i, y i • A i)ᵀ) * X) := by
  rw [eq_matrixTraceRepresentation h𝒜]
  exact matrixTraceRepresentation_adjoint A X y

/-- Sum-form companion to `matrix_trace_representation_adjoint`. -/
theorem matrix_trace_representation_adjoint_spec
    {𝒜 : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {A : Fin k → Matrix (Fin m) (Fin n) ℝ}
    (h𝒜 : ∀ X i, 𝒜 X i = Matrix.trace ((A i)ᵀ * X))
    (X : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin k)) :
    ∑ i, (𝒜 X) i * y i = Matrix.trace (((∑ i, y i • A i)ᵀ) * X) := by
  simpa [euclideanSpace_inner_eq_sum_mul] using
    matrix_trace_representation_adjoint h𝒜 X y

/-- Canonical adjoint-form companion to `matrix_trace_representation_adjoint`. -/
theorem matrix_trace_representation_adjoint_eq
    {𝒜 : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {A : Fin k → Matrix (Fin m) (Fin n) ℝ}
    (h𝒜 : ∀ X i, 𝒜 X i = Matrix.trace ((A i)ᵀ * X))
    (y : EuclideanSpace ℝ (Fin k)) :
    𝒜.adjoint y = ∑ i, y i • A i := by
  rw [eq_matrixTraceRepresentation h𝒜]
  exact matrixTraceRepresentation_adjoint_eq A y

end
