/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_8_extra_1
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "JacobianMap" => Point →L[ℝ] Point
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- The generalized-Jacobian owner is `Definition_14_8_extra_1.generalizedJacobian`, with the
-- matrix coordinate surface `generalizedJacobianMatrix` used here for Newton steps that invert
-- selected matrices.

/-- The nonsmooth Newton update `x - V⁻¹(F x)` from `(14.8.18)` for a selected nonsingular
matrix `V`. -/
def nonsmoothNewtonStep (F : Point → Point) (x : Point) (V : MatrixN) : Point :=
  x - Matrix.toEuclideanLin V⁻¹ (F x)

/-- Unfolding `nonsmoothNewtonStep F x V` gives the source formula `x - V⁻¹(F x)` for a
selected matrix `V`. -/
theorem nonsmoothNewtonStep_eq
    (F : Point → Point) (x : Point) (V : MatrixN) :
    nonsmoothNewtonStep F x V = x - Matrix.toEuclideanLin V⁻¹ (F x) := rfl

/-- Chapter14 Algorithm 14.8-extra-5: for a map `F : ℝ^n → ℝ^n`, a nonsmooth Newton method
records an iterate sequence `x_k` and, at each stage `k`, a selected matrix
`V_k ∈ generalizedJacobianMatrix F (x_k)` that is nonsingular. The next iterate is given by the
source update `x_(k + 1) = x_k - V_k⁻¹(F(x_k))`, used as a nonsmooth replacement for the
smooth Newton step when solving `F x = 0`. In later convergence statements, local Lipschitz
regularity of `F` is an ambient assumption rather than part of this algorithmic data. -/
structure NonsmoothNewtonMethod (n : ℕ) where
  map : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  iterate : ℕ → EuclideanSpace ℝ (Fin n)
  selectedMatrix : ℕ → Matrix (Fin n) (Fin n) ℝ
  selectedMatrix_mem :
    ∀ k, selectedMatrix k ∈ generalizedJacobianMatrix map (iterate k)
  selectedMatrix_nonsingular :
    ∀ k, IsUnit (selectedMatrix k)
  iterate_succ :
    ∀ k,
      iterate (k + 1) =
        nonsmoothNewtonStep map (iterate k) (selectedMatrix k)

namespace NonsmoothNewtonMethod

/-- A nonsmooth Newton method can be evaluated at stage `k` as its iterate `x_k`. -/
instance : CoeFun (NonsmoothNewtonMethod n) (fun _ ↦ ℕ → Point) where
  coe method := method.iterate

/-- The initial point of a nonsmooth Newton method is its stage-`0` iterate. -/
abbrev initialPoint (method : NonsmoothNewtonMethod n) : Point := method.iterate 0

/-- The intrinsic generalized-Jacobian operator selected at stage `k`, obtained from the stored
matrix representative by the canonical Euclidean matrix/operator equivalence. -/
abbrev selectedOperator (method : NonsmoothNewtonMethod n) (k : ℕ) : JacobianMap :=
  jacobianMapOfMatrix (method.selectedMatrix k)

theorem jacobianMapOfMatrix_eq_toEuclideanCLM (V : MatrixN) :
    jacobianMapOfMatrix V = (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] JacobianMap) V := by
  ext x i
  simp [jacobianMapOfMatrix]

@[simp] theorem jacobianMapOfMatrix_mul (A B : MatrixN) :
    jacobianMapOfMatrix (A * B) = jacobianMapOfMatrix A ∘L jacobianMapOfMatrix B := by
  rw [jacobianMapOfMatrix_eq_toEuclideanCLM, jacobianMapOfMatrix_eq_toEuclideanCLM,
    jacobianMapOfMatrix_eq_toEuclideanCLM]
  exact (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] JacobianMap).map_mul A B

@[simp] theorem jacobianMapOfMatrix_one :
    jacobianMapOfMatrix (1 : MatrixN) = ContinuousLinearMap.id ℝ Point := by
  ext x i
  simp [jacobianMapOfMatrix, Matrix.toEuclideanLin_eq_toLin_orthonormal]

/-- Evaluating `method` as a function returns its iterate sequence. -/
theorem coe_apply (method : NonsmoothNewtonMethod n) (k : ℕ) :
    method k = method.iterate k := rfl

@[simp] theorem initialPoint_eq (method : NonsmoothNewtonMethod n) :
    method.initialPoint = method.iterate 0 := rfl

@[simp] theorem jacobianMatrixOfMap_selectedOperator
    (method : NonsmoothNewtonMethod n) (k : ℕ) :
    jacobianMatrixOfMap (method.selectedOperator k) = method.selectedMatrix k := by
  simp [NonsmoothNewtonMethod.selectedOperator]

/-- At each stage `k`, the recorded matrix `V_k` belongs to the generalized Jacobian
`generalizedJacobianMatrix method.map (method.iterate k)`. -/
theorem selectedMatrix_mem_at (method : NonsmoothNewtonMethod n) (k : ℕ) :
    method.selectedMatrix k ∈ generalizedJacobianMatrix method.map (method.iterate k) :=
  method.selectedMatrix_mem k

/-- At each stage `k`, the recorded matrix `V_k` is the standard-basis matrix of some
generalized-Jacobian map at the current iterate. -/
theorem exists_selectedJacobianMap
    (method : NonsmoothNewtonMethod n) (k : ℕ) :
    ∃ A : JacobianMap,
      A ∈ generalizedJacobian method.map (method.iterate k) ∧
        jacobianMatrixOfMap A = method.selectedMatrix k := by
  rcases
      (mem_generalizedJacobianMatrix_iff
        method.map (method.iterate k) (method.selectedMatrix k)).1
        (method.selectedMatrix_mem_at k) with
    ⟨A, hA, hMatrix⟩
  exact ⟨A, hA, hMatrix⟩

/-- At each stage `k`, the recorded matrix `V_k` is nonsingular. -/
theorem selectedMatrix_nonsingular_at (method : NonsmoothNewtonMethod n) (k : ℕ) :
    IsUnit (method.selectedMatrix k) :=
  method.selectedMatrix_nonsingular k

/-- At each stage `k`, the intrinsic selected operator belongs to the generalized Jacobian
`generalizedJacobian method.map (method.iterate k)`. -/
theorem selectedOperator_mem_at (method : NonsmoothNewtonMethod n) (k : ℕ) :
    method.selectedOperator k ∈ generalizedJacobian method.map (method.iterate k) := by
  rcases method.exists_selectedJacobianMap k with ⟨A, hA, hEq⟩
  have h_selected : method.selectedOperator k = A := by
    rw [NonsmoothNewtonMethod.selectedOperator, ← hEq, jacobianMapOfMatrix_jacobianMatrixOfMap]
  simpa [h_selected] using hA

/-- At each stage `k`, the intrinsic selected operator is invertible. -/
theorem selectedOperator_isInvertible_at (method : NonsmoothNewtonMethod n) (k : ℕ) :
    (method.selectedOperator k).IsInvertible := by
  rcases method.selectedMatrix_nonsingular_at k with ⟨u, hu⟩
  have hmul : method.selectedMatrix k * (method.selectedMatrix k)⁻¹ = (1 : MatrixN) := by
    rw [← hu]
    simp
  have hmul' : (method.selectedMatrix k)⁻¹ * method.selectedMatrix k = (1 : MatrixN) := by
    rw [← hu]
    simp
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := jacobianMapOfMatrix (method.selectedMatrix k)⁻¹) ?_ ?_
  · calc
      method.selectedOperator k ∘L jacobianMapOfMatrix (method.selectedMatrix k)⁻¹
          = jacobianMapOfMatrix (method.selectedMatrix k * (method.selectedMatrix k)⁻¹) := by
              rw [NonsmoothNewtonMethod.selectedOperator, ← jacobianMapOfMatrix_mul]
      _ = jacobianMapOfMatrix (1 : MatrixN) := by rw [hmul]
      _ = ContinuousLinearMap.id ℝ Point := jacobianMapOfMatrix_one
  · calc
      jacobianMapOfMatrix (method.selectedMatrix k)⁻¹ ∘L method.selectedOperator k
          = jacobianMapOfMatrix ((method.selectedMatrix k)⁻¹ * method.selectedMatrix k) := by
              rw [NonsmoothNewtonMethod.selectedOperator, ← jacobianMapOfMatrix_mul]
      _ = jacobianMapOfMatrix (1 : MatrixN) := by rw [hmul']
      _ = ContinuousLinearMap.id ℝ Point := jacobianMapOfMatrix_one

@[simp] theorem selectedOperator_inverse_eq
    (method : NonsmoothNewtonMethod n) (k : ℕ) :
    (method.selectedOperator k).inverse = jacobianMapOfMatrix (method.selectedMatrix k)⁻¹ := by
  rcases method.selectedMatrix_nonsingular_at k with ⟨u, hu⟩
  have hmul : method.selectedMatrix k * (method.selectedMatrix k)⁻¹ = (1 : MatrixN) := by
    rw [← hu]
    simp
  have hmul' : (method.selectedMatrix k)⁻¹ * method.selectedMatrix k = (1 : MatrixN) := by
    rw [← hu]
    simp
  apply ContinuousLinearMap.inverse_eq
  · calc
      method.selectedOperator k ∘L jacobianMapOfMatrix (method.selectedMatrix k)⁻¹
          = jacobianMapOfMatrix (method.selectedMatrix k * (method.selectedMatrix k)⁻¹) := by
              rw [NonsmoothNewtonMethod.selectedOperator, ← jacobianMapOfMatrix_mul]
      _ = jacobianMapOfMatrix (1 : MatrixN) := by rw [hmul]
      _ = ContinuousLinearMap.id ℝ Point := jacobianMapOfMatrix_one
  · calc
      jacobianMapOfMatrix (method.selectedMatrix k)⁻¹ ∘L method.selectedOperator k
          = jacobianMapOfMatrix ((method.selectedMatrix k)⁻¹ * method.selectedMatrix k) := by
              rw [NonsmoothNewtonMethod.selectedOperator, ← jacobianMapOfMatrix_mul]
      _ = jacobianMapOfMatrix (1 : MatrixN) := by rw [hmul']
      _ = ContinuousLinearMap.id ℝ Point := jacobianMapOfMatrix_one

/-- The recorded iterate sequence satisfies the nonsmooth Newton update
`x_(k + 1) = x_k - V_k⁻¹(F(x_k))`. -/
theorem iterate_succ_eq (method : NonsmoothNewtonMethod n) (k : ℕ) :
    method.iterate (k + 1) =
      nonsmoothNewtonStep method.map (method.iterate k) (method.selectedMatrix k) :=
  method.iterate_succ k

end NonsmoothNewtonMethod

#print axioms nonsmoothNewtonStep
#print axioms NonsmoothNewtonMethod

end
