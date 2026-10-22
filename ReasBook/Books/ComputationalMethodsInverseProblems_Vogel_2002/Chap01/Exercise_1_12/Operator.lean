/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_5
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

noncomputable section

open scoped Matrix

namespace Tikhonov

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The Tikhonov operator matrix `(Kᵀ * K + α • 1)⁻¹ * Kᵀ`. -/
def operator (K : Matrix n n ℝ) (α : ℝ) : Matrix n n ℝ :=
  (Kᵀ * K + α • (1 : Matrix n n ℝ))⁻¹ * Kᵀ

/-- The defining formula for `Tikhonov.operator`. -/
theorem operator_def (K : Matrix n n ℝ) (α : ℝ) :
    operator K α = (Kᵀ * K + α • (1 : Matrix n n ℝ))⁻¹ * Kᵀ := by
  simp [operator]

/-- Rewriting the scalar Tikhonov filter factor into the textbook ratio form. -/
theorem filterScalar_eq_ratio (α s : ℝ) :
    SpectralFilter.tikhonov α (s ^ 2) / s = s / (s ^ 2 + α) := by
  by_cases hs : s = 0
  · subst hs
    simp [SpectralFilter.tikhonov]
  · simpa [add_comm] using SpectralFilter.tikhonovAtSquare_div_eq_ratio hs

/-- Under an orthogonal SVD `K = U * Matrix.diagonal s * Vᵀ` and `0 < α`, the
Tikhonov operator matrix agrees with the diagonal spectral-filter representation. -/
theorem operator_eq_svdFilter
    (K U V : Matrix n n ℝ) (s : n → ℝ) (α : ℝ)
    (hα_pos : 0 < α)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    operator K α =
      V * Matrix.diagonal (fun i ↦ SpectralFilter.tikhonov α (s i ^ 2) / s i) * Uᵀ := by
  let diagSq : n → ℝ := fun i ↦ s i ^ 2
  let diagShift : n → ℝ := fun i ↦ s i ^ 2 + α
  have hVtV : Vᵀ * V = 1 := (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).mp hV
  have hVVt : V * Vᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).mp hV
  have hUtU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).mp hU
  have hKt :
      Kᵀ = V * Matrix.diagonal s * Uᵀ := by
    rw [hK]
    simp [Matrix.mul_assoc, Matrix.diagonal_transpose]
  have hGram :
      Kᵀ * K = V * Matrix.diagonal diagSq * Vᵀ := by
    -- Compute the source-space Gramian in the right singular basis.
    calc
      Kᵀ * K = (V * Matrix.diagonal s * Uᵀ) * (U * Matrix.diagonal s * Vᵀ) := by
        rw [hKt, hK]
      _ = V * (Matrix.diagonal s * (Uᵀ * U) * Matrix.diagonal s) * Vᵀ := by
        simp [Matrix.mul_assoc]
      _ = V * (Matrix.diagonal s * Matrix.diagonal s) * Vᵀ := by
        rw [hUtU]
        simp [Matrix.mul_assoc]
      _ = V * Matrix.diagonal diagSq * Vᵀ := by
        rw [Matrix.diagonal_mul_diagonal]
        simp [diagSq, pow_two, Matrix.mul_assoc]
  have hDiagConst :
      Matrix.diagonal (fun _ : n ↦ α) = α • (1 : Matrix n n ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hDiagAdd :
      Matrix.diagonal diagSq + Matrix.diagonal (fun _ : n ↦ α) =
        Matrix.diagonal diagShift := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [diagSq, diagShift]
    · simp [hij]
  have hScalar :
      α • (1 : Matrix n n ℝ) = V * Matrix.diagonal (fun _ : n ↦ α) * Vᵀ := by
    -- Reinsert the identity as `V * Vᵀ` so the scalar shift uses the same basis.
    calc
      α • (1 : Matrix n n ℝ) = α • (V * Vᵀ) := by rw [hVVt]
      _ = V * (α • (1 : Matrix n n ℝ)) * Vᵀ := by
        simp
      _ = V * Matrix.diagonal (fun _ : n ↦ α) * Vᵀ := by
        rw [← hDiagConst]
  have hShift :
      Kᵀ * K + α • (1 : Matrix n n ℝ) = V * Matrix.diagonal diagShift * Vᵀ := by
    -- The shifted Gramian stays diagonal in the right singular basis.
    calc
      Kᵀ * K + α • (1 : Matrix n n ℝ)
          = V * Matrix.diagonal diagSq * Vᵀ + V * Matrix.diagonal (fun _ : n ↦ α) * Vᵀ := by
              rw [hGram, hScalar]
      _ = V * (Matrix.diagonal diagSq + Matrix.diagonal (fun _ : n ↦ α)) * Vᵀ := by
            calc
              V * Matrix.diagonal diagSq * Vᵀ + V * Matrix.diagonal (fun _ : n ↦ α) * Vᵀ
                  = (V * Matrix.diagonal diagSq) * Vᵀ +
                      (V * Matrix.diagonal (fun _ : n ↦ α)) * Vᵀ := by
                        simp [Matrix.mul_assoc]
              _ = (V * (Matrix.diagonal diagSq + Matrix.diagonal (fun _ : n ↦ α))) * Vᵀ := by
                    rw [← Matrix.add_mul, ← Matrix.mul_add]
              _ = V * (Matrix.diagonal diagSq + Matrix.diagonal (fun _ : n ↦ α)) * Vᵀ := by
                    simp [Matrix.mul_assoc]
      _ = V * Matrix.diagonal diagShift * Vᵀ := by
            simpa using congrArg (fun M ↦ V * M * Vᵀ) hDiagAdd
  have hDiagInv :
      Matrix.diagonal diagShift * Matrix.diagonal (fun i ↦ (diagShift i)⁻¹) = 1 := by
    -- Positive diagonal entries invert coordinatewise.
    ext i j
    by_cases hij : i = j
    · subst hij
      have hshift_pos : 0 < diagShift i := by
        dsimp [diagShift]
        positivity
      simp [diagShift, hshift_pos.ne']
    · simp [hij]
  have hShiftInv :
      (Kᵀ * K + α • (1 : Matrix n n ℝ))⁻¹ =
        V * Matrix.diagonal (fun i ↦ (diagShift i)⁻¹) * Vᵀ := by
    -- The inverse of an orthogonal diagonalization is the same basis with reciprocal diagonal.
    rw [hShift]
    apply Matrix.inv_eq_right_inv
    calc
      (V * Matrix.diagonal diagShift * Vᵀ) *
          (V * Matrix.diagonal (fun i ↦ (diagShift i)⁻¹) * Vᵀ)
          = V *
              (Matrix.diagonal diagShift * (Vᵀ * V) *
                Matrix.diagonal (fun i ↦ (diagShift i)⁻¹)) *
              Vᵀ := by
                simp [Matrix.mul_assoc]
      _ = V *
            (Matrix.diagonal diagShift *
              Matrix.diagonal (fun i ↦ (diagShift i)⁻¹)) *
            Vᵀ := by
              rw [hVtV]
              simp [Matrix.mul_assoc]
      _ = V * 1 * Vᵀ := by rw [hDiagInv]
      _ = 1 := by simp [hVVt]
  have hCoeffDiag :
      Matrix.diagonal (fun i ↦ (diagShift i)⁻¹ * s i) =
        Matrix.diagonal (fun i ↦ SpectralFilter.tikhonov α (s i ^ 2) / s i) := by
    -- Normalize the diagonal coefficient to the scalar Tikhonov filter spelling.
    ext i j
    by_cases hij : i = j
    · subst hij
      have hcoeff : (diagShift i)⁻¹ * s i = SpectralFilter.tikhonov α (s i ^ 2) / s i := by
        by_cases hs : s i = 0
        · rw [hs]
          simp [SpectralFilter.tikhonov, diagShift]
        · rw [SpectralFilter.tikhonov]
          field_simp [hs, diagShift]
          ring
      simpa using hcoeff
    · simp [Matrix.diagonal_apply_ne _ hij]
  -- Multiply the reciprocal shifted Gramian by `Kᵀ` and cancel the orthogonal middle factor.
  calc
    operator K α
        = (V * Matrix.diagonal (fun i ↦ (diagShift i)⁻¹) * Vᵀ) *
            (V * Matrix.diagonal s * Uᵀ) := by
              rw [operator_def, hShiftInv, hKt]
    _ = V * (Matrix.diagonal (fun i ↦ (diagShift i)⁻¹) * (Vᵀ * V) * Matrix.diagonal s) * Uᵀ := by
          simp [Matrix.mul_assoc]
    _ = V * (Matrix.diagonal (fun i ↦ (diagShift i)⁻¹) * Matrix.diagonal s) * Uᵀ := by
          rw [hVtV]
          simp [Matrix.mul_assoc]
    _ = V * Matrix.diagonal (fun i ↦ (diagShift i)⁻¹ * s i) * Uᵀ := by
          rw [Matrix.diagonal_mul_diagonal]
    _ = V * Matrix.diagonal (fun i ↦ SpectralFilter.tikhonov α (s i ^ 2) / s i) * Uᵀ := by
          rw [hCoeffDiag]

/-- Applying the SVD/filter representation of `Tikhonov.operator` to a data vector in
`EuclideanSpace` under the regularization condition `0 < α`. -/
theorem operator_apply_eq_svdFilter
    (K U V : Matrix n n ℝ) (s : n → ℝ) (α : ℝ) (d : EuclideanSpace ℝ n)
    (hα_pos : 0 < α)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    Matrix.toEuclideanLin (operator K α) d =
      Matrix.toEuclideanLin
        (V * Matrix.diagonal (fun i ↦ SpectralFilter.tikhonov α (s i ^ 2) / s i) * Uᵀ) d := by
  -- Apply the matrix identity from `operator_eq_svdFilter` to the chosen data vector.
  simpa using congrArg (fun M ↦ Matrix.toEuclideanLin M d)
    (operator_eq_svdFilter K U V s α hα_pos hU hV hK)

end Tikhonov
