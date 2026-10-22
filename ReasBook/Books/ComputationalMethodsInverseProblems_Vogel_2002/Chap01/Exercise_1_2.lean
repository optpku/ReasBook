/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2.Operator

public section

noncomputable section

open scoped Matrix

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

private theorem toEuclideanLin_mul_apply
    (A B : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) =
      Matrix.toEuclideanLin (A * B) x := by
  ext i
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- Companion API for Exercise 1.2: the explicit inverse SVD reconstruction
matrix is the constant-filter specialization of
`FilterRegularization.operatorMatrix`. -/
theorem svdInverseMatrix_eq_operatorMatrix
    (U V : Matrix n n ℝ) (s : n → ℝ) :
    V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ =
      FilterRegularization.operatorMatrix U V s (fun _ _ ↦ (1 : ℝ)) 0 := by
  simp [FilterRegularization.operatorMatrix_def]

/-- Exercise 1.2. Under the square finite-dimensional SVD setup
`K = U * Matrix.diagonal s * Vᵀ`, with orthogonal factors `U` and `V`, strictly
positive singular values, and noisy data
`d = Matrix.toEuclideanLin K fTrue + η`, equation `(1.9)` is the explicit SVD
inverse reconstruction formula
`V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ`, rewritten as the true signal plus
the singular-value-weighted noise term. -/
theorem svdInverse_eq_true_add_noise
    (K U V : Matrix n n ℝ) (s : n → ℝ)
    (fTrue d η : EuclideanSpace ℝ n)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i)
    (h_data : d = Matrix.toEuclideanLin K fTrue + η) :
    Matrix.toEuclideanLin
        (V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ) d =
      fTrue +
        Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin
            (Matrix.diagonal (fun i ↦ (s i)⁻¹))
            (Matrix.toEuclideanLin Uᵀ η)) := by
  have hUtU : Uᵀ * U = 1 :=
    (Matrix.mem_orthogonalGroup_iff' n ℝ).1 hU
  have hVVt : V * Vᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff n ℝ).1 hV
  have hDiagInv :
      Matrix.diagonal (fun i ↦ (s i)⁻¹) * Matrix.diagonal s = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [(hs_pos i).ne']
    · simp [hij]
  have hInverseMul :
      (V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ) * K = 1 := by
    calc
      (V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ) * K
          = (V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ) *
              (U * Matrix.diagonal s * Vᵀ) := by rw [hK]
      _ =
          V *
            (Matrix.diagonal (fun i ↦ (s i)⁻¹) * (Uᵀ * U) * Matrix.diagonal s) *
            Vᵀ := by simp [Matrix.mul_assoc]
      _ = V * (Matrix.diagonal (fun i ↦ (s i)⁻¹) * Matrix.diagonal s) * Vᵀ := by
            rw [hUtU]
            simp [Matrix.mul_assoc]
      _ = V * 1 * Vᵀ := by rw [hDiagInv]
      _ = 1 := by simp [hVVt]
  have hSignal :
      Matrix.toEuclideanLin
          (V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ)
          (Matrix.toEuclideanLin K fTrue) =
        fTrue := by
    calc
      Matrix.toEuclideanLin
          (V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ)
          (Matrix.toEuclideanLin K fTrue)
          =
        Matrix.toEuclideanLin
          ((V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ) * K) fTrue := by
            rw [toEuclideanLin_mul_apply]
      _ = fTrue := by
            rw [hInverseMul]
            simp [Matrix.toEuclideanLin]
  have hNoise :
      Matrix.toEuclideanLin (V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ) η =
        Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin
            (Matrix.diagonal (fun i ↦ (s i)⁻¹))
            (Matrix.toEuclideanLin Uᵀ η)) := by
    calc
      Matrix.toEuclideanLin (V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ) η
          = Matrix.toEuclideanLin
              (V * (Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ)) η := by
                simp [Matrix.mul_assoc]
      _ = Matrix.toEuclideanLin V
            (Matrix.toEuclideanLin (Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ) η) := by
              rw [(toEuclideanLin_mul_apply V
                (Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ) η).symm]
      _ = Matrix.toEuclideanLin V
            (Matrix.toEuclideanLin
              (Matrix.diagonal (fun i ↦ (s i)⁻¹))
              (Matrix.toEuclideanLin Uᵀ η)) := by
              congr 1
              rw [toEuclideanLin_mul_apply]
  calc
    Matrix.toEuclideanLin (V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ) d
        =
      Matrix.toEuclideanLin (V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ)
        (Matrix.toEuclideanLin K fTrue + η) := by
          rw [h_data]
    _ =
      Matrix.toEuclideanLin
          (V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ)
          (Matrix.toEuclideanLin K fTrue) +
        Matrix.toEuclideanLin (V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ) η := by
          simp
    _ = fTrue + Matrix.toEuclideanLin (V * Matrix.diagonal (fun i ↦ (s i)⁻¹) * Uᵀ) η := by
          rw [hSignal]
    _ =
      fTrue +
        Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin
            (Matrix.diagonal (fun i ↦ (s i)⁻¹))
            (Matrix.toEuclideanLin Uᵀ η)) := by
              rw [hNoise]
