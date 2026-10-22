/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_15.Iteration
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_16.Landweber
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

noncomputable section

open scoped BigOperators Matrix

namespace Landweber

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Helper for Exercise 1.15: applying two matrix-induced maps composes by
matrix multiplication. -/
lemma toEuclideanLin_mul_apply
    (A B : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    A.toEuclideanLin (B.toEuclideanLin x) = (A * B).toEuclideanLin x := by
  -- Compare both sides after unfolding `EuclideanSpace` to the underlying `mulVec` action.
  ext i
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- Helper for Exercise 1.15: the sum of two matrix-induced applications is the
application of the summed matrix. -/
lemma toEuclideanLin_add_apply
    (A B : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    A.toEuclideanLin x + B.toEuclideanLin x = (A + B).toEuclideanLin x := by
  -- Unfold both actions to `mulVec`, where additivity is entrywise.
  ext i
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Helper for Exercise 1.15: under an SVD `K = U * diagonal s * Vᵀ`, the scaled
transpose `τ • Kᵀ` becomes the corresponding diagonal spectral factor. -/
lemma scaledTranspose_eq_svdDiagonal
    (K U V : Matrix n n ℝ) (s : n → ℝ) (τ : ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    τ • Kᵀ = V * Matrix.diagonal (fun i ↦ τ * s i) * Uᵀ := by
  have hdiag : τ • Matrix.diagonal s = Matrix.diagonal (fun i ↦ τ * s i) := by
    -- Scalar multiplication of a diagonal matrix acts entrywise on the diagonal function.
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  -- Rewrite the transpose in SVD coordinates and push the scalar into the diagonal matrix.
  calc
    τ • Kᵀ = τ • (V * Matrix.diagonal s * Uᵀ) := by
      rw [hK]
      simp [Matrix.mul_assoc, Matrix.diagonal_transpose]
    _ = (τ • (V * Matrix.diagonal s)) * Uᵀ := by
      rw [← Matrix.smul_mul]
    _ = (V * (τ • Matrix.diagonal s)) * Uᵀ := by
      rw [← Matrix.mul_smul]
    _ = V * Matrix.diagonal (fun i ↦ τ * s i) * Uᵀ := by
      rw [hdiag]

/-- Helper for Exercise 1.15: the Landweber iteration matrix `I - τ Kᵀ K`
diagonalizes in the right singular-vector basis. -/
lemma iterationMatrix_eq_svdDiagonal
    (K U V : Matrix n n ℝ) (s : n → ℝ) (τ : ℝ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    iterationMatrix K τ = V * Matrix.diagonal (fun i ↦ 1 - τ * s i ^ 2) * Vᵀ := by
  have hU' : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hU
  have hV' : V * Vᵀ = 1 := (Matrix.mem_orthogonalGroup_iff n ℝ).mp hV
  have hKK :
      Kᵀ * K = V * Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ := by
    -- Compute `Kᵀ K` by cancelling the orthogonal middle factor `Uᵀ * U`.
    calc
      Kᵀ * K = (V * Matrix.diagonal s * Uᵀ) * (U * Matrix.diagonal s * Vᵀ) := by
        rw [hK]
        simp [Matrix.mul_assoc, Matrix.diagonal_transpose]
      _ = V * (Matrix.diagonal s * (Uᵀ * U) * Matrix.diagonal s) * Vᵀ := by
        simp [Matrix.mul_assoc]
      _ = V * (Matrix.diagonal s * Matrix.diagonal s) * Vᵀ := by
        rw [hU']
        simp [Matrix.mul_assoc]
      _ = V * Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ := by
        simp [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, pow_two]
  -- Rewrite `I` as `V * I * Vᵀ` so the whole expression stays in one spectral basis.
  calc
    iterationMatrix K τ = V * Vᵀ - τ • (V * Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ) := by
      rw [iterationMatrix_def, hKK, ← hV']
    _ = V * ((1 : Matrix n n ℝ) - τ • Matrix.diagonal (fun i ↦ s i ^ 2)) * Vᵀ := by
      simp [Matrix.mul_assoc, sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul]
    _ = V * Matrix.diagonal (fun i ↦ 1 - τ * s i ^ 2) * Vᵀ := by
      have hdiag :
          (1 : Matrix n n ℝ) - τ • Matrix.diagonal (fun i ↦ s i ^ 2) =
            Matrix.diagonal (fun i ↦ 1 - τ * s i ^ 2) := by
        -- The diagonal entries become `1 - τ * s i ^ 2`, and all off-diagonal entries vanish.
        ext i j
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij]
      rw [hdiag]

/-- Helper for Exercise 1.15: the diagonal spectral Landweber coefficients satisfy
the same one-step matrix recursion as the iterates. -/
lemma svdFilterMatrix_succ
    (U V : Matrix n n ℝ) (s c : n → ℝ) (τ : ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ) :
    (V * Matrix.diagonal (fun i ↦ 1 - τ * s i ^ 2) * Vᵀ) *
        (V * Matrix.diagonal c * Uᵀ) +
      V * Matrix.diagonal (fun i ↦ τ * s i) * Uᵀ =
        V * Matrix.diagonal (fun i ↦ (1 - τ * s i ^ 2) * c i + τ * s i) * Uᵀ := by
  have hV' : Vᵀ * V = 1 := (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hV
  -- Cancel the orthogonal middle factor and then combine the two diagonal contributions.
  calc
    (V * Matrix.diagonal (fun i ↦ 1 - τ * s i ^ 2) * Vᵀ) *
        (V * Matrix.diagonal c * Uᵀ) +
      V * Matrix.diagonal (fun i ↦ τ * s i) * Uᵀ =
        V * (Matrix.diagonal (fun i ↦ 1 - τ * s i ^ 2) * (Vᵀ * V) * Matrix.diagonal c) * Uᵀ +
          V * Matrix.diagonal (fun i ↦ τ * s i) * Uᵀ := by
      simp [Matrix.mul_assoc]
    _ = V * (Matrix.diagonal (fun i ↦ 1 - τ * s i ^ 2) * Matrix.diagonal c) * Uᵀ +
          V * Matrix.diagonal (fun i ↦ τ * s i) * Uᵀ := by
      rw [hV']
      simp [Matrix.mul_assoc]
    _ = V * ((Matrix.diagonal (fun i ↦ 1 - τ * s i ^ 2) * Matrix.diagonal c) * Uᵀ) +
          V * (Matrix.diagonal (fun i ↦ τ * s i) * Uᵀ) := by
      simp [Matrix.mul_assoc]
    _ = V * (((Matrix.diagonal (fun i ↦ 1 - τ * s i ^ 2) * Matrix.diagonal c) * Uᵀ) +
          (Matrix.diagonal (fun i ↦ τ * s i) * Uᵀ)) := by
      rw [← Matrix.mul_add]
    _ = V * ((Matrix.diagonal (fun i ↦ 1 - τ * s i ^ 2) * Matrix.diagonal c +
          Matrix.diagonal (fun i ↦ τ * s i)) * Uᵀ) := by
      rw [← Matrix.add_mul]
    _ = V * Matrix.diagonal (fun i ↦ (1 - τ * s i ^ 2) * c i + τ * s i) * Uᵀ := by
      simp [Matrix.mul_assoc, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal]

/-- Helper for Exercise 1.15: the scalar filter coefficient
`SpectralFilter.landweber τ v (a ^ 2) / a` satisfies the Landweber recursion. -/
lemma landweberCoeff_succ
    (τ a : ℝ) (v : ℕ) :
    (1 - τ * a ^ 2) * (SpectralFilter.landweber τ v (a ^ 2) / a) + τ * a =
      SpectralFilter.landweber τ (v + 1) (a ^ 2) / a := by
  by_cases ha : a = 0
  · -- The zero singular-value branch collapses to `0 = 0`.
    simp [ha, SpectralFilter.landweber_eq]
  · -- Away from zero, multiply through by `a` and use the closed form of `landweber`.
    rw [SpectralFilter.landweber_eq, SpectralFilter.landweber_eq]
    field_simp [ha]
    rw [pow_succ]
    ring

/-- Preliminary identity for Exercise 1.15: the zero-start Landweber iterate equals
`Finset.sum (Finset.range v) (fun j ↦ (G ^ j).toEuclideanLin b)` with
`G = Landweber.iterationMatrix K τ` and `b = (τ • Kᵀ).toEuclideanLin d`. -/
theorem iterate_eq_sum_powers
    (K : Matrix n n ℝ) (τ : ℝ) (d : EuclideanSpace ℝ n) (v : ℕ) :
    iterate K τ d v =
      Finset.sum (Finset.range v) fun j ↦
        ((iterationMatrix K τ) ^ j).toEuclideanLin ((τ • Kᵀ).toEuclideanLin d) := by
  induction v with
  | zero =>
      -- The zero-start iterate and the empty geometric sum are both `0`.
      rw [iterate_zero]
      simp
  | succ v ih =>
      -- Apply the recursion once, then push `iterationMatrix K τ` through the finite sum.
      rw [iterate_succ, ih]
      have hmap :
          (iterationMatrix K τ).toEuclideanLin
              (Finset.sum (Finset.range v) fun j ↦
                ((iterationMatrix K τ) ^ j).toEuclideanLin ((τ • Kᵀ).toEuclideanLin d)) =
          Finset.sum (Finset.range v) fun j ↦
            (iterationMatrix K τ).toEuclideanLin
              (((iterationMatrix K τ) ^ j).toEuclideanLin ((τ • Kᵀ).toEuclideanLin d)) := by
        rw [map_sum]
      rw [hmap]
      calc
        Finset.sum (Finset.range v) (fun j ↦
            (iterationMatrix K τ).toEuclideanLin
              (((iterationMatrix K τ) ^ j).toEuclideanLin ((τ • Kᵀ).toEuclideanLin d))) +
            (τ • Kᵀ).toEuclideanLin d =
          Finset.sum (Finset.range v) (fun j ↦
              ((iterationMatrix K τ) ^ (j + 1)).toEuclideanLin
                ((τ • Kᵀ).toEuclideanLin d)) +
            ((iterationMatrix K τ) ^ 0).toEuclideanLin ((τ • Kᵀ).toEuclideanLin d) := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro j hj
            rw [toEuclideanLin_mul_apply, pow_succ']
          · simp
        _ = Finset.sum (Finset.range (v + 1)) (fun j ↦
            ((iterationMatrix K τ) ^ j).toEuclideanLin ((τ • Kᵀ).toEuclideanLin d)) := by
          simpa using
            (Finset.sum_range_succ'
              (fun j ↦ ((iterationMatrix K τ) ^ j).toEuclideanLin ((τ • Kᵀ).toEuclideanLin d))
              v).symm

/-- Exercise 1.15. Under an orthogonal SVD `K = U * Matrix.diagonal s * Vᵀ`,
the Landweber iterate yields the representation `(1.10)` with filter function
`(1.38)`, realized by `SpectralFilter.landweber`. -/
theorem iterate_eq_filterRepresentation
    (K U V : Matrix n n ℝ) (s : n → ℝ) (τ : ℝ) (d : EuclideanSpace ℝ n) (v : ℕ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    iterate K τ d v =
      (V * Matrix.diagonal
        (fun i ↦ SpectralFilter.landweber τ v (s i ^ 2) / s i) * Uᵀ).toEuclideanLin d := by
  induction v with
  | zero =>
      -- The zero-step iterate and the zero filter both vanish.
      rw [iterate_zero]
      simp [SpectralFilter.landweber_eq]
  | succ v ih =>
      -- Route correction: instead of expanding matrix powers, match the iterate recursion
      -- directly against the diagonal filter recursion in SVD coordinates.
      rw [iterate_succ, ih, iterationMatrix_eq_svdDiagonal K U V s τ hU hV hK,
        scaledTranspose_eq_svdDiagonal K U V s τ hK, toEuclideanLin_mul_apply,
        toEuclideanLin_add_apply]
      rw [svdFilterMatrix_succ U V s
        (fun i ↦ SpectralFilter.landweber τ v (s i ^ 2) / s i) τ hV]
      have hdiag :
          Matrix.diagonal
              (fun i ↦
                (1 - τ * s i ^ 2) * (SpectralFilter.landweber τ v (s i ^ 2) / s i) + τ * s i) =
            Matrix.diagonal
              (fun i ↦ SpectralFilter.landweber τ (v + 1) (s i ^ 2) / s i) := by
        -- The diagonal entries evolve by the scalar Landweber recursion.
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [landweberCoeff_succ]
        · simp [hij]
      rw [hdiag]

end Landweber
