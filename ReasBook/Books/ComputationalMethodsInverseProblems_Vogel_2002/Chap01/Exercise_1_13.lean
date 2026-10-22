/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Definition_1_3.Tikhonov
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2_2.Reconstruction
import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_12
import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2_2

public section

noncomputable section

open scoped Matrix

namespace VariationalRegularization

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Helper for Exercise 1.13: moving a matrix action from the right input of the
Euclidean dot product to the left input replaces the matrix by its transpose. -/
lemma dotProduct_map_right_eq_transpose_map_left
    (A : Matrix n n ℝ) (x y : EuclideanSpace ℝ n) :
    dotProduct x (A.toEuclideanLin y) = dotProduct ((Aᵀ).toEuclideanLin x) y := by
  -- Rewrite the dot product as the real inner product so the transpose comes
  -- from the adjoint identity for `Matrix.toEuclideanLin`.
  have hAdj : LinearMap.adjoint A.toEuclideanLin = (Aᵀ).toEuclideanLin := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
  have hInner :
      inner ℝ x (A.toEuclideanLin y) = inner ℝ ((Aᵀ).toEuclideanLin x) y := by
    calc
      inner ℝ x (A.toEuclideanLin y) = inner ℝ (A.toEuclideanLin y) x := by
        rw [real_inner_comm]
      _ = inner ℝ y (LinearMap.adjoint A.toEuclideanLin x) := by
            simpa using
              (LinearMap.adjoint_inner_right (A := A.toEuclideanLin) (x := y) (y := x)).symm
      _ = inner ℝ y ((Aᵀ).toEuclideanLin x) := by
            rw [hAdj]
      _ = inner ℝ ((Aᵀ).toEuclideanLin x) y := by
            rw [real_inner_comm]
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using hInner

/-- Helper for Exercise 1.13: under an orthogonal SVD, the shifted Gramian
`Kᵀ * K + α I` stays diagonal in the right-singular basis `V`. -/
lemma sourceShiftedGramian_eq_orthogonalDiagonal
    (K U V : Matrix n n ℝ) (s : n → ℝ) (α : ℝ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    Kᵀ * K + α • (1 : Matrix n n ℝ) =
      V * Matrix.diagonal (fun i ↦ s i ^ 2 + α) * Vᵀ := by
  have hGram : Kᵀ * K = V * Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ := by
    have hUtU : Uᵀ * U = 1 :=
      (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ) (A := U)).1 hU
    -- Expand the Gramian once and collapse the orthogonal middle factor.
    calc
      Kᵀ * K = ((U * Matrix.diagonal s * Vᵀ)ᵀ) * (U * Matrix.diagonal s * Vᵀ) := by
        rw [hK]
      _ = (V * Matrix.diagonal s * Uᵀ) * (U * Matrix.diagonal s * Vᵀ) := by
            simp [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
      _ = V * (Matrix.diagonal s * (Uᵀ * U) * Matrix.diagonal s) * Vᵀ := by
            simp [Matrix.mul_assoc]
      _ = V * (Matrix.diagonal s * Matrix.diagonal s) * Vᵀ := by
            rw [hUtU]
            simp [Matrix.mul_assoc]
      _ = V * Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ := by
            rw [Matrix.diagonal_mul_diagonal]
            congr 2
            ext i
            ring
  have hVVt : V * Vᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ) (A := V)).1 hV
  have hDiagConst : Matrix.diagonal (fun _ : n ↦ α) = α • (1 : Matrix n n ℝ) := by
    -- The scalar shift is the diagonal matrix with constant diagonal entries `α`.
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hDiagAdd :
      Matrix.diagonal (fun i ↦ s i ^ 2) + Matrix.diagonal (fun _ : n ↦ α) =
        Matrix.diagonal (fun i ↦ s i ^ 2 + α) := by
    -- Adding the two diagonal matrices just adds the diagonal entries.
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hScalar :
      α • (1 : Matrix n n ℝ) = V * Matrix.diagonal (fun _ : n ↦ α) * Vᵀ := by
    -- Re-express the scalar identity matrix in the same `V` basis as the Gramian.
    calc
      α • (1 : Matrix n n ℝ) = α • (V * Vᵀ) := by
        rw [hVVt]
      _ = V * (α • (1 : Matrix n n ℝ)) * Vᵀ := by
            simp
      _ = V * Matrix.diagonal (fun _ : n ↦ α) * Vᵀ := by
            rw [← hDiagConst]
  calc
    Kᵀ * K + α • (1 : Matrix n n ℝ) =
        V * Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ +
          V * Matrix.diagonal (fun _ : n ↦ α) * Vᵀ := by
            rw [hGram, hScalar]
    _ = V *
          (Matrix.diagonal (fun i ↦ s i ^ 2) + Matrix.diagonal (fun _ : n ↦ α)) *
          Vᵀ := by
            calc
              V * Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ +
                  V * Matrix.diagonal (fun _ : n ↦ α) * Vᵀ =
                  (V * Matrix.diagonal (fun i ↦ s i ^ 2)) * Vᵀ +
                    (V * Matrix.diagonal (fun _ : n ↦ α)) * Vᵀ := by
                      simp [Matrix.mul_assoc]
              _ =
                  (V *
                    (Matrix.diagonal (fun i ↦ s i ^ 2) +
                      Matrix.diagonal (fun _ : n ↦ α))) * Vᵀ := by
                        rw [← Matrix.add_mul, ← Matrix.mul_add]
              _ = V *
                    (Matrix.diagonal (fun i ↦ s i ^ 2) +
                      Matrix.diagonal (fun _ : n ↦ α)) *
                    Vᵀ := by
                        simp [Matrix.mul_assoc]
    _ = V * Matrix.diagonal (fun i ↦ s i ^ 2 + α) * Vᵀ := by
          exact congrArg (fun M ↦ V * M * Vᵀ) hDiagAdd

/-- Quadratic-form expansion used in Exercise 1.13: the Tikhonov objective is
`fᵀ (Kᵀ * K + α • 1) f - 2 fᵀ Kᵀ d + ‖d‖ ^ 2`. -/
theorem tikhonovObjective_eq_quadraticForm
    (K : Matrix n n ℝ) (d : EuclideanSpace ℝ n) (α : ℝ) (f : EuclideanSpace ℝ n) :
    tikhonovObjective K d α f =
      dotProduct f (((Kᵀ * K + α • (1 : Matrix n n ℝ))).toEuclideanLin f) -
        2 * dotProduct f ((Kᵀ).toEuclideanLin d) + ‖d‖ ^ 2 := by
  -- Rewrite the quadratic and mixed residual terms through the adjoint of `K`.
  have hKAdj : LinearMap.adjoint K.toEuclideanLin = (Kᵀ).toEuclideanLin := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint K).symm
  have hCross :
      inner ℝ (K.toEuclideanLin f) d = inner ℝ ((Kᵀ).toEuclideanLin d) f := by
    calc
      inner ℝ (K.toEuclideanLin f) d =
          inner ℝ f (LinearMap.adjoint K.toEuclideanLin d) := by
            simpa using
              (LinearMap.adjoint_inner_right (A := K.toEuclideanLin) (x := f) (y := d)).symm
      _ = inner ℝ f ((Kᵀ).toEuclideanLin d) := by
            rw [hKAdj]
      _ = inner ℝ ((Kᵀ).toEuclideanLin d) f := by
            rw [real_inner_comm]
  have hQuadratic :
      inner ℝ (K.toEuclideanLin f) (K.toEuclideanLin f) =
        inner ℝ (((Kᵀ * K).toEuclideanLin f)) f := by
    calc
      inner ℝ (K.toEuclideanLin f) (K.toEuclideanLin f) =
          inner ℝ f (LinearMap.adjoint K.toEuclideanLin (K.toEuclideanLin f)) := by
            simpa using
              (LinearMap.adjoint_inner_right
                (A := K.toEuclideanLin) (x := f) (y := K.toEuclideanLin f)).symm
      _ = inner ℝ f ((Kᵀ).toEuclideanLin (K.toEuclideanLin f)) := by
            rw [hKAdj]
      _ = inner ℝ f (((Kᵀ * K).toEuclideanLin f)) := by
            rw [toEuclideanLin_mul_apply]
      _ = inner ℝ (((Kᵀ * K).toEuclideanLin f)) f := by
            rw [real_inner_comm]
  have hMatrixPart :
      inner ℝ (((Kᵀ * K).toEuclideanLin f)) f + α * inner ℝ f f =
        inner ℝ (((Kᵀ * K + α • (1 : Matrix n n ℝ)).toEuclideanLin f)) f := by
    -- Combine the Gramian term and the scalar Tikhonov penalty into one matrix action.
    have hAddApply :
        ((Kᵀ * K + α • (1 : Matrix n n ℝ)).toEuclideanLin f) =
          ((Kᵀ * K).toEuclideanLin f + α • f) := by
      simp [Matrix.toLpLin_apply]
    calc
      inner ℝ (((Kᵀ * K).toEuclideanLin f)) f + α * inner ℝ f f =
          inner ℝ (((Kᵀ * K).toEuclideanLin f)) f + inner ℝ (α • f) f := by
            rw [real_inner_smul_left]
      _ = inner ℝ (((Kᵀ * K).toEuclideanLin f) + α • f) f := by
            rw [inner_add_left]
      _ = inner ℝ (((Kᵀ * K + α • (1 : Matrix n n ℝ)).toEuclideanLin f)) f := by
            rw [← hAddApply]
  have hInnerForm :
      tikhonovObjective K d α f =
        inner ℝ (((Kᵀ * K + α • (1 : Matrix n n ℝ)).toEuclideanLin f)) f -
          2 * inner ℝ ((Kᵀ).toEuclideanLin d) f + ‖d‖ ^ 2 := by
    -- Expand the residual norm and regroup the quadratic, mixed, and constant terms.
    rw [tikhonovObjective_def, norm_sub_sq_real, hCross]
    calc
      ‖K.toEuclideanLin f‖ ^ 2 - 2 * inner ℝ ((Kᵀ).toEuclideanLin d) f + ‖d‖ ^ 2 +
            α * ‖f‖ ^ 2 =
          inner ℝ (((Kᵀ * K).toEuclideanLin f)) f +
            α * inner ℝ f f -
              2 * inner ℝ ((Kᵀ).toEuclideanLin d) f + ‖d‖ ^ 2 := by
                rw [← real_inner_self_eq_norm_sq (K.toEuclideanLin f), hQuadratic,
                  ← real_inner_self_eq_norm_sq f]
                ring
      _ =
          inner ℝ (((Kᵀ * K + α • (1 : Matrix n n ℝ)).toEuclideanLin f)) f -
            2 * inner ℝ ((Kᵀ).toEuclideanLin d) f + ‖d‖ ^ 2 := by
              rw [hMatrixPart]
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using hInnerForm

/-- Exercise 1.13. Under an orthogonal SVD `K = U * Matrix.diagonal s * Vᵀ`,
the Tikhonov objective admits the singular-value-coordinate expansion in
`(Vᵀ).toEuclideanLin f` and `(Uᵀ).toEuclideanLin d`. -/
theorem tikhonovObjective_eq_svdCoordinates
    (K U V : Matrix n n ℝ) (s : n → ℝ) (d : EuclideanSpace ℝ n) (α : ℝ)
    (f : EuclideanSpace ℝ n)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    tikhonovObjective K d α f =
      dotProduct ((Vᵀ).toEuclideanLin f)
          ((Matrix.diagonal (fun i ↦ s i ^ 2 + α)).toEuclideanLin ((Vᵀ).toEuclideanLin f)) -
        2 * dotProduct ((Vᵀ).toEuclideanLin f)
          ((Matrix.diagonal s).toEuclideanLin ((Uᵀ).toEuclideanLin d)) +
        ‖d‖ ^ 2 := by
  let diagShift : n → ℝ := fun i ↦ s i ^ 2 + α
  have hQuadratic :
      dotProduct f (((Kᵀ * K + α • (1 : Matrix n n ℝ)).toEuclideanLin f)) =
        dotProduct ((Vᵀ).toEuclideanLin f)
          ((Matrix.diagonal diagShift).toEuclideanLin ((Vᵀ).toEuclideanLin f)) := by
    -- Rewrite the shifted Gramian in the `V` basis and then move the outer `V`
    -- across the dot product by transpose.
    rw [sourceShiftedGramian_eq_orthogonalDiagonal K U V s α hU hV hK]
    have hMap :
        ((V * Matrix.diagonal diagShift * Vᵀ).toEuclideanLin f) =
          V.toEuclideanLin
            ((Matrix.diagonal diagShift).toEuclideanLin ((Vᵀ).toEuclideanLin f)) := by
      calc
        ((V * Matrix.diagonal diagShift * Vᵀ).toEuclideanLin f) =
            ((V * (Matrix.diagonal diagShift * Vᵀ)).toEuclideanLin f) := by
              rw [Matrix.mul_assoc]
        _ = V.toEuclideanLin ((Matrix.diagonal diagShift * Vᵀ).toEuclideanLin f) := by
              exact (toEuclideanLin_mul_apply V (Matrix.diagonal diagShift * Vᵀ) f).symm
        _ = V.toEuclideanLin
              ((Matrix.diagonal diagShift).toEuclideanLin ((Vᵀ).toEuclideanLin f)) := by
              congr 1
              calc
                ((Matrix.diagonal diagShift * Vᵀ).toEuclideanLin f) =
                    (((Matrix.diagonal diagShift) * Vᵀ).toEuclideanLin f) := by
                      rfl
                _ =
                    (Matrix.diagonal diagShift).toEuclideanLin ((Vᵀ).toEuclideanLin f) := by
                      exact
                        (toEuclideanLin_mul_apply (Matrix.diagonal diagShift) Vᵀ f).symm
    rw [hMap]
    simpa using
      dotProduct_map_right_eq_transpose_map_left V f
        ((Matrix.diagonal diagShift).toEuclideanLin ((Vᵀ).toEuclideanLin f))
  have hKt : Kᵀ = V * Matrix.diagonal s * Uᵀ := by
    -- Transpose the SVD identity once so the cross term has the same `V`-outer shape.
    rw [hK]
    simp [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hCross :
      dotProduct f ((Kᵀ).toEuclideanLin d) =
        dotProduct ((Vᵀ).toEuclideanLin f)
          ((Matrix.diagonal s).toEuclideanLin ((Uᵀ).toEuclideanLin d)) := by
    rw [hKt]
    have hMap :
        ((V * Matrix.diagonal s * Uᵀ).toEuclideanLin d) =
          V.toEuclideanLin
            ((Matrix.diagonal s).toEuclideanLin ((Uᵀ).toEuclideanLin d)) := by
      calc
        ((V * Matrix.diagonal s * Uᵀ).toEuclideanLin d) =
            ((V * (Matrix.diagonal s * Uᵀ)).toEuclideanLin d) := by
              rw [Matrix.mul_assoc]
        _ = V.toEuclideanLin ((Matrix.diagonal s * Uᵀ).toEuclideanLin d) := by
              exact (toEuclideanLin_mul_apply V (Matrix.diagonal s * Uᵀ) d).symm
        _ = V.toEuclideanLin ((Matrix.diagonal s).toEuclideanLin ((Uᵀ).toEuclideanLin d)) := by
              congr 1
              calc
                ((Matrix.diagonal s * Uᵀ).toEuclideanLin d) =
                    (((Matrix.diagonal s) * Uᵀ).toEuclideanLin d) := by
                      rfl
                _ = (Matrix.diagonal s).toEuclideanLin ((Uᵀ).toEuclideanLin d) := by
                      exact (toEuclideanLin_mul_apply (Matrix.diagonal s) Uᵀ d).symm
    rw [hMap]
    simpa using
      dotProduct_map_right_eq_transpose_map_left V f
        ((Matrix.diagonal s).toEuclideanLin ((Uᵀ).toEuclideanLin d))
  -- Reuse the quadratic-form expansion and substitute the two SVD-coordinate rewrites.
  rw [tikhonovObjective_eq_quadraticForm, hQuadratic, hCross]

end VariationalRegularization

namespace Tikhonov

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Under the Exercise 1.12 square-SVD hypotheses and `0 < α`,
`Tikhonov.reconstruction` agrees with the explicit Tikhonov filter
representation. -/
theorem reconstruction_eq_filterRepresentation
    (K U V : Matrix n n ℝ) (s : n → ℝ) (α : ℝ) (d : EuclideanSpace ℝ n)
    (hα_pos : 0 < α)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    reconstruction K α d =
      Matrix.toEuclideanLin
        (V * Matrix.diagonal (fun i ↦ s i / (s i ^ 2 + α)) * Uᵀ) d := by
  simpa [reconstruction_eq, operator_def] using
    operatorRepresentation_eq_filterRepresentation K U V s α d hα_pos hU hV hK

/-- Minimizer consequence used in Exercise 1.13: under an orthogonal SVD
`K = U * Matrix.diagonal s * Vᵀ` and `0 < α`, the explicit Tikhonov filter
vector is a variational Tikhonov minimizer. -/
theorem filterRepresentation_isTikhonovMinimizer
    (K U V : Matrix n n ℝ) (s : n → ℝ) (d : EuclideanSpace ℝ n) (α : ℝ)
    (hα_pos : 0 < α)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    VariationalRegularization.IsTikhonovMinimizer K d α
      (Matrix.toEuclideanLin
        (V * Matrix.diagonal (fun i ↦ s i / (s i ^ 2 + α)) * Uᵀ) d) := by
  rw [← reconstruction_eq_filterRepresentation K U V s α d hα_pos hU hV hK]
  exact tikhonov_reconstruction_isTikhonovMinimizer K d α hα_pos

end Tikhonov
