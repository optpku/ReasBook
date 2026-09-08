module

public import ReasLib.Optimization.DFP.InverseUpdate
public import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport

/-!
# Orthogonal transport of the inverse DFP update

The inverse-form DFP update is equivariant under a simultaneous orthogonal
change of coordinates of the metric and secant pair.
-/

public section

open scoped Matrix

namespace Matrix

/-- For a Hermitian base matrix, the inverse-form DFP update commutes with an
orthogonal change of coordinates. -/
theorem inverseDFPUpdate_conjugate_of_mem_orthogonalGroup
    {n : Type*} [Fintype n] [DecidableEq n]
    (R H : Matrix n n ℝ) (s y : n → ℝ)
    (hR : R ∈ Matrix.orthogonalGroup n ℝ) (hH : H.IsHermitian) :
    R * Matrix.inverseDFPUpdate H s y * R.transpose =
      Matrix.inverseDFPUpdate (R * H * R.transpose) (R *ᵥ s) (R *ᵥ y) := by
  have hHT : H.transpose = H := by
    simpa [Matrix.IsHermitian] using hH.eq
  have hphysicalT : (R * H * R.transpose).transpose =
      R * H * R.transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hHT]
    simp only [Matrix.mul_assoc]
  have hHy := Matrix.conjugate_mulVec_of_mem_orthogonalGroup R H hR y
  have hquadratic := Matrix.dotProduct_mulVec_eq_of_mem_orthogonalGroup
    R hR y (H *ᵥ y)
  have hsecant := Matrix.dotProduct_mulVec_eq_of_mem_orthogonalGroup R hR s y
  have houterHy := Matrix.conjugate_vecMulVec R (H *ᵥ y)
  have houters := Matrix.conjugate_vecMulVec R s
  have houterHy' :
      R * (Matrix.vecMulVec (H *ᵥ y) (H *ᵥ y) * R.transpose) =
        Matrix.vecMulVec (R *ᵥ (H *ᵥ y)) (R *ᵥ (H *ᵥ y)) := by
    rw [← Matrix.mul_assoc]
    exact houterHy
  have houters' : R * (Matrix.vecMulVec s s * R.transpose) =
      Matrix.vecMulVec (R *ᵥ s) (R *ᵥ s) := by
    rw [← Matrix.mul_assoc]
    exact houters
  have hyH : y ᵥ* H = H *ᵥ y := by
    calc
      y ᵥ* H = y ᵥ* H.transpose :=
        congrArg (fun M ↦ y ᵥ* M) hHT.symm
      _ = H *ᵥ y := Matrix.vecMul_transpose H y
  have hphysicalY : (R *ᵥ y) ᵥ* (R * H * R.transpose) =
      (R * H * R.transpose) *ᵥ (R *ᵥ y) := by
    calc
      (R *ᵥ y) ᵥ* (R * H * R.transpose) =
          (R *ᵥ y) ᵥ* (R * H * R.transpose).transpose :=
        congrArg (fun M ↦ (R *ᵥ y) ᵥ* M) hphysicalT.symm
      _ = (R * H * R.transpose) *ᵥ (R *ᵥ y) :=
        Matrix.vecMul_transpose (R * H * R.transpose) (R *ᵥ y)
  rw [Matrix.inverseDFPUpdate_def, Matrix.inverseDFPUpdate_def, hyH, hphysicalY,
    hHy, hquadratic, hsecant]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [houterHy', houters']

end Matrix
