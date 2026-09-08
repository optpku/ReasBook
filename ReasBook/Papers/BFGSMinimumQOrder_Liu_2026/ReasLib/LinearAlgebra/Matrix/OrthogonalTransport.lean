module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

noncomputable section

open scoped Matrix

namespace Matrix

/-- An orthogonal matrix preserves the real coordinate dot product under
matrix-vector multiplication. -/
theorem dotProduct_mulVec_eq_of_mem_orthogonalGroup
    {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℝ) (hR : R ∈ Matrix.orthogonalGroup n ℝ)
    (u v : n → ℝ) :
    (R *ᵥ u) ⬝ᵥ (R *ᵥ v) = u ⬝ᵥ v := by
  have hcancel : R.transpose * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hR
  calc
    (R *ᵥ u) ⬝ᵥ (R *ᵥ v) = (u ᵥ* R.transpose) ⬝ᵥ (R *ᵥ v) := by
      rw [Matrix.vecMul_transpose]
    _ = u ⬝ᵥ (R.transpose *ᵥ (R *ᵥ v)) :=
      (Matrix.dotProduct_mulVec u R.transpose (R *ᵥ v)).symm
    _ = u ⬝ᵥ v := by
      rw [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]

/-- An orthogonal matrix preserves the Euclidean norm under matrix-vector
multiplication. -/
theorem norm_toLp_mulVec_eq_of_mem_orthogonalGroup
    {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℝ) (hR : R ∈ Matrix.orthogonalGroup n ℝ)
    (v : n → ℝ) :
    ‖WithLp.toLp 2 (R *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
  have hsquare : ‖WithLp.toLp 2 (R *ᵥ v)‖ ^ 2 =
      ‖WithLp.toLp 2 v‖ ^ 2 := by
    have hleft := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (R *ᵥ v))
    have hright := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 v)
    rw [hleft, hright]
    simpa only [dotProduct, pow_two] using
      dotProduct_mulVec_eq_of_mem_orthogonalGroup R hR v v
  nlinarith [norm_nonneg (WithLp.toLp 2 (R *ᵥ v)),
    norm_nonneg (WithLp.toLp 2 v)]

/-- A special orthogonal matrix preserves the real coordinate dot product. -/
theorem dotProduct_mulVec_eq_of_mem_specialOrthogonalGroup
    {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℝ) (hR : R ∈ Matrix.specialOrthogonalGroup n ℝ)
    (u v : n → ℝ) :
    (R *ᵥ u) ⬝ᵥ (R *ᵥ v) = u ⬝ᵥ v := by
  exact dotProduct_mulVec_eq_of_mem_orthogonalGroup R
    (Matrix.mem_specialOrthogonalGroup_iff.mp hR).1 u v

/-- A special orthogonal matrix preserves the Euclidean norm. -/
theorem norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℝ) (hR : R ∈ Matrix.specialOrthogonalGroup n ℝ)
    (v : n → ℝ) :
    ‖WithLp.toLp 2 (R *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
  exact norm_toLp_mulVec_eq_of_mem_orthogonalGroup R
    (Matrix.mem_specialOrthogonalGroup_iff.mp hR).1 v

/-- Conjugating a matrix and transporting a vector by the same orthogonal
matrix commutes with matrix-vector multiplication. -/
theorem conjugate_mulVec_of_mem_orthogonalGroup
    {n : Type*} [Fintype n] [DecidableEq n]
    (R H : Matrix n n ℝ) (hR : R ∈ Matrix.orthogonalGroup n ℝ)
    (v : n → ℝ) :
    (R * H * R.transpose) *ᵥ (R *ᵥ v) = R *ᵥ (H *ᵥ v) := by
  have hcancel : R.transpose * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hR
  calc
    (R * H * R.transpose) *ᵥ (R *ᵥ v) =
        (R * H) *ᵥ (R.transpose *ᵥ (R *ᵥ v)) :=
      (Matrix.mulVec_mulVec (R *ᵥ v) (R * H) R.transpose).symm
    _ = (R * H) *ᵥ ((R.transpose * R) *ᵥ v) := by
      exact congrArg ((R * H).mulVec) (Matrix.mulVec_mulVec v R.transpose R)
    _ = (R * H) *ᵥ v := by
      rw [hcancel, Matrix.one_mulVec]
    _ = R *ᵥ (H *ᵥ v) := (Matrix.mulVec_mulVec v R H).symm

/-- Conjugation transports a self outer product to the self outer product of
the transported vector. -/
theorem conjugate_vecMulVec
    {n : Type*} [Fintype n]
    (R : Matrix n n ℝ) (u : n → ℝ) :
    R * Matrix.vecMulVec u u * R.transpose =
      Matrix.vecMulVec (R *ᵥ u) (R *ᵥ u) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

end Matrix
