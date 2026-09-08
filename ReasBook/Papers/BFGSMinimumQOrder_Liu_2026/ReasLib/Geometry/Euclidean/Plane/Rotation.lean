module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

noncomputable section

open scoped EuclideanSpace Matrix

namespace EuclideanPlane

/-- The orientation of the Euclidean plane determined by its standard orthonormal basis. -/
def orientation : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

/-- Counterclockwise right-angle rotation in standard Euclidean coordinates. -/
def perp : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  orientation.rightAngleRotation

/-- The coordinate matrix of counterclockwise rotation through `π / 2` in the Euclidean plane. -/
def quarterTurnMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; 1, 0]

/-- The standard orientation's volume form is the determinant in the standard orthonormal basis. -/
private lemma volumeForm_eq_standardBasisDet :
    orientation.volumeForm = (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.det := by
  -- The chosen orientation is definitionally the orientation of this basis.
  exact orientation.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) rfl

/-- The standard oriented area form is the usual coordinate determinant. -/
theorem standardAreaForm_apply (x y : EuclideanSpace ℝ (Fin 2)) :
    orientation.areaForm x y = x 0 * y 1 - x 1 * y 0 := by
  -- Pass through the volume form and evaluate its determinant in standard coordinates.
  simp only [Orientation.areaForm_to_volumeForm, volumeForm_eq_standardBasisDet,
    Module.Basis.det_apply, Matrix.det_fin_two, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The right-angle operator sends `(x₁, x₂)` to `(-x₂, x₁)`. -/
theorem perp_apply (x : EuclideanSpace ℝ (Fin 2)) :
    perp x = !₂[-x 1, x 0] := by
  -- Compare the two vectors coordinatewise against the standard orthonormal basis.
  ext i
  fin_cases i
  · -- The area determinant against the first basis vector gives the first coordinate.
    calc
      (perp x) 0 = inner ℝ (perp x) (EuclideanSpace.basisFun (Fin 2) ℝ 0) :=
        (EuclideanSpace.inner_basisFun_real (Fin 2) (perp x) 0).symm
      _ = orientation.areaForm x (EuclideanSpace.basisFun (Fin 2) ℝ 0) :=
        orientation.inner_rightAngleRotation_left x (EuclideanSpace.basisFun (Fin 2) ℝ 0)
      _ = -x 1 := by simp [standardAreaForm_apply]
  · -- The area determinant against the second basis vector gives the second coordinate.
    calc
      (perp x) 1 = inner ℝ (perp x) (EuclideanSpace.basisFun (Fin 2) ℝ 1) :=
        (EuclideanSpace.inner_basisFun_real (Fin 2) (perp x) 1).symm
      _ = orientation.areaForm x (EuclideanSpace.basisFun (Fin 2) ℝ 1) :=
        orientation.inner_rightAngleRotation_left x (EuclideanSpace.basisFun (Fin 2) ℝ 1)
      _ = x 0 := by simp [standardAreaForm_apply]

/-- The quarter-turn matrix acts as the positively oriented right-angle rotation. -/
theorem quarterTurnMatrix_toEuclideanLin (x : EuclideanSpace ℝ (Fin 2)) :
    Matrix.toEuclideanLin quarterTurnMatrix x = perp x := by
  -- Rewrite the geometric quarter-turn in coordinates, then evaluate each matrix row.
  rw [perp_apply]
  ext i
  fin_cases i
  · simp [Matrix.toLpLin_apply, quarterTurnMatrix, dotProduct, Fin.sum_univ_two]
  · simp [Matrix.toLpLin_apply, quarterTurnMatrix, dotProduct, Fin.sum_univ_two]

/-- Rotation of the standard Euclidean plane by an oriented angle. -/
def rotation (theta : Real.Angle) :
    EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  orientation.rotation theta

/-- Rotation in the standard Euclidean plane is the cosine-sine combination of a vector and
its positively oriented perpendicular. -/
theorem rotation_apply (theta : Real.Angle) (x : EuclideanSpace ℝ (Fin 2)) :
    rotation theta x = theta.cos • x + theta.sin • perp x := by
  rfl

/-- The standard-coordinate matrix of rotation by `theta`. -/
def rotationMatrix (theta : Real.Angle) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![theta.cos, -theta.sin; theta.sin, theta.cos]

/-- The matrix of the bundled rotation in the standard Euclidean basis is `rotationMatrix`. -/
theorem toMatrix_rotation (theta : Real.Angle) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (rotation theta).toLinearMap =
        rotationMatrix theta := by
  have hperpZero :
      orientation.rightAngleRotation
          (EuclideanSpace.single (0 : Fin 2) 1) =
        (!₂[(0 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) := by
    rw [← perp]
    simpa using perp_apply (EuclideanSpace.single (0 : Fin 2) 1)
  have hperpOne :
      orientation.rightAngleRotation
          (EuclideanSpace.single (1 : Fin 2) 1) =
        (!₂[-(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) := by
    rw [← perp]
    simpa using perp_apply (EuclideanSpace.single (1 : Fin 2) 1)
  -- Evaluate the rotation on each standard basis vector and read off its coordinates.
  ext i j
  fin_cases i
  · fin_cases j
    · simp [LinearMap.toMatrix_apply, rotation, Orientation.rotation_apply,
        rotationMatrix, hperpZero]
    · simp [LinearMap.toMatrix_apply, rotation, Orientation.rotation_apply,
        rotationMatrix, hperpOne]
  · fin_cases j
    · simp [LinearMap.toMatrix_apply, rotation, Orientation.rotation_apply,
        rotationMatrix, hperpZero]
    · simp [LinearMap.toMatrix_apply, rotation, Orientation.rotation_apply,
        rotationMatrix, hperpOne]

/-- Matrix-vector multiplication by `rotationMatrix` agrees with the bundled rotation. -/
theorem rotationMatrix_mulVec (theta : Real.Angle) (x : EuclideanSpace ℝ (Fin 2)) :
    rotationMatrix theta *ᵥ EuclideanSpace.equiv (Fin 2) ℝ x =
      EuclideanSpace.equiv (Fin 2) ℝ (rotation theta x) := by
  -- Matrix multiplication is the coordinate form of applying the represented linear map.
  rw [← toMatrix_rotation]
  exact LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (rotation theta).toLinearMap x

/-- The explicit rotation matrix has determinant one. -/
theorem det_rotationMatrix (theta : Real.Angle) :
    (rotationMatrix theta).det = 1 := by
  -- Determinants agree with those of the represented rotation.
  rw [← toMatrix_rotation, LinearMap.det_toMatrix]
  exact orientation.det_rotation theta

/-- The matrix whose columns are a vector and its positively oriented perpendicular. -/
def frame (e : EuclideanSpace ℝ (Fin 2)) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i ↦ ![e i, perp e i]

/-- Frame coordinates reconstruct the corresponding linear combination of `e` and `perp e`. -/
theorem frame_mulVec (e : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    frame e *ᵥ ![a, b] =
      EuclideanSpace.equiv (Fin 2) ℝ (a • e + b • perp e) := by
  -- Expand the two rows of the frame and the two coordinates of the vector sum.
  ext i
  fin_cases i
  · simp [frame, Matrix.mulVec, dotProduct, Fin.sum_univ_two, perp_apply]
    ring
  · simp [frame, Matrix.mulVec, dotProduct, Fin.sum_univ_two, perp_apply]
    ring

/-- The frame `(e, perp e)` is positively oriented orthonormal exactly when
`e` is a unit vector. -/
theorem frame_mem_specialOrthogonalGroup_iff (e : EuclideanSpace ℝ (Fin 2)) :
    frame e ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ ↔ ‖e‖ = 1 := by
  have hnorm := EuclideanSpace.real_norm_sq_eq e
  rw [Fin.sum_univ_two] at hnorm
  have hcoord : e 0 ^ 2 + e 1 ^ 2 = 1 ↔ ‖e‖ = 1 := by
    constructor
    · intro h
      nlinarith [norm_nonneg e]
    · intro h
      rw [h] at hnorm
      nlinarith
  -- The two-dimensional criterion reduces membership to the squared coordinate norm.
  rw [Matrix.mem_specialOrthogonalGroup_fin_two_iff]
  simpa [frame, perp_apply] using hcoord

/-- A unit frame is the rotation matrix of the oriented angle from the first
standard basis vector. -/
theorem frame_eq_rotationMatrix_oangle (e : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1) :
    frame e = rotationMatrix
      (orientation.oangle (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) e) := by
  -- The oriented-angle rotation carries the first standard unit vector to `e`.
  have hnorm :
      ‖(!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2))‖ = ‖e‖ := by
    rw [he]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hrotation :
      rotation (orientation.oangle (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) e)
          (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) = e :=
    (orientation.rotation_oangle_eq_iff_norm_eq
      (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) e).2 hnorm
  have hperp :
      orientation.rightAngleRotation
          (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) =
        (!₂[(0 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) := by
    rw [← perp]
    simpa using perp_apply (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2))
  have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hrotation
  have hone := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hrotation
  simp [rotation, Orientation.rotation_apply, hperp] at hzero hone
  -- These two coordinate identities identify all four matrix entries.
  ext i j
  fin_cases i
  · fin_cases j
    · simpa [frame, rotationMatrix] using hzero.symm
    · simpa [frame, rotationMatrix, perp_apply] using congrArg Neg.neg hone.symm
  · fin_cases j
    · simpa [frame, rotationMatrix] using hone.symm
    · simpa [frame, rotationMatrix, perp_apply] using hzero.symm

end EuclideanPlane
