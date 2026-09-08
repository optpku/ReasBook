module

public import ReasLib.Geometry.Euclidean.Plane.Rotation

/- Infrastructure I.4a (Planar rotations and positively oriented frames) (1):
the standard orientation, right-angle operator, rotations, and frame constructions. -/
#check (EuclideanPlane.orientation :
  Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2))
#check EuclideanPlane.perp
#check EuclideanPlane.rotation
#check EuclideanPlane.rotationMatrix
#check EuclideanPlane.frame

/- Infrastructure I.4a (Planar rotations and positively oriented frames) (2):
composition, inverse, determinant-one, and norm-preservation laws. -/
#check (Orientation.rotation_rotation :
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
      (theta₁ theta₂ : Real.Angle) (x : V),
    o.rotation theta₁ (o.rotation theta₂ x) = o.rotation (theta₁ + theta₂) x)
#check Orientation.rotation_symm
#check Orientation.det_rotation
#check LinearIsometryEquiv.norm_map

/- Infrastructure I.4a (Planar rotations and positively oriented frames) (3):
coordinate bridges among frames, vectors, matrices, and `Real.Angle`. -/
#check (EuclideanPlane.perp_apply :
  ∀ x : EuclideanSpace ℝ (Fin 2), EuclideanPlane.perp x = !₂[-x 1, x 0])
#check Orientation.rotation_apply
#check EuclideanPlane.toMatrix_rotation
#check EuclideanPlane.rotationMatrix_mulVec
#check EuclideanPlane.det_rotationMatrix
#check EuclideanPlane.frame_mulVec
#check EuclideanPlane.frame_mem_specialOrthogonalGroup_iff
#check EuclideanPlane.frame_eq_rotationMatrix_oangle
