module

public import ReasLib.Analysis.Complex.PolarOrthonormal
public import ReasLib.Geometry.Euclidean.Plane.Rotation

public section

noncomputable section

open scoped EuclideanSpace

namespace EuclideanPlane

/-- The standard real-linear isometry from the complex plane to the Euclidean plane. -/
def complexIsometry : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- Under `complexIsometry`, a complex polar vector is the standard planar rotation of the
first coordinate vector, scaled by its radius. -/
theorem complexIsometry_apply_mul_exp (r θ : ℝ) :
    complexIsometry ((r : ℂ) * Complex.exp (θ * Complex.I)) =
      r • rotation (θ : Real.Angle) (EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
  rw [complexIsometry, Complex.isometryOfOrthonormal_apply, rotation_apply]
  ext i
  fin_cases i
  · simp [perp_apply, Complex.mul_re, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  · simp [perp_apply, Complex.mul_re, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- Two planar points close to polar vectors about a common center inherit the maximum of the
radial and principal angular separation bounds, up to their two approximation errors. -/
theorem polarDistance_ge_max_principal_sub_errors
    {c z₁ z₂ : EuclideanSpace ℝ (Fin 2)}
    {rMin r₁ r₂ θ₁ θ₂ e₁ e₂ : ℝ}
    (hrMin : 0 < rMin) (hr₁ : rMin ≤ r₁) (hr₂ : rMin ≤ r₂)
    (hz₁ : dist (z₁ - c)
      (r₁ • rotation (θ₁ : Real.Angle) (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ e₁)
    (hz₂ : dist (z₂ - c)
      (r₂ • rotation (θ₂ : Real.Angle) (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ e₂) :
    max |r₁ - r₂| (2 * rMin / Real.pi *
      |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)|) - e₁ - e₂ ≤ dist z₁ z₂ := by
  have hz₁Complex :
      dist (z₁ - c)
        (complexIsometry ((r₁ : ℂ) * Complex.exp (θ₁ * Complex.I))) ≤ e₁ := by
    rw [complexIsometry_apply_mul_exp]
    exact hz₁
  have hz₂Complex :
      dist (z₂ - c)
        (complexIsometry ((r₂ : ℂ) * Complex.exp (θ₂ * Complex.I))) ≤ e₂ := by
    rw [complexIsometry_apply_mul_exp]
    exact hz₂
  exact Complex.polarDistance_ge_max_principal_sub_errors_of_orthonormalBasis_sub_center
    (EuclideanSpace.basisFun (Fin 2) ℝ)
    (p₁ := (r₁ : ℂ) * Complex.exp (θ₁ * Complex.I))
    (p₂ := (r₂ : ℂ) * Complex.exp (θ₂ * Complex.I))
    rfl rfl hrMin hr₁ hr₂ hz₁Complex hz₂Complex

end EuclideanPlane
