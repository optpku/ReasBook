module

public import ReasLib.Analysis.Complex.PolarIsometry
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

namespace Complex

/-- Transport the principal polar separation estimate through the isometry induced by a real
orthonormal basis of a two-dimensional inner product space. -/
theorem polarDistance_ge_max_principal_sub_errors_of_orthonormalBasis
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (v : OrthonormalBasis (Fin 2) ℝ F) {z₁ z₂ : F} {p₁ p₂ : ℂ}
    {rMin r₁ r₂ θ₁ θ₂ e₁ e₂ : ℝ}
    (hp₁ : p₁ = (r₁ : ℂ) * Complex.exp (θ₁ * Complex.I))
    (hp₂ : p₂ = (r₂ : ℂ) * Complex.exp (θ₂ * Complex.I))
    (hrMin : 0 < rMin) (hr₁ : rMin ≤ r₁) (hr₂ : rMin ≤ r₂)
    (hz₁ : dist z₁ (Complex.isometryOfOrthonormal v p₁) ≤ e₁)
    (hz₂ : dist z₂ (Complex.isometryOfOrthonormal v p₂) ≤ e₂) :
    max |r₁ - r₂| (2 * rMin / Real.pi *
      |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)|) - e₁ - e₂ ≤ dist z₁ z₂ := by
  exact polarDistance_ge_max_principal_sub_errors_of_linearIsometryEquiv
    (Complex.isometryOfOrthonormal v) hp₁ hp₂ hrMin hr₁ hr₂ hz₁ hz₂

/-- The same polar separation estimate for points measured relative to a common center. -/
theorem polarDistance_ge_max_principal_sub_errors_of_orthonormalBasis_sub_center
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (v : OrthonormalBasis (Fin 2) ℝ F) {c z₁ z₂ : F} {p₁ p₂ : ℂ}
    {rMin r₁ r₂ θ₁ θ₂ e₁ e₂ : ℝ}
    (hp₁ : p₁ = (r₁ : ℂ) * Complex.exp (θ₁ * Complex.I))
    (hp₂ : p₂ = (r₂ : ℂ) * Complex.exp (θ₂ * Complex.I))
    (hrMin : 0 < rMin) (hr₁ : rMin ≤ r₁) (hr₂ : rMin ≤ r₂)
    (hz₁ : dist (z₁ - c) (Complex.isometryOfOrthonormal v p₁) ≤ e₁)
    (hz₂ : dist (z₂ - c) (Complex.isometryOfOrthonormal v p₂) ≤ e₂) :
    max |r₁ - r₂| (2 * rMin / Real.pi *
      |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)|) - e₁ - e₂ ≤ dist z₁ z₂ := by
  have htranslated := polarDistance_ge_max_principal_sub_errors_of_orthonormalBasis
    v (z₁ := z₁ - c) (z₂ := z₂ - c) hp₁ hp₂ hrMin hr₁ hr₂ hz₁ hz₂
  calc
    max |r₁ - r₂| (2 * rMin / Real.pi *
        |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)|) - e₁ - e₂ ≤
        dist (z₁ - c) (z₂ - c) := htranslated
    _ = dist z₁ z₂ := by
      simp only [dist_eq_norm, sub_sub_sub_cancel_right]

end Complex
