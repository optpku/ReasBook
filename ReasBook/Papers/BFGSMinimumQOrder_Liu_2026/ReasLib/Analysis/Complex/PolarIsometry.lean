module

public import ReasLib.Analysis.Complex.PolarPerturbation

public section

namespace Complex

/-- Transport the principal polar distance estimate across a real linear isometry equivalence.
The complex polar representatives are exposed as `p₁` and `p₂`, so the error hypotheses can be
stated directly in the target normed space. -/
theorem polarDistance_ge_max_principal_sub_errors_of_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ℂ ≃ₗᵢ[ℝ] E) {z₁ z₂ : E} {p₁ p₂ : ℂ}
    {rMin r₁ r₂ θ₁ θ₂ e₁ e₂ : ℝ}
    (hp₁ : p₁ = (r₁ : ℂ) * Complex.exp (θ₁ * Complex.I))
    (hp₂ : p₂ = (r₂ : ℂ) * Complex.exp (θ₂ * Complex.I))
    (hrMin : 0 < rMin) (hr₁ : rMin ≤ r₁) (hr₂ : rMin ≤ r₂)
    (hz₁ : dist z₁ (φ p₁) ≤ e₁) (hz₂ : dist z₂ (φ p₂) ≤ e₂) :
    max |r₁ - r₂| (2 * rMin / Real.pi *
      |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)|) - e₁ - e₂ ≤ dist z₁ z₂ := by
  have hz₁_map : dist (φ.symm z₁) p₁ ≤ e₁ := by
    calc
      dist (φ.symm z₁) p₁ = dist (φ (φ.symm z₁)) (φ p₁) := by
        simpa using (φ.dist_map (φ.symm z₁) p₁).symm
      _ = dist z₁ (φ p₁) := by rw [φ.apply_symm_apply]
      _ ≤ e₁ := hz₁
  have hz₂_map : dist (φ.symm z₂) p₂ ≤ e₂ := by
    calc
      dist (φ.symm z₂) p₂ = dist (φ (φ.symm z₂)) (φ p₂) := by
        simpa using (φ.dist_map (φ.symm z₂) p₂).symm
      _ = dist z₂ (φ p₂) := by rw [φ.apply_symm_apply]
      _ ≤ e₂ := hz₂
  have hz₁_norm : ‖φ.symm z₁ -
      ((r₁ : ℂ) * Complex.exp (θ₁ * Complex.I))‖ ≤ e₁ := by
    simpa only [dist_eq_norm, hp₁] using hz₁_map
  have hz₂_norm : ‖φ.symm z₂ -
      ((r₂ : ℂ) * Complex.exp (θ₂ * Complex.I))‖ ≤ e₂ := by
    simpa only [dist_eq_norm, hp₂] using hz₂_map
  have hcomplex := polarDistance_ge_max_principal_sub_errors
    (z₁ := φ.symm z₁) (z₂ := φ.symm z₂) hrMin hr₁ hr₂ hz₁_norm hz₂_norm
  have hdist : ‖φ.symm z₁ - φ.symm z₂‖ = dist z₁ z₂ := by
    simpa only [dist_eq_norm] using φ.symm.dist_map z₁ z₂
  calc
    max |r₁ - r₂| (2 * rMin / Real.pi *
        |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)|) - e₁ - e₂ ≤
        ‖φ.symm z₁ - φ.symm z₂‖ := hcomplex
    _ = dist z₁ z₂ := hdist

end Complex
