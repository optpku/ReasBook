module

public import ReasLib.Analysis.Complex.PolarPrincipalDistance

public section

namespace Complex

/-- Perturbing two polar points by errors `e₁` and `e₂` lowers the principal polar distance
bound by at most the sum of those errors. -/
theorem polarDistance_ge_max_principal_sub_errors
    {z₁ z₂ : ℂ} {rMin r₁ r₂ θ₁ θ₂ e₁ e₂ : ℝ} (hrMin : 0 < rMin)
    (hr₁ : rMin ≤ r₁) (hr₂ : rMin ≤ r₂)
    (hz₁ : ‖z₁ - ((r₁ : ℂ) * Complex.exp (θ₁ * Complex.I))‖ ≤ e₁)
    (hz₂ : ‖z₂ - ((r₂ : ℂ) * Complex.exp (θ₂ * Complex.I))‖ ≤ e₂) :
    max |r₁ - r₂| (2 * rMin / Real.pi *
      |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)|) - e₁ - e₂ ≤ ‖z₁ - z₂‖ := by
  let p₁ : ℂ := (r₁ : ℂ) * Complex.exp (θ₁ * Complex.I)
  let p₂ : ℂ := (r₂ : ℂ) * Complex.exp (θ₂ * Complex.I)
  have hpolar : max |r₁ - r₂| (2 * rMin / Real.pi *
      |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)|) ≤ ‖p₁ - p₂‖ := by
    simpa [p₁, p₂] using polarDistance_ge_max_principal hrMin hr₁ hr₂
  have hz₁' : ‖p₁ - z₁‖ ≤ e₁ := by
    simpa [p₁, norm_sub_rev] using hz₁
  have hz₂' : ‖z₂ - p₂‖ ≤ e₂ := by
    simpa [p₂] using hz₂
  have htriangle : ‖p₁ - p₂‖ ≤ ‖p₁ - z₁‖ + ‖z₁ - z₂‖ + ‖z₂ - p₂‖ := by
    have hdecomp : p₁ - p₂ = (p₁ - z₁) + ((z₁ - z₂) + (z₂ - p₂)) := by
      ring
    have hinner : ‖(z₁ - z₂) + (z₂ - p₂)‖ ≤ ‖z₁ - z₂‖ + ‖z₂ - p₂‖ :=
      norm_add_le (z₁ - z₂) (z₂ - p₂)
    calc
      ‖p₁ - p₂‖ = ‖(p₁ - z₁) + ((z₁ - z₂) + (z₂ - p₂))‖ := by rw [hdecomp]
      _ ≤ ‖p₁ - z₁‖ + ‖(z₁ - z₂) + (z₂ - p₂)‖ :=
        norm_add_le (p₁ - z₁) ((z₁ - z₂) + (z₂ - p₂))
      _ ≤ ‖p₁ - z₁‖ + (‖z₁ - z₂‖ + ‖z₂ - p₂‖) :=
        add_le_add_right hinner _
      _ = ‖p₁ - z₁‖ + ‖z₁ - z₂‖ + ‖z₂ - p₂‖ := by ring
  linarith

end Complex
