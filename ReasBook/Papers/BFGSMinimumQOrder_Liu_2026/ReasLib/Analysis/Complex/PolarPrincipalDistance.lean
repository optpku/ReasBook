module

public import ReasLib.Analysis.Complex.Polar

public section

namespace Complex

/-- The principal polar distance is bounded below by both radial separation and angular
separation when both radii are at least `rMin`. -/
theorem polarDistance_ge_max_principal {rMin r₁ r₂ θ₁ θ₂ : ℝ} (hrMin : 0 < rMin)
    (hr₁ : rMin ≤ r₁) (hr₂ : rMin ≤ r₂) :
    max |r₁ - r₂| (2 * rMin / Real.pi *
      |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)|) ≤
      ‖(r₁ : ℂ) * Complex.exp (θ₁ * Complex.I) -
        (r₂ : ℂ) * Complex.exp (θ₂ * Complex.I)‖ := by
  have hr₁Icc : r₁ ∈ Set.Icc rMin (max r₁ r₂) := by
    constructor
    · exact hr₁
    · exact le_max_left _ _
  have hr₂Icc : r₂ ∈ Set.Icc rMin (max r₁ r₂) := by
    constructor
    · exact hr₂
    · exact le_max_right _ _
  have hrad : |r₁ - r₂| ≤
      ‖(r₁ : ℂ) * Complex.exp (θ₁ * Complex.I) -
        (r₂ : ℂ) * Complex.exp (θ₂ * Complex.I)‖ := by
    simpa only [norm_mul, norm_real, Real.norm_eq_abs, norm_exp_ofReal_mul_I, mul_one,
      abs_of_pos (lt_of_lt_of_le hrMin hr₁), abs_of_pos (lt_of_lt_of_le hrMin hr₂)] using
      (abs_norm_sub_norm_le
        ((r₁ : ℂ) * Complex.exp (θ₁ * Complex.I))
        ((r₂ : ℂ) * Complex.exp (θ₂ * Complex.I)))
  have hang : 2 * rMin / Real.pi *
      |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)| ≤
      ‖(r₁ : ℂ) * Complex.exp (θ₁ * Complex.I) -
        (r₂ : ℂ) * Complex.exp (θ₂ * Complex.I)‖ := by
    exact polarChordLowerBound (rMax := max r₁ r₂) hrMin hr₁Icc hr₂Icc
  exact max_le hrad hang

end Complex
