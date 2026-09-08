module

public import ReasLib.Analysis.Complex.Polar

public section

namespace Complex

/-- In a positive annulus, the distance between two polar points dominates both their radial
separation and their principal angular separation. -/
theorem polarDistance_ge_max {rMin rMax r₁ r₂ θ₁ θ₂ : ℝ} (hrMin : 0 < rMin)
    (hr₁ : r₁ ∈ Set.Icc rMin rMax) (hr₂ : r₂ ∈ Set.Icc rMin rMax)
    (hθ : |θ₁ - θ₂| ≤ Real.pi) :
    max |r₁ - r₂| (2 * rMin / Real.pi * |θ₁ - θ₂|) ≤
      ‖(r₁ : ℂ) * Complex.exp (θ₁ * Complex.I) -
        (r₂ : ℂ) * Complex.exp (θ₂ * Complex.I)‖ := by
  apply max_le
  · simpa only [norm_mul, norm_real, Real.norm_eq_abs, norm_exp_ofReal_mul_I, mul_one,
      abs_of_pos (lt_of_lt_of_le hrMin hr₁.1), abs_of_pos (lt_of_lt_of_le hrMin hr₂.1)] using
      (abs_norm_sub_norm_le
        ((r₁ : ℂ) * Complex.exp (θ₁ * Complex.I))
        ((r₂ : ℂ) * Complex.exp (θ₂ * Complex.I)))
  · exact polarChordLowerBoundOfAbsSubLePi hrMin hr₁ hr₂ hθ

end Complex
