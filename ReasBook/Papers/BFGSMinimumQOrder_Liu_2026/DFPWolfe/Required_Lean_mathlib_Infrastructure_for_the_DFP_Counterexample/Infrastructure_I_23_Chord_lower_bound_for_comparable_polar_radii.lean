module

public import ReasLib.Analysis.Complex.Polar

public section

/- Infrastructure I.23 (Chord lower bound for comparable polar radii) (1) -/
#check (Complex.polarChordLowerBound :
  ∀ {rMin rMax r₁ r₂ θ₁ θ₂ : ℝ}, 0 < rMin →
    r₁ ∈ Set.Icc rMin rMax → r₂ ∈ Set.Icc rMin rMax →
      2 * rMin / Real.pi * |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)| ≤
        ‖(r₁ : ℂ) * Complex.exp (θ₁ * Complex.I) -
          (r₂ : ℂ) * Complex.exp (θ₂ * Complex.I)‖)

/- Infrastructure I.23 (Chord lower bound for comparable polar radii) (2) -/
#check (Complex.polarChordLowerBoundOfAbsSubLePi :
  ∀ {rMin rMax r₁ r₂ θ₁ θ₂ : ℝ}, 0 < rMin →
    r₁ ∈ Set.Icc rMin rMax → r₂ ∈ Set.Icc rMin rMax →
      |θ₁ - θ₂| ≤ Real.pi →
        2 * rMin / Real.pi * |θ₁ - θ₂| ≤
          ‖(r₁ : ℂ) * Complex.exp (θ₁ * Complex.I) -
            (r₂ : ℂ) * Complex.exp (θ₂ * Complex.I)‖)
