/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_23_Chord_lower_bound_for_comparable_polar_radii.lean
-/

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
