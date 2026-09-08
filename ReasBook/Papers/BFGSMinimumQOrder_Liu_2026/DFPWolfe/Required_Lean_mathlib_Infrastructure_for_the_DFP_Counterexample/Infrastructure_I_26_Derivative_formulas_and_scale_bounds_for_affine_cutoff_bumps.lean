module

public import DFPWolfe.Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample.Infrastructure_I_26_Derivative_formulas_and_scale_bounds_for_affine_cutoff_bumps_AffineBump

public section

open Set
open scoped ContDiff

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace AffineCutoffBump

/-- Infrastructure I.26 (Derivative formulas and scale bounds for affine cutoff bumps) (1):
the first Fréchet derivative of the affine cutoff bump. -/
theorem fderiv_eq (χ : E → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχ_support : tsupport χ ⊆ Metric.ball 0 1)
    (x : E) (ρ : ℝ) (a z : E) (hρ : 0 < ρ) :
    fderiv ℝ (affineCutoffBump χ x ρ a) z =
      χ (ρ⁻¹ • (z - x)) • innerSL ℝ a +
        (ρ⁻¹ * inner ℝ a (z - x)) •
          fderiv ℝ χ (ρ⁻¹ • (z - x)) := by
  exact AffineBump.fderiv_scaledLinearBump χ hχ x ρ a z hρ

/-- Infrastructure I.26 (Derivative formulas and scale bounds for affine cutoff bumps) (2):
the second Fréchet derivative of the affine cutoff bump, evaluated on two directions. -/
theorem secondFDeriv_apply (χ : E → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχ_support : tsupport χ ⊆ Metric.ball 0 1)
    (x : E) (ρ : ℝ) (a z v u : E) (hρ : 0 < ρ) :
    fderiv ℝ (fderiv ℝ (affineCutoffBump χ x ρ a)) z v u =
      ρ⁻¹ *
          (fderiv ℝ χ (ρ⁻¹ • (z - x)) v * inner ℝ a u +
            inner ℝ a v * fderiv ℝ χ (ρ⁻¹ • (z - x)) u) +
        ρ⁻¹ ^ 2 * inner ℝ a (z - x) *
          fderiv ℝ (fderiv ℝ χ) (ρ⁻¹ • (z - x)) v u := by
  exact AffineBump.secondFDeriv_scaledLinearBump_apply χ hχ x ρ a z v u hρ

/-- Infrastructure I.26 (Derivative formulas and scale bounds for affine cutoff bumps) (3):
the value bound on the support at positive scale. -/
theorem norm_le (χ : E → ℝ) (hχ : ContDiff ℝ 2 χ) (M₀ : ℝ)
    (hχ_support : tsupport χ ⊆ Metric.ball 0 1)
    (hχ_bound : ∀ y, ‖χ y‖ ≤ M₀)
    (x : E) (ρ : ℝ) (a z : E) (hρ : 0 < ρ)
    (hz : z ∈ tsupport (affineCutoffBump χ x ρ a)) :
    ‖affineCutoffBump χ x ρ a z‖ ≤ M₀ * ‖a‖ * ρ := by
  exact AffineBump.norm_scaledLinearBump_le
    χ hχ M₀ hχ_support hχ_bound x ρ a z hρ hz

/-- Infrastructure I.26 (Derivative formulas and scale bounds for affine cutoff bumps) (4):
the first-derivative bound on the support at positive scale. -/
theorem norm_fderiv_le (χ : E → ℝ) (hχ : ContDiff ℝ 2 χ) (M₀ M₁ : ℝ)
    (hχ_support : tsupport χ ⊆ Metric.ball 0 1)
    (hχ_bound : ∀ y, ‖χ y‖ ≤ M₀)
    (hDχ_bound : ∀ y, ‖fderiv ℝ χ y‖ ≤ M₁)
    (x : E) (ρ : ℝ) (a z : E) (hρ : 0 < ρ)
    (hz : z ∈ tsupport (affineCutoffBump χ x ρ a)) :
    ‖fderiv ℝ (affineCutoffBump χ x ρ a) z‖ ≤ (M₁ + M₀) * ‖a‖ := by
  exact AffineBump.norm_fderiv_scaledLinearBump_le
    χ hχ M₀ M₁ hχ_support hχ_bound hDχ_bound x ρ a z hρ hz

/-- Infrastructure I.26 (Derivative formulas and scale bounds for affine cutoff bumps) (5):
the second-derivative bound on the support at positive scale. -/
theorem norm_secondFDeriv_le (χ : E → ℝ) (hχ : ContDiff ℝ 2 χ) (M₁ M₂ : ℝ)
    (hχ_support : tsupport χ ⊆ Metric.ball 0 1)
    (hDχ_bound : ∀ y, ‖fderiv ℝ χ y‖ ≤ M₁)
    (hD2χ_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ χ) y‖ ≤ M₂)
    (x : E) (ρ : ℝ) (a z : E) (hρ : 0 < ρ)
    (hz : z ∈ tsupport (affineCutoffBump χ x ρ a)) :
    ‖fderiv ℝ (fderiv ℝ (affineCutoffBump χ x ρ a)) z‖ ≤
      (M₂ + 2 * M₁) * ‖a‖ / ρ := by
  exact AffineBump.norm_secondFDeriv_scaledLinearBump_le
    χ hχ M₁ M₂ hχ_support hDχ_bound hD2χ_bound x ρ a z hρ hz

end AffineCutoffBump
