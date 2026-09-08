module

public import ReasLib.Analysis.Calculus.ContDiff.AffineCutoffBump
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

noncomputable section

open scoped ContDiff Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineBump

/-- The Fréchet derivative at the center of a scaled linear bump is the cutoff value times
the associated inner-product functional. -/
theorem fderiv_scaledLinearBump_apply_center (χ : E → ℝ) (hχ : ContDiff ℝ 2 χ)
    (x : E) (ρ : ℝ) (a : E) (hρ : 0 < ρ) :
    fderiv ℝ (scaledLinearBump χ x ρ a) x = χ 0 • innerSL ℝ a := by
  rw [fderiv_scaledLinearBump χ hχ x ρ a x hρ]
  simp

/-- The center gradient of a scaled linear bump is the cutoff value multiplied by its linear
coefficient. -/
theorem hasGradientAt_scaledLinearBump_center [CompleteSpace E]
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (x : E) (ρ : ℝ) (a : E) (hρ : 0 < ρ) :
    HasGradientAt (scaledLinearBump χ x ρ a) ((χ 0) • a) x := by
  have htwo_le : (2 : WithTop ℕ∞) ≤ ∞ := by
    have htwo_nat : (2 : ℕ∞) ≤ ⊤ := le_top
    exact WithTop.coe_le_coe.mpr htwo_nat
  have hχtwo : ContDiff ℝ 2 χ := hχ.of_le htwo_le
  have hdiff : DifferentiableAt ℝ (scaledLinearBump χ x ρ a) x := by
    have hinfty_ne : (∞ : WithTop ℕ∞) ≠ 0 := by
      norm_num
    exact (contDiff_scaledLinearBump χ hχ x ρ a).differentiable hinfty_ne x
  have hderiv : fderiv ℝ (scaledLinearBump χ x ρ a) x =
      χ 0 • innerSL ℝ a :=
    fderiv_scaledLinearBump_apply_center χ hχtwo x ρ a hρ
  have hdual : InnerProductSpace.toDual ℝ E ((χ 0) • a) =
      χ 0 • innerSL ℝ a := by
    ext v
    simp [innerSL_apply_apply]
  rw [hasGradientAt_iff_hasFDerivAt, hdual, ← hderiv]
  exact hdiff.hasFDerivAt

/-- If the cutoff equals one at the origin, the scaled linear bump has the prescribed center
gradient. -/
theorem hasGradientAt_scaledLinearBump_center_of_eq_one [CompleteSpace E]
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1)
    (x : E) (ρ : ℝ) (a : E) (hρ : 0 < ρ) :
    HasGradientAt (scaledLinearBump χ x ρ a) a x := by
  simpa [hχ0] using hasGradientAt_scaledLinearBump_center χ hχ x ρ a hρ

end AffineBump
