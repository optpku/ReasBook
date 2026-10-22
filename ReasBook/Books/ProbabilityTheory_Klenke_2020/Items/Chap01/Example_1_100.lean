/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

open scoped ENNReal

-- Proof sketch: view the linear bijection as a linear map and apply
-- `Real.map_linearMap_volume_pi_eq_smul_volume_pi`; invertibility gives a nonzero determinant, and
-- `LinearEquiv.coe_det` identifies the determinant of the equivalence with the determinant of its
-- underlying linear map.
/-- Example 1.100: A linear bijection of `ℝ^n`, formalized as a linear equivalence of `Fin n → ℝ`,
pushes Lebesgue measure forward to `|det L|⁻¹` times Lebesgue measure. -/
theorem map_volume_linearEquiv_eq_smul_volume (n : ℕ)
    (L : (Fin n → ℝ) ≃ₗ[ℝ] Fin n → ℝ) :
    Measure.map L (volume : Measure (Fin n → ℝ)) =
      ENNReal.ofReal (abs (LinearEquiv.det L)⁻¹) • volume := by
  have hdet : LinearMap.det (L : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ) ≠ 0 :=
    IsUnit.ne_zero L.isUnit_det'
  simpa [LinearEquiv.coe_det] using
    (Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet :
      Measure.map (L : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ) volume =
        ENNReal.ofReal (abs (LinearMap.det (L : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ))⁻¹) • volume)
