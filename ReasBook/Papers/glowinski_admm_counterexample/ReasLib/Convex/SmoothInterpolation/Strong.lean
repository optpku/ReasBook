module

public import glowinski_admm_counterexample.ReasLib.Convex.SmoothInterpolation.Finite
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

open Set Filter
open scoped Topology RealInnerProductSpace

namespace SmoothInterpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

namespace QuadraticCore

variable {H : E → ℝ} {m : ℝ} (hH : QuadraticCore H m)

/-- Add a quadratic to obtain strong convexity without losing smoothness. -/
noncomputable def shift (μ : ℝ) (x : E) : ℝ := hH.conjugate x + μ / 2 * ‖x‖ ^ 2

theorem shift_stronglyConvex (μ : ℝ) : StrongConvexOn univ μ (hH.shift μ) := by
  rw [strongConvexOn_iff_convex]
  simpa only [shift, add_sub_cancel_right] using hH.convexOn_conjugate

theorem shift_contDiff (μ : ℝ) : ContDiff ℝ 1 (hH.shift μ) :=
  hH.contDiff_conjugate.add (contDiff_const.mul (contDiff_norm_sq ℝ))

theorem hasFDerivAt_shift (μ : ℝ) (x : E) :
    HasFDerivAt (hH.shift μ) (innerSL ℝ (hH.gradient x + μ • x)) x := by
  have hlin : innerSL ℝ (hH.gradient x + μ • x) =
      innerSL ℝ (hH.gradient x) + (μ/2) • (2 • innerSL ℝ x) := by
    ext t
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      innerSL_apply_apply, inner_add_left, real_inner_smul_left, smul_eq_mul]
    ring
  rw [hlin]
  exact (hH.hasFDerivAt_conjugate x).add
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (μ/2))

/-- The shifted gradient remains globally Lipschitz. -/
theorem shift_fderiv_lipschitz (μ : ℝ) (hμ : 0 ≤ μ) :
    LipschitzWith (hH.constant + ⟨μ, hμ⟩) (fderiv ℝ (hH.shift μ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [(hH.hasFDerivAt_shift μ x).fderiv, (hH.hasFDerivAt_shift μ y).fderiv,
    dist_eq_norm, ← map_sub, innerSL_apply_norm, dist_eq_norm]
  change ‖(hH.gradient x + μ • x) - (hH.gradient y + μ • y)‖ ≤
    (m⁻¹ + μ) * ‖x-y‖
  rw [show (hH.gradient x + μ • x) - (hH.gradient y + μ • y) =
    (hH.gradient x-hH.gradient y) + μ • (x-y) by module]
  calc
    _ ≤ ‖hH.gradient x-hH.gradient y‖ + ‖μ • (x-y)‖ := norm_add_le _ _
    _ ≤ m⁻¹ * ‖x-y‖ + μ * ‖x-y‖ := by
      rw [norm_smul, Real.norm_of_nonneg hμ]
      exact add_le_add_left (hH.gradient_norm_sub x y) _
    _ = _ := by ring

theorem shift_zero (μ : ℝ) : hH.shift μ 0 = 0 := by
  simp only [shift, hH.conjugate_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero]

theorem shift_lower (μ : ℝ) (x : E) : μ / 2 * ‖x‖ ^ 2 ≤ hH.shift μ x := by
  have := hH.conjugate_nonneg x
  dsimp [shift]
  linarith

/-- The shifted conjugate has a global supporting paraboloid at every point. -/
theorem shift_support (μ : ℝ) (x y : E) :
    hH.shift μ x + ⟪hH.gradient x + μ • x, y-x⟫ + μ/2 * ‖y-x‖^2 ≤ hH.shift μ y := by
  have hb := (hH.remainder x y).1
  dsimp [shift]
  rw [inner_add_left, real_inner_smul_left, inner_sub_right, norm_sub_sq_real]
  rw [inner_sub_right] at hb
  have hi := real_inner_comm x y
  have hs : ⟪x, x⟫ = ‖x‖^2 := real_inner_self_eq_norm_sq x
  simp only [inner_sub_right] at *
  rw [hi, hs]
  linarith

end QuadraticCore

end SmoothInterpolation
