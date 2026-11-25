/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Order.Filter.Basic
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_4.Conjugate

public section

noncomputable section

open Filter
open scoped Topology

namespace VariationalRegularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Continuity makes the inner-product cross term negligible to first order. -/
lemma isLittleO_inner_sub_of_continuousAt (G : E → E) (y : E)
    (hG : ContinuousAt G y) :
    (fun z ↦ inner ℝ (G z - G y) (z - y)) =o[𝓝 y] fun z ↦ z - y := by
  have hsmall : (fun z ↦ ‖G z - G y‖) =o[𝓝 y] (fun _ : E ↦ (1 : ℝ)) := by
    apply Asymptotics.IsLittleO.norm_left
    exact (Asymptotics.isLittleO_one_iff ℝ).2
      (tendsto_sub_nhds_zero_iff.2 hG)
  have hproduct :
      (fun z ↦ ‖G z - G y‖ * ‖z - y‖) =o[𝓝 y] fun z ↦ z - y := by
    simpa only [one_mul, Asymptotics.isLittleO_norm_right] using
      hsmall.mul_isBigO (Asymptotics.isBigO_refl (fun z : E ↦ ‖z - y‖) (𝓝 y))
  exact (Asymptotics.IsBigO.of_norm_le fun z ↦
    norm_inner_le_norm (G z - G y) (z - y)).trans_isLittleO hproduct

/-- Helper for Theorem 8.7: the representative `z ↦ inner ℝ (G z) z - φ (G z)`
has gradient `G y` at a point `y` when `G` is continuous there, `G z - G y`
is locally `O(z - y)`, and `H (G y) = y` identifies the gradient of `φ` at
`G y`. -/
theorem hasGradientAt_representative_of_localInversePoint
    (φ : E → ℝ) (G H : E → E) (y : E)
    (hφ : HasGradientAt φ (H (G y)) (G y))
    (hG : ContinuousAt G y)
    (hGbig : (fun z ↦ G z - G y) =O[𝓝 y] fun z ↦ z - y)
    (hright : H (G y) = y) :
    HasGradientAt (fun z ↦ inner ℝ (G z) z - φ (G z)) (G y) y := by
  have hrem :
      (fun z ↦ φ (G z) - φ (G y) - inner ℝ y (G z - G y)) =o[𝓝 y]
        fun z ↦ z - y := by
    simpa only [hright, Function.comp_apply] using!
      ((hasGradientAt_iff_isLittleO.1 hφ).comp_tendsto hG).trans_isBigO hGbig
  rw [hasGradientAt_iff_isLittleO]
  refine ((isLittleO_inner_sub_of_continuousAt G y hG).sub hrem).congr_left fun z ↦ ?_
  simp only [inner_sub_left, inner_sub_right, real_inner_comm]
  ring

/-- If `G` is a local inverse branch of `H` near `y₀` and `φStar` is locally
represented by `y ↦ inner ℝ (G y) y - φ (G y)`, then `φStar` has
gradient `G y` near `y₀`, provided the branch also satisfies a local
`IsBigO` control relative to `z - y`. -/
theorem hasGradientAt_of_localInverseRepresentation
    (φ φStar : E → ℝ) (G H : E → E) (x₀ y₀ : E)
    (hφ : ∀ᶠ x in 𝓝 x₀, HasGradientAt φ (H x) x)
    (hG : Tendsto G (𝓝 y₀) (𝓝 x₀))
    (hcont : ∀ᶠ y in 𝓝 y₀, ContinuousAt G y)
    (hGbig : ∀ᶠ y in 𝓝 y₀, (fun z ↦ G z - G y) =O[𝓝 y] fun z ↦ z - y)
    (hright : ∀ᶠ y in 𝓝 y₀, H (G y) = y)
    (hrepr : ∀ᶠ y in 𝓝 y₀, φStar y = inner ℝ (G y) y - φ (G y)) :
    ∀ᶠ y in 𝓝 y₀, HasGradientAt φStar (G y) y := by
  filter_upwards [hG.eventually hφ, hcont, hGbig, hright, hrepr.eventually_nhds]
    with y hyφ hycont hybig hyright hyrepr
  exact (hasGradientAt_representative_of_localInversePoint φ G H y
    hyφ hycont hybig hyright).congr_of_eventuallyEq hyrepr

/-- A continuous choice of admissible maximizers differentiates the conjugate functional.
The supremum bounds its remainder between zero and an inner-product cross term. -/
theorem hasGradientAt_conjugateFunctionalToReal_of_continuous_optimizer
    (C : Set E) (φ : E → ℝ) (G : E → E) (y : E)
    (hG : ContinuousAt G y)
    (hmem : ∀ᶠ z in 𝓝 y, G z ∈ C)
    (hrepr : ∀ᶠ z in 𝓝 y,
      conjugateFunctional C φ z = ((inner ℝ (G z) z - φ (G z) : ℝ) : EReal)) :
    HasGradientAt (fun z ↦ (conjugateFunctional C φ z).toReal) (G y) y := by
  have hyC := hmem.self_of_nhds
  have hyrepr := hrepr.self_of_nhds
  have hsup (x z : E) (hx : x ∈ C) :
      ((inner ℝ x z - φ x : ℝ) : EReal) ≤ conjugateFunctional C φ z :=
    le_sSup ⟨x, hx, rfl⟩
  rw [hasGradientAt_iff_isLittleO]
  refine (Asymptotics.IsBigO.of_bound' ?_).trans_isLittleO
    (isLittleO_inner_sub_of_continuousAt G y hG)
  filter_upwards [hmem, hrepr] with z hzC hzrepr
  have hlower : inner ℝ (G y) z - φ (G y) ≤ inner ℝ (G z) z - φ (G z) := by
    exact EReal.coe_le_coe_iff.1 ((hsup (G y) z hyC).trans_eq hzrepr)
  have hupper : inner ℝ (G z) y - φ (G z) ≤ inner ℝ (G y) y - φ (G y) := by
    exact EReal.coe_le_coe_iff.1 ((hsup (G z) y hzC).trans_eq hyrepr)
  simp only [hzrepr, hyrepr, EReal.toReal_coe]
  have hnonneg :
      0 ≤ (inner ℝ (G z) z - φ (G z)) - (inner ℝ (G y) y - φ (G y)) -
        inner ℝ (G y) (z - y) := by
    simp only [inner_sub_right]
    linarith
  have hbound :
      (inner ℝ (G z) z - φ (G z)) - (inner ℝ (G y) y - φ (G y)) -
        inner ℝ (G y) (z - y) ≤ inner ℝ (G z - G y) (z - y) := by
    simp only [inner_sub_left, inner_sub_right]
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs]
  exact hbound.trans (le_abs_self _)

end VariationalRegularization
