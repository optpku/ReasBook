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

public section

noncomputable section

open Filter
open scoped Topology

namespace VariationalRegularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

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
  -- TODO: finish the little-o proof using `hGbig` to transport the `φ` remainder and
  -- a norm/inner-product estimate for the cross term.
  sorry

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
  -- TODO: package the pointwise helper over one common open neighborhood once the
  -- `hasGradientAt_representative_of_localInversePoint` proof is complete.
  sorry

end VariationalRegularization
