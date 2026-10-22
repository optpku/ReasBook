/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Exercise_8_2.Penalty

public section

noncomputable section

namespace VariationalRegularization

/-- The homogeneous-Neumann boundary condition on the unit square, written
explicitly as vanishing normal partials on the corresponding boundary edges. -/
@[expose]
def hasVanishingNormalDerivativeOnUnitSquareBoundary (f : ℝ × ℝ → ℝ) : Prop :=
  ∀ p, p ∈ unitSquareBoundary →
    ((p.1 = 0 ∨ p.1 = 1) → unitSquarePartialX f p = 0) ∧
      ((p.2 = 0 ∨ p.2 = 1) → unitSquarePartialY f p = 0)

/-- The defining edgewise formula for
`hasVanishingNormalDerivativeOnUnitSquareBoundary`. -/
theorem hasVanishingNormalDerivativeOnUnitSquareBoundary_def (f : ℝ × ℝ → ℝ) :
    hasVanishingNormalDerivativeOnUnitSquareBoundary f ↔
      ∀ p, p ∈ unitSquareBoundary →
        ((p.1 = 0 ∨ p.1 = 1) → unitSquarePartialX f p = 0) ∧
          ((p.2 = 0 ∨ p.2 = 1) → unitSquarePartialY f p = 0) := by
  -- This is the exposed predicate definition for the boundary condition.
  rfl

/-- The weighted diffusion operator `(8.27)` associated to `ψ` and the current
state `f`, acting on a raw unit-square function `u`. -/
@[expose]
def unitSquareWeightedDiffusion
    (ψ : ℝ → ℝ) (f u : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p ↦
    -unitSquarePartialX
        (fun q ↦ deriv ψ (unitSquareGradientSq f q) * unitSquarePartialX u q) p -
      unitSquarePartialY
        (fun q ↦ deriv ψ (unitSquareGradientSq f q) * unitSquarePartialY u q) p

/-- The defining pointwise formula for `unitSquareWeightedDiffusion`. -/
theorem unitSquareWeightedDiffusion_apply
    (ψ : ℝ → ℝ) (f u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    unitSquareWeightedDiffusion ψ f u p =
      -unitSquarePartialX
          (fun q ↦ deriv ψ (unitSquareGradientSq f q) * unitSquarePartialX u q) p -
        unitSquarePartialY
          (fun q ↦ deriv ψ (unitSquareGradientSq f q) * unitSquarePartialY u q) p := by
  -- This theorem just unfolds the weighted diffusion operator.
  rfl

end VariationalRegularization
