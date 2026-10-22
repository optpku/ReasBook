/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic

public section

noncomputable section

universe u v w

namespace ContinuousLinearMap

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}

section Objective

variable [NormedField 𝕜]
variable [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]

/-- The generalized Tikhonov functional `f ↦ ρ (K f, g) + α * J f` for a bounded linear
operator `K`, datum `g`, discrepancy functional `ρ`, penalty functional `J`, and parameter
`α`. -/
def generalizedTikhonovFunctional
    (K : H₁ →L[𝕜] H₂) (g : H₂) (ρ : H₂ × H₂ → ℝ) (J : H₁ → ℝ) (α : ℝ) : H₁ → ℝ :=
  fun f ↦ ρ (K f, g) + α * J f

/-- Definition 2.4-extra-1. The defining formula for
`ContinuousLinearMap.generalizedTikhonovFunctional`, namely
`f ↦ ρ (K f, g) + α * J f`. -/
theorem generalizedTikhonovFunctional_def
    (K : H₁ →L[𝕜] H₂) (g : H₂) (ρ : H₂ × H₂ → ℝ) (J : H₁ → ℝ) (α : ℝ) (f : H₁) :
    K.generalizedTikhonovFunctional g ρ J α f = ρ (K f, g) + α * J f := by
  -- Unfold the objective at `f`; the two sides are definitionally equal.
  rfl

end Objective

end ContinuousLinearMap
