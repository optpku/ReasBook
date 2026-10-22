/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Remark_3_4.Wolfe

public section

noncomputable section

namespace LineSearch

/-- Remark 3.4-extra-2 (1). Under explicit derivative data at `0`, the sufficient
decrease condition is the inequality `φ τ ≤ φ 0 + c₁ * τ * d₀` together with the
source bounds on `τ` and `c₁`. -/
theorem sufficientDecrease_iff_hasDerivAt {φ : ℝ → ℝ} {τ c₁ d₀ : ℝ}
    (h0 : HasDerivAt φ d₀ 0) :
    SufficientDecrease φ τ c₁ ↔
      SufficientDecreaseBounds τ c₁ ∧ φ τ ≤ φ 0 + c₁ * τ * d₀ := by
  rw [sufficientDecrease_iff]
  simp [h0.deriv]

/-- Remark 3.4-extra-2 (2). Under explicit derivative data at `0` and `τ`, the
curvature condition is the inequality `c₂ * d₀ ≤ dτ` together with the source
bounds on `τ`, `c₁`, and `c₂`. -/
theorem curvatureCondition_iff_hasDerivAt {φ : ℝ → ℝ} {τ c₁ c₂ d₀ dτ : ℝ}
    (h0 : HasDerivAt φ d₀ 0) (hτ : HasDerivAt φ dτ τ) :
    CurvatureCondition φ τ c₁ c₂ ↔
      CurvatureBounds τ c₁ c₂ ∧ c₂ * d₀ ≤ dτ := by
  rw [curvatureCondition_iff]
  simp [h0.deriv, hτ.deriv]

/- Remark 3.4-extra-2 (3). The Wolfe conditions are exactly the conjunction of
the sufficient decrease and curvature conditions. -/
#check wolfe_iff

/- The final convergence sentence in the source excerpt is intentionally not
formalized here: the required mild hypotheses on the cost function `J`, the
search directions `p`, and an iterate update such as `f (v + 1) = f v + τ v • p v`
are not specified in the available source data. -/

end LineSearch
