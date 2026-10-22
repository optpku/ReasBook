/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic

public section

noncomputable section

namespace LineSearch

/-- The source bounds on a step length `τ` and Armijo parameter `c₁`. -/
def SufficientDecreaseBounds (τ c₁ : ℝ) : Prop :=
  0 < τ ∧ 0 < c₁ ∧ c₁ < 1

/-- The sufficient decrease condition for a one-dimensional line-search profile. -/
def SufficientDecrease (φ : ℝ → ℝ) (τ c₁ : ℝ) : Prop :=
  SufficientDecreaseBounds τ c₁ ∧ φ τ ≤ φ 0 + c₁ * τ * deriv φ 0

/-- The sufficient decrease condition is exactly the source bounds together with
the Armijo inequality. -/
theorem sufficientDecrease_iff {φ : ℝ → ℝ} {τ c₁ : ℝ} :
    SufficientDecrease φ τ c₁ ↔
      SufficientDecreaseBounds τ c₁ ∧ φ τ ≤ φ 0 + c₁ * τ * deriv φ 0 :=
  Iff.rfl

/-- A sufficient-decrease step satisfies the source bounds on `τ` and `c₁`. -/
theorem SufficientDecrease.bounds {φ : ℝ → ℝ} {τ c₁ : ℝ}
    (h : SufficientDecrease φ τ c₁) : SufficientDecreaseBounds τ c₁ :=
  h.1

/-- A sufficient-decrease step satisfies the Armijo inequality. -/
theorem SufficientDecrease.le {φ : ℝ → ℝ} {τ c₁ : ℝ}
    (h : SufficientDecrease φ τ c₁) :
    φ τ ≤ φ 0 + c₁ * τ * deriv φ 0 :=
  h.2

/-- The source bounds on `τ`, `c₁`, and `c₂` used in the curvature condition. -/
def CurvatureBounds (τ c₁ c₂ : ℝ) : Prop :=
  0 < τ ∧ c₁ < c₂ ∧ c₂ < 1

/-- The curvature condition for a one-dimensional line-search profile. -/
def CurvatureCondition (φ : ℝ → ℝ) (τ c₁ c₂ : ℝ) : Prop :=
  CurvatureBounds τ c₁ c₂ ∧ c₂ * deriv φ 0 ≤ deriv φ τ

/-- The curvature condition is exactly the source bounds together with the
derivative inequality. -/
theorem curvatureCondition_iff {φ : ℝ → ℝ} {τ c₁ c₂ : ℝ} :
    CurvatureCondition φ τ c₁ c₂ ↔
      CurvatureBounds τ c₁ c₂ ∧ c₂ * deriv φ 0 ≤ deriv φ τ :=
  Iff.rfl

/-- A curvature-condition step satisfies the source bounds on `τ`, `c₁`, and `c₂`. -/
theorem CurvatureCondition.bounds {φ : ℝ → ℝ} {τ c₁ c₂ : ℝ}
    (h : CurvatureCondition φ τ c₁ c₂) : CurvatureBounds τ c₁ c₂ :=
  h.1

/-- A curvature-condition step satisfies the derivative inequality. -/
theorem CurvatureCondition.le {φ : ℝ → ℝ} {τ c₁ c₂ : ℝ}
    (h : CurvatureCondition φ τ c₁ c₂) :
    c₂ * deriv φ 0 ≤ deriv φ τ :=
  h.2

/-- The Wolfe conditions for a one-dimensional line-search profile. -/
def Wolfe (φ : ℝ → ℝ) (τ c₁ c₂ : ℝ) : Prop :=
  SufficientDecrease φ τ c₁ ∧ CurvatureCondition φ τ c₁ c₂

/-- A Wolfe step satisfies the sufficient decrease condition. -/
theorem Wolfe.sufficientDecrease {φ : ℝ → ℝ} {τ c₁ c₂ : ℝ}
    (h : Wolfe φ τ c₁ c₂) : SufficientDecrease φ τ c₁ :=
  h.1

/-- A Wolfe step satisfies the curvature condition. -/
theorem Wolfe.curvatureCondition {φ : ℝ → ℝ} {τ c₁ c₂ : ℝ}
    (h : Wolfe φ τ c₁ c₂) : CurvatureCondition φ τ c₁ c₂ :=
  h.2

/-- The Wolfe conditions are exactly the conjunction of sufficient decrease and
curvature. -/
theorem wolfe_iff {φ : ℝ → ℝ} {τ c₁ c₂ : ℝ} :
    Wolfe φ τ c₁ c₂ ↔ SufficientDecrease φ τ c₁ ∧ CurvatureCondition φ τ c₁ c₂ :=
  Iff.rfl

end LineSearch
