/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_2

public section

noncomputable section

namespace GradientProjection

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A projected step satisfies the inexact sufficient-decrease condition when it
obeys the source bounds on `τ` and `c₁` together with the projected Armijo-type
inequality using the displacement `P (f_v + τ • p_v) - f_v`, measured along the
canonical line-search profile of `J ∘ P`. -/
def SufficientDecrease
    (P : H → H) (J : H → ℝ) (f_v p_v : H) (τ c₁ : ℝ) : Prop :=
  0 < τ ∧
    0 < c₁ ∧
    c₁ < 1 ∧
    LineSearch.profile (J ∘ P) f_v p_v τ ≤
      LineSearch.profile (J ∘ P) f_v p_v 0 +
        c₁ * inner ℝ (gradient J f_v) (P (f_v + τ • p_v) - f_v)

/-- The projected sufficient-decrease condition is equivalent to the displayed
source inequality `J (P (f_v + τ • p_v)) ≤ J (P f_v) + c₁ * inner ℝ
(gradient J f_v) (P (f_v + τ • p_v) - f_v)` together with the source bounds on
`τ` and `c₁`. -/
theorem sufficientDecrease_iff
    (P : H → H) (J : H → ℝ) (f_v p_v : H) (τ c₁ : ℝ) :
    SufficientDecrease P J f_v p_v τ c₁ ↔
      0 < τ ∧
        0 < c₁ ∧
        c₁ < 1 ∧
        J (P (f_v + τ • p_v)) ≤
          J (P f_v) +
            c₁ * inner ℝ (gradient J f_v) (P (f_v + τ • p_v) - f_v) := by
  constructor
  · rintro ⟨hτ, hc₁, hc₁_lt, hle⟩
    refine ⟨hτ, hc₁, hc₁_lt, ?_⟩
    simpa [LineSearch.profile_apply, Function.comp, zero_smul, add_zero] using hle
  · rintro ⟨hτ, hc₁, hc₁_lt, hle⟩
    refine ⟨hτ, hc₁, hc₁_lt, ?_⟩
    simpa [LineSearch.profile_apply, Function.comp, zero_smul, add_zero] using hle

/-- A projected sufficient-decrease step satisfies the source bounds on `τ` and
`c₁`. -/
theorem SufficientDecrease.bounds
    {P : H → H} {J : H → ℝ} {f_v p_v : H} {τ c₁ : ℝ}
    (h : SufficientDecrease P J f_v p_v τ c₁) :
    0 < τ ∧ 0 < c₁ ∧ c₁ < 1 :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- A projected sufficient-decrease step satisfies the projected Armijo-type
inequality. -/
theorem SufficientDecrease.le
    {P : H → H} {J : H → ℝ} {f_v p_v : H} {τ c₁ : ℝ}
    (h : SufficientDecrease P J f_v p_v τ c₁) :
    J (P (f_v + τ • p_v)) ≤
      J (P f_v) +
        c₁ * inner ℝ (gradient J f_v) (P (f_v + τ • p_v) - f_v) := by
  exact (sufficientDecrease_iff P J f_v p_v τ c₁).mp h |>.2.2.2

end GradientProjection
