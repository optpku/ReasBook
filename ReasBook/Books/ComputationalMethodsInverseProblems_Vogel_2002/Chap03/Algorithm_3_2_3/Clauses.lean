/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_2.ExactStep
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

universe u

namespace NonlinearConjugateGradient

/-- Algorithm 3.2.3. The displayed gradient refresh `gᵥ = gradient J (fᵥ)`. -/
abbrev HasGradientFormula {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (J : H → ℝ) (f g : ℕ → H) : Prop :=
  ∀ v : ℕ, g v = gradient J (f v)

/-- Algorithm 3.2.3. The displayed initialization `p₀ = -g₀`. -/
abbrev HasInitialDirection {H : Type u}
    [AddCommGroup H]
    (g p : ℕ → H) : Prop :=
  p 0 = -g 0

/-- Algorithm 3.2.3. The displayed initialization `δ₀ = ‖g₀‖²`. -/
abbrev HasInitialDelta {H : Type u}
    [NormedAddCommGroup H]
    (g : ℕ → H) (δ : ℕ → ℝ) : Prop :=
  δ 0 = ‖g 0‖ ^ 2

/-- Algorithm 3.2.3. The exact line-search clause
`τᵥ := arg min_(τ > 0) J (fᵥ + τ • pᵥ)`. -/
abbrev HasExactLineSearch {H : Type u}
    [AddCommGroup H] [Module ℝ H]
    (J : H → ℝ) (f p : ℕ → H) (τ : ℕ → ℝ) : Prop :=
  ∀ v : ℕ,
    LineSearch.IsExactStep J (f v) (p v) (τ v)

/-- Algorithm 3.2.3. The displayed solution update
`fᵥ₊₁ = fᵥ + τᵥ • pᵥ₊₁`, kept exactly as written even though it is the source
inconsistency blocking a faithful nonlinear-CG state/update owner. -/
abbrev HasDisplayedSolutionUpdate {H : Type u}
    [AddCommGroup H] [Module ℝ H]
    (f p : ℕ → H) (τ : ℕ → ℝ) : Prop :=
  ∀ v : ℕ, f (v + 1) = f v + τ v • p (v + 1)

/-- Algorithm 3.2.3. The displayed recurrence `δᵥ₊₁ = ‖gᵥ₊₁‖²`. -/
abbrev HasDeltaUpdate {H : Type u}
    [NormedAddCommGroup H]
    (g : ℕ → H) (δ : ℕ → ℝ) : Prop :=
  ∀ v : ℕ, δ (v + 1) = ‖g (v + 1)‖ ^ 2

/-- Algorithm 3.2.3. The Fletcher-Reeves scalar update
`βᵥ = δᵥ₊₁ / δᵥ`. -/
abbrev HasBetaFormula (δ β : ℕ → ℝ) : Prop :=
  ∀ v : ℕ, β v = δ (v + 1) / δ v

/-- Algorithm 3.2.3. The displayed search-direction recurrence
`pᵥ₊₁ = -gᵥ₊₁ + βᵥ • pᵥ`. -/
abbrev HasDirectionUpdate {H : Type u}
    [AddCommGroup H] [Module ℝ H]
    (g p : ℕ → H) (β : ℕ → ℝ) : Prop :=
  ∀ v : ℕ, p (v + 1) = -g (v + 1) + β v • p v

end NonlinearConjugateGradient
