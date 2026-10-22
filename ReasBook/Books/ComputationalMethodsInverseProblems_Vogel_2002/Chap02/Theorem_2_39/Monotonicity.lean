/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_32

public section

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `GradientMonotoneOn J C` is the Hilbert-space monotonicity condition
`0 ≤ inner ℝ (gradient J f₁ - gradient J f₂) (f₁ - f₂)` for all `f₁, f₂ ∈ C`. -/
def GradientMonotoneOn (J : H → ℝ) (C : Set H) : Prop :=
  ∀ ⦃f₁ f₂ : H⦄, f₁ ∈ C → f₂ ∈ C →
    0 ≤ inner ℝ (gradient J f₁ - gradient J f₂) (f₁ - f₂)

/-- Specification lemma for `GradientMonotoneOn`. -/
theorem gradientMonotoneOn_iff (J : H → ℝ) (C : Set H) :
    GradientMonotoneOn J C ↔
      ∀ ⦃f₁ f₂ : H⦄, f₁ ∈ C → f₂ ∈ C →
        0 ≤ inner ℝ (gradient J f₁ - gradient J f₂) (f₁ - f₂) := by
  rfl

/-- `GradientStrictMonotoneOn J C` is the strict Hilbert-space monotonicity condition
`0 < inner ℝ (gradient J f₁ - gradient J f₂) (f₁ - f₂)` for distinct
`f₁, f₂ ∈ C`. -/
def GradientStrictMonotoneOn (J : H → ℝ) (C : Set H) : Prop :=
  ∀ ⦃f₁ f₂ : H⦄, f₁ ∈ C → f₂ ∈ C → f₁ ≠ f₂ →
    0 < inner ℝ (gradient J f₁ - gradient J f₂) (f₁ - f₂)

/-- Specification lemma for `GradientStrictMonotoneOn`. -/
theorem gradientStrictMonotoneOn_iff (J : H → ℝ) (C : Set H) :
    GradientStrictMonotoneOn J C ↔
      ∀ ⦃f₁ f₂ : H⦄, f₁ ∈ C → f₂ ∈ C → f₁ ≠ f₂ →
        0 < inner ℝ (gradient J f₁ - gradient J f₂) (f₁ - f₂) := by
  rfl
