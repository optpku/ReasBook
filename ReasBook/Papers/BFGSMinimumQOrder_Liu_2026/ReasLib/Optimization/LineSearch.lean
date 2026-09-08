module

public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

universe u

namespace LineSearch

/-- Exact line search along `d` selects a feasible nonnegative step minimizing the
objective on that ray.  This is the BFGS project's pre-existing line-search API. -/
def IsExact {E : Type u} [AddCommGroup E] [Module ℝ E]
    (F : E → ℝ) (x d : E) (α : ℝ) : Prop :=
  0 ≤ α ∧ IsMinOn (fun t : ℝ ↦ F (x + t • d)) (Set.Ici 0) α

/-- The feasibility and minimizing properties defining an exact line search. -/
theorem isExact_iff {E : Type u} [AddCommGroup E] [Module ℝ E]
    (F : E → ℝ) (x d : E) (α : ℝ) :
    IsExact F x d α ↔
      0 ≤ α ∧ IsMinOn (fun t : ℝ ↦ F (x + t • d)) (Set.Ici 0) α := by
  rfl

/-- A step `s` from `x` satisfies the weak Wolfe conditions for `f` with
coefficients `c₁` and `c₂`. -/
structure IsWeakWolfe {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (c₁ c₂ : ℝ) (f : E → ℝ) (x s : E) : Prop where
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₂_lt_one : c₂ < 1
  differentiableAt : DifferentiableAt ℝ f x
  differentiableAtNext : DifferentiableAt ℝ f (x + s)
  armijo : f (x + s) ≤ f x + c₁ * inner ℝ (gradient f x) s
  weakCurvature : c₂ * inner ℝ (gradient f x) s ≤ inner ℝ (gradient f (x + s)) s

/-- A certified gradient computes the canonical gradient's pairing with any direction. -/
private lemma inner_gradient_eq_of_hasGradientAt {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : E → ℝ} {x g : E}
    (gradientAt : HasGradientAt f g x) (s : E) :
    inner ℝ (gradient f x) s = inner ℝ g s := by
  -- Replace the canonical gradient by the vector supplied by its certificate.
  rw [gradientAt.gradient]

/-- Certified endpoint gradients transport both weak Wolfe inequalities to canonical gradients. -/
private lemma canonicalWeakWolfeInequalities_of_hasGradientAt {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {c₁ c₂ : ℝ}
    {f : E → ℝ} {x s g gNext : E} (gradientAt : HasGradientAt f g x)
    (gradientAtNext : HasGradientAt f gNext (x + s))
    (armijo : f (x + s) ≤ f x + c₁ * inner ℝ g s)
    (weakCurvature : c₂ * inner ℝ g s ≤ inner ℝ gNext s) :
    f (x + s) ≤ f x + c₁ * inner ℝ (gradient f x) s ∧
      c₂ * inner ℝ (gradient f x) s ≤ inner ℝ (gradient f (x + s)) s := by
  constructor
  · -- Normalize the Armijo directional derivative at the initial point.
    simpa only [inner_gradient_eq_of_hasGradientAt gradientAt s] using armijo
  · -- Normalize both endpoint directional derivatives in the curvature inequality.
    simpa only [inner_gradient_eq_of_hasGradientAt gradientAt s,
      inner_gradient_eq_of_hasGradientAt gradientAtNext s] using weakCurvature

set_option linter.defProp false in
/-- Certified endpoint gradients and the two endpoint inequalities construct weak Wolfe
satisfaction. -/
def IsWeakWolfe.ofHasGradientAt {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {c₁ c₂ : ℝ} {f : E → ℝ}
    {x s g gNext : E} (c₁_pos : 0 < c₁) (c₁_lt_c₂ : c₁ < c₂) (c₂_lt_one : c₂ < 1)
    (gradientAt : HasGradientAt f g x) (gradientAtNext : HasGradientAt f gNext (x + s))
    (armijo : f (x + s) ≤ f x + c₁ * inner ℝ g s)
    (weakCurvature : c₂ * inner ℝ g s ≤ inner ℝ gNext s) :
    IsWeakWolfe c₁ c₂ f x s := by
  -- Transport both certified-gradient inequalities to the canonical gradients first.
  obtain ⟨canonicalArmijo, canonicalWeakCurvature⟩ :=
    canonicalWeakWolfeInequalities_of_hasGradientAt gradientAt gradientAtNext armijo weakCurvature
  -- Package the coefficient bounds, endpoint regularity, and transported inequalities.
  exact {
    c₁_pos := c₁_pos
    c₁_lt_c₂ := c₁_lt_c₂
    c₂_lt_one := c₂_lt_one
    differentiableAt := gradientAt.differentiableAt
    differentiableAtNext := gradientAtNext.differentiableAt
    armijo := canonicalArmijo
    weakCurvature := canonicalWeakCurvature
  }

/-- Weak Wolfe coefficients satisfy their three strict ordering bounds. -/
lemma IsWeakWolfe.coefficientBounds {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {c₁ c₂ : ℝ} {f : E → ℝ} {x s : E}
    (h : IsWeakWolfe c₁ c₂ f x s) : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1 := by
  -- Collect the coefficient fields into the standard right-associated conjunction.
  exact ⟨h.c₁_pos, h.c₁_lt_c₂, h.c₂_lt_one⟩

/-- Weak Wolfe satisfaction includes differentiability at both endpoints of the step. -/
lemma IsWeakWolfe.differentiableAtEndpoints {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {c₁ c₂ : ℝ} {f : E → ℝ} {x s : E}
    (h : IsWeakWolfe c₁ c₂ f x s) :
    DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ f (x + s) := by
  -- Pair the two endpoint regularity fields for conjunction-based consumers.
  exact ⟨h.differentiableAt, h.differentiableAtNext⟩

/-- Weak Wolfe satisfaction supplies the Armijo and weak-curvature inequalities. -/
lemma IsWeakWolfe.inequalities {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {c₁ c₂ : ℝ} {f : E → ℝ} {x s : E}
    (h : IsWeakWolfe c₁ c₂ f x s) :
    f (x + s) ≤ f x + c₁ * inner ℝ (gradient f x) s ∧
      c₂ * inner ℝ (gradient f x) s ≤ inner ℝ (gradient f (x + s)) s := by
  -- Pair the two endpoint inequalities without unfolding the Wolfe structure.
  exact ⟨h.armijo, h.weakCurvature⟩

/-- Along a descent step, weak curvature strictly increases the directional derivative. -/
lemma IsWeakWolfe.directionalDerivative_lt_next {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {c₁ c₂ : ℝ} {f : E → ℝ} {x s : E}
    (h : IsWeakWolfe c₁ c₂ f x s) (descent : inner ℝ (gradient f x) s < 0) :
    inner ℝ (gradient f x) s < inner ℝ (gradient f (x + s)) s := by
  -- Multiplication by the negative initial derivative reverses `c₂ < 1`.
  have scaledImprovement :
      inner ℝ (gradient f x) s < c₂ * inner ℝ (gradient f x) s := by
    simpa only [one_mul] using mul_lt_mul_of_neg_right h.c₂_lt_one descent
  -- The weak-curvature field carries this strict improvement to the next endpoint.
  exact scaledImprovement.trans_le h.weakCurvature

/-- Along a descent step, the gradient displacement has positive pairing with the step. -/
lemma IsWeakWolfe.secantCurvature_pos {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {c₁ c₂ : ℝ} {f : E → ℝ} {x s : E}
    (h : IsWeakWolfe c₁ c₂ f x s) (descent : inner ℝ (gradient f x) s < 0) :
    0 < inner ℝ (gradient f (x + s) - gradient f x) s := by
  -- Expand the gradient displacement and use the strict directional-derivative increase.
  rw [inner_sub_left]
  exact sub_pos.mpr (h.directionalDerivative_lt_next descent)

/-- Weak Wolfe satisfaction is equivalent to its coefficient, differentiability, Armijo,
and weak-curvature conditions. -/
theorem IsWeakWolfe.iff {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {c₁ c₂ : ℝ} {f : E → ℝ} {x s : E} :
    IsWeakWolfe c₁ c₂ f x s ↔
      0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1 ∧ DifferentiableAt ℝ f x ∧
        DifferentiableAt ℝ f (x + s) ∧
          f (x + s) ≤ f x + c₁ * inner ℝ (gradient f x) s ∧
            c₂ * inner ℝ (gradient f x) s ≤ inner ℝ (gradient f (x + s)) s := by
  constructor
  · intro h
    -- Project the seven defining fields into the right-associated conjunction.
    exact ⟨h.c₁_pos, h.c₁_lt_c₂, h.c₂_lt_one, h.differentiableAt,
      h.differentiableAtNext, h.armijo, h.weakCurvature⟩
  · rintro ⟨c₁_pos, c₁_lt_c₂, c₂_lt_one, differentiableAt,
      differentiableAtNext, armijo, weakCurvature⟩
    -- Reassemble the same seven conditions into weak Wolfe satisfaction.
    exact {
      c₁_pos := c₁_pos
      c₁_lt_c₂ := c₁_lt_c₂
      c₂_lt_one := c₂_lt_one
      differentiableAt := differentiableAt
      differentiableAtNext := differentiableAtNext
      armijo := armijo
      weakCurvature := weakCurvature
    }

/-- The coefficients `1 / 4` and `3 / 4` satisfy the strict bounds required for weak
Wolfe line search. -/
theorem IsWeakWolfe.selectedConstantsAdmissible :
    0 < (1 / 4 : ℝ) ∧ (1 / 4 : ℝ) < (3 / 4 : ℝ) ∧ (3 / 4 : ℝ) < 1 := by
  constructor
  · -- Normalize the positivity bound for the first coefficient.
    norm_num
  · constructor
    · -- Normalize the strict ordering of the two selected coefficients.
      norm_num
    · -- Normalize the upper bound for the second coefficient.
      norm_num

/-- Certified endpoint gradients and the two line-search inequalities establish weak
Wolfe satisfaction for the selected coefficients `1 / 4` and `3 / 4`. -/
theorem IsWeakWolfe.ofHasGradientAtSelectedConstants {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {f : E → ℝ}
    {x s g gNext : E} (gradientAt : HasGradientAt f g x)
    (gradientAtNext : HasGradientAt f gNext (x + s))
    (armijo : f (x + s) ≤ f x + (1 / 4 : ℝ) * inner ℝ g s)
    (weakCurvature : (3 / 4 : ℝ) * inner ℝ g s ≤ inner ℝ gNext s) :
    IsWeakWolfe (1 / 4) (3 / 4) f x s := by
  -- Supply the selected coefficient bounds to the generic certified-gradient constructor.
  exact ofHasGradientAt selectedConstantsAdmissible.1 selectedConstantsAdmissible.2.1
    selectedConstantsAdmissible.2.2 gradientAt gradientAtNext armijo weakCurvature

end LineSearch
