module

public import Mathlib.Analysis.InnerProductSpace.Basic

public section

universe u

/-- The standard quadratic function on a real inner-product space. -/
noncomputable def standardQuadratic {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) : ℝ :=
  (1 / 2 : ℝ) * ‖x‖ ^ 2

/-- The standard quadratic function evaluates to half the squared norm. -/
theorem standardQuadratic_apply {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : E) :
    standardQuadratic x = (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
  -- Unfolding the definition makes both sides judgmentally equal.
  rfl

attribute [simp] standardQuadratic_apply
