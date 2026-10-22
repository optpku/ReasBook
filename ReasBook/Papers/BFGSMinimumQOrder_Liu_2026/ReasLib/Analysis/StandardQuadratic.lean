/-
Authors: Chenyi Li
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/BFGSMinimumQOrder_Liu_2026/README.md (formalization contributor).
-/

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
