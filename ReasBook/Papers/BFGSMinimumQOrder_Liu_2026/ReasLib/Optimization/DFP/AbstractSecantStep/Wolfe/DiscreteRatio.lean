module

public import ReasLib.Optimization.DFP.AbstractSecantStep.Wolfe

public section

/-!
# Discrete line-ratio curvature certificates

The exact two-phase construction uses only the two ratios `1 / 3` and `2 / 3`.  This module
records the resulting strong-curvature certificate at the abstract secant-step level, leaving the
coefficient `c₂` symbolic so that it can be reused by any line-search argument with
`2 / 3 ≤ c₂`.
-/

namespace DFP.AbstractSecantStep

universe u

/-- A secant step whose line ratio is `1 / 3` or `2 / 3` satisfies strong curvature for every
coefficient at least `2 / 3`. -/
theorem strongCurvature_of_tau_values {n : Type u} [Fintype n]
    (z : AbstractSecantStep n) {c₂ : ℝ}
    (hτ : z.tau = 2 / 3 ∨ z.tau = 1 / 3) (hc₂ : (2 / 3 : ℝ) ≤ c₂) :
    LineSearch.Wolfe.IsStrongCurvature c₂ z.slope z.nextSlope := by
  apply z.strongCurvature
  rcases hτ with hτ | hτ
  · rw [hτ]
    norm_num [abs_of_nonneg]
    linarith
  · rw [hτ]
    norm_num [abs_of_nonneg]
    exact hc₂

end DFP.AbstractSecantStep
