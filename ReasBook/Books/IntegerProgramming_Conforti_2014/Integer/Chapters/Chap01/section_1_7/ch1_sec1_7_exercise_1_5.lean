import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was not available in this environment; this item uses
-- a direct stopping-rule predicate and a companion approximation guarantee.

/-- Exercise 1.5. A `p%`-approximate Step 4 for branch-and-bound may stop once the incumbent
objective value `zBar` is at least `(1 - p / 100)` times the current global upper bound on the
optimal value. -/
def branch_and_bound_relative_gap_step (p zBar upperBound : ℝ) : Prop :=
  (1 - p / 100) * upperBound ≤ zBar

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_5.lean.
If the current branch-and-bound upper bound dominates the positive optimum value, then the
relative-gap stopping rule certifies that the incumbent value is within `p%` of optimal. -/
theorem branch_and_bound_relative_gap_step_spec
    {p zBar zStar upperBound : ℝ}
    (hp_nonneg : 0 ≤ p)
    (hp_le_hundred : p ≤ 100)
    (hzStar_pos : 0 < zStar)
    (hupper : zStar ≤ upperBound)
    (hstep : branch_and_bound_relative_gap_step p zBar upperBound) :
    zBar / zStar ≥ 1 - p / 100 := by
  -- Expose the stopping rule in the multiplicative form used by the order argument.
  have hstep_expanded : (1 - p / 100) * upperBound ≤ zBar := by
    simpa only [branch_and_bound_relative_gap_step] using hstep
  -- Package the percentage assumptions as the advertised range before using its upper endpoint.
  have hp_range : p ∈ Set.Icc (0 : ℝ) 100 := ⟨hp_nonneg, hp_le_hundred⟩
  -- The percentage bound makes the approximation factor nonnegative.
  have hfactor_nonneg : 0 ≤ 1 - p / 100 := by
    linarith [hp_range.2]
  -- Scale the optimum-to-upper-bound comparison and compose it with the stopping certificate.
  have hscaled : (1 - p / 100) * zStar ≤ (1 - p / 100) * upperBound :=
    mul_le_mul_of_nonneg_left hupper hfactor_nonneg
  have hproduct : (1 - p / 100) * zStar ≤ zBar :=
    hscaled.trans hstep_expanded
  -- Positivity of the optimum permits division without reversing the inequality.
  exact (le_div_iff₀ hzStar_pos).2 hproduct

#print axioms branch_and_bound_relative_gap_step_spec
