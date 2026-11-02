import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_definition_6_2_1_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

-- This exercise reuses the Chapter 6 owner `Function.Subadditive` rather than restating the
-- pointwise inequality as separate primitive theorem hypotheses.

section Exercise69

variable {n : ℕ}

/-- Exercise 6.9 (1): if `g : ℝ^n → ℝ` is subadditive, then `g 0 ≥ 0`. -/
theorem exercise_6_9_subadditive_map_zero_nonneg
    (g : (Fin n → ℝ) → ℝ)
    (hg : g.Subadditive) :
    0 ≤ g 0 :=
  hg.map_zero_nonneg

/-- Exercise 6.9 (2): if `f, g : ℝ^n → ℝ` are subadditive, then their pointwise maximum, written
in Lean as `f ⊔ g`, is subadditive. -/
theorem exercise_6_9_max_subadditive
    (f g : (Fin n → ℝ) → ℝ)
    (hf : f.Subadditive)
    (hg : g.Subadditive) :
    (f ⊔ g).Subadditive := by
  simpa using hf.max hg

end Exercise69
