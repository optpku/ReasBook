import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_definition_6_2_1_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

-- This exercise reuses the Chapter 6 owner `Function.Subadditive`.

section Exercise68

/-- Exercise 6.8 (1). The ceiling function `g(x) = ⌈x⌉`, coerced to `ℝ`, is subadditive. -/
theorem exercise_6_8_ceil_subadditive :
    (fun x : ℝ ↦ (⌈x⌉ : ℝ)).Subadditive := by
  -- The real-valued claim is exactly the cast of the standard integer ceiling inequality.
  intro x y
  change ((⌈x + y⌉ : ℤ) : ℝ) ≤ ((⌈x⌉ : ℤ) : ℝ) + ((⌈y⌉ : ℤ) : ℝ)
  exact_mod_cast Int.ceil_add_le x y

/-- Exercise 6.8 (2). For a given positive integer period `t`, the remainder function
`g(x) = x mod t`, written explicitly as `Int.fract (x / t) * t`, is subadditive. -/
theorem exercise_6_8_mod_positive_integer_subadditive
    {t : ℤ} (ht : 0 < t) :
    (fun x : ℝ ↦ Int.fract (x / (t : ℝ)) * (t : ℝ)).Subadditive := by
  -- The source proof route is to apply subadditivity of the fractional part after scaling by `t`.
  intro x y
  have hfract := Int.fract_add_le (x / (t : ℝ)) (y / (t : ℝ))
  -- Positivity of the integer period gives the nonnegativity needed to preserve the inequality.
  have ht0 : 0 ≤ (t : ℝ) := by
    exact_mod_cast ht.le
  have hmul := mul_le_mul_of_nonneg_right hfract ht0
  simpa [add_div, add_mul] using hmul

end Exercise68
