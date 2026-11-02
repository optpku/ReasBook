module

public import Mathlib.Data.Int.Basic

public section

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_22.lean:
the quotient and remainder of `4 * n` modulo `7` give nonnegative coefficients
for the generators `7` and `9`, except at the exceptional value `47`. -/
lemma sevenNineResidueWitness_spec {n : ℤ} (hn : 40 < n) (hne : n ≠ 47) :
    0 ≤ 9 * ((4 * n) / 7) - 5 * n ∧
      0 ≤ (4 * n) % 7 ∧
        n = 7 * (9 * ((4 * n) / 7) - 5 * n) + 9 * ((4 * n) % 7) := by
  -- Separate coefficient nonnegativity from the representation identity.
  constructor
  · by_cases hr : (4 * n) % 7 = 6
    · omega
    · omega
  · constructor
    · omega
    · omega

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_22.lean:
every integer greater than `40`, other than `47`, is a nonnegative combination
of `7` and `9`. -/
lemma exists_nonneg_seven_nine_decomposition_of_gt_forty_of_ne {n : ℤ}
    (hn : 40 < n) (hne : n ≠ 47) :
    ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ n = 7 * a + 9 * b := by
  -- Package the quotient and remainder coordinates as the required witnesses.
  obtain ⟨ha, hb, hab⟩ := sevenNineResidueWitness_spec hn hne
  exact ⟨9 * ((4 * n) / 7) - 5 * n, (4 * n) % 7, ha, hb, hab⟩

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_22.lean.
Theorem 1.22. If an integer `n` satisfies `40 < n` and there do not exist integers
`a, b ≥ 0` with `n = 7 * a + 9 * b`, then `n = 47`. -/
theorem eq_41_of_gt_40_and_not_exists_nonneg_seven_nine_decomposition
    {n : ℤ} (hn : 40 < n)
    (hdecomp : ¬ ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ n = 7 * a + 9 * b) :
    n = 47 := by
  -- Any value other than 47 has the decomposition, contradicting its negation.
  by_contra hne
  exact hdecomp (exists_nonneg_seven_nine_decomposition_of_gt_forty_of_ne hn hne)
