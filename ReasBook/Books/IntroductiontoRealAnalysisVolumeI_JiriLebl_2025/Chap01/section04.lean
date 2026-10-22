/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap01
section Section04

/-- Proposition 1.4.1: A set `I ⊆ ℝ` is an interval if and only if it contains at
least two points and, whenever `a, c ∈ I` and `a < b < c`, the point `b` also belongs
to `I`. -/
theorem interval_real_iff_two_points_and_between (I : Set ℝ) :
    (Set.OrdConnected I ∧ ∃ a c, a ≠ c ∧ a ∈ I ∧ c ∈ I) ↔
      (∃ a c, a ≠ c ∧ a ∈ I ∧ c ∈ I) ∧
        (∀ {a c b}, a ∈ I → c ∈ I → a < b → b < c → b ∈ I) := by
  constructor
  · rintro ⟨hconn, hex⟩
    refine ⟨hex, ?_⟩
    intro a c b ha hc hab hbc
    have hmem : b ∈ Set.Icc a c := ⟨le_of_lt hab, le_of_lt hbc⟩
    exact hconn.out ha hc hmem
  · rintro ⟨hex, hbetween⟩
    refine ⟨?_, hex⟩
    refine ⟨?_⟩
    intro a ha c hc b hb
    rcases lt_or_eq_of_le hb.1 with hlt | rfl
    · rcases lt_or_eq_of_le hb.2 with hlt' | rfl
      · exact hbetween ha hc hlt hlt'
      · simpa using hc
    · simpa using ha

/-- Theorem 1.4.2 (Cantor): The set of real numbers `ℝ` is uncountable. -/
theorem cantor_real_uncountable : Uncountable ℝ := by
  -- This follows directly from the standard cardinality computation of `ℝ`.
  simpa using (Cardinal.instUncountableReal : Uncountable ℝ)

end Section04
end Chap01
