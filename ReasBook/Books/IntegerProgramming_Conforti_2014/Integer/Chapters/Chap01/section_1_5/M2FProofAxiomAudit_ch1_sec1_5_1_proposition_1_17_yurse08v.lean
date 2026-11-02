module

public import Mathlib.Data.Int.GCD

public section

namespace Int

/-- Helper for Proposition 1.17: a nonzero integer pair has a nonzero coordinate. -/
lemma left_ne_zero_or_right_ne_zero_of_pair_ne_zero {a b : ℤ}
    (h_nonzero : (a, b) ≠ (0, 0)) :
    a ≠ 0 ∨ b ≠ 0 := by
  -- Split on the left coordinate to reduce the pair contradiction to the right coordinate.
  by_cases ha : a = 0
  · right
    -- If the left coordinate vanishes, the right coordinate cannot also vanish.
    intro hb
    apply h_nonzero
    rw [ha, hb]
  · exact Or.inl ha

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_proposition_1_17.lean.
Proposition 1.17: for
integers `a` and `b` with `(a, b) ≠ (0, 0)`, the positive values of `a * x + b * y` form a set
of natural numbers with least element `Int.gcd a b`. This is the Lean rendering of the textbook
set `S := {a * x + b * y : x, y ∈ ℤ, a * x + b * y ≥ 1}`. -/
theorem gcd_isLeast_positiveLinearCombination
    (a b : ℤ)
    (h_nonzero : (a, b) ≠ (0, 0)) :
    IsLeast {n : ℕ | 0 < n ∧ ∃ x y : ℤ, (n : ℤ) = a * x + b * y} (Int.gcd a b) := by
  -- The pair hypothesis makes the gcd strictly positive.
  have h_coordinate : a ≠ 0 ∨ b ≠ 0 :=
    left_ne_zero_or_right_ne_zero_of_pair_ne_zero h_nonzero
  have h_gcd_pos : 0 < Int.gcd a b := Int.gcd_pos_iff.mpr h_coordinate
  -- Bézout's characterization turns represented values into multiples of the gcd.
  simp_rw [← Int.gcd_dvd_iff]
  constructor
  · exact ⟨h_gcd_pos, dvd_refl (Int.gcd a b)⟩
  · simp only [lowerBounds, Set.mem_setOf_eq, and_imp]
    exact fun n hn_pos hn_dvd ↦ Nat.le_of_dvd hn_pos hn_dvd

end Int

end

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_57ce6e930536059ee282"
#print axioms _root_.Int.gcd_isLeast_positiveLinearCombination
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_57ce6e930536059ee282"
