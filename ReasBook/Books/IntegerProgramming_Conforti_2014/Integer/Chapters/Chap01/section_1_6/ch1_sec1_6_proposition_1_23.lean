/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.RingTheory.Int.Basic

public section

namespace Int

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_proposition_1_23.lean.
Proposition 1.23: if `n` is an integer with `1 < n`, then there exists a prime integer `p`
such that `p ∣ n`. -/
theorem exists_prime_and_dvd_of_one_lt (n : ℤ) (hn : 1 < n) :
    ∃ p : ℤ, Prime p ∧ p ∣ n := by
  -- Bounding `n` by its absolute value transfers the strict lower bound to `n.natAbs`.
  have hAbs : (1 : ℤ) < |n| := lt_of_lt_of_le hn (le_abs_self n)
  have hNatAbsGtOne : 1 < n.natAbs := by
    rwa [Int.abs_eq_natAbs, Nat.one_lt_cast] at hAbs
  -- Thus `n` is not a unit, so the canonical integer prime-divisor theorem applies.
  exact Int.exists_prime_and_dvd (Nat.ne_of_gt hNatAbsGtOne)

end Int

end
