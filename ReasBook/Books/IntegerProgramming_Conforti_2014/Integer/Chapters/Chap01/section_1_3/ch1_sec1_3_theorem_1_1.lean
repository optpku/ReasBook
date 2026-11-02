module

public import Mathlib.Data.Nat.Digits.Lemmas

public section

/-- Theorem 1.1 (1): every natural number admits a base-`2` digit expansion with digits less than
`2`. -/
theorem binaryExpansionExists (n : ℕ) :
    ∃ L : List ℕ, Nat.ofDigits 2 L = n ∧ ∀ d ∈ L, d < 2 := by
  refine ⟨Nat.digits 2 n, Nat.ofDigits_digits 2 n, ?_⟩
  intro d hd
  exact Nat.digits_lt_base (by decide) hd

/-- The canonical binary digit list of `n` represents `n`, uses only digits less than `2`, and is
normalized by a nonzero last digit whenever it is nonempty. -/
theorem binaryDigits_spec (n : ℕ) :
    Nat.ofDigits 2 (Nat.digits 2 n) = n ∧
      (∀ d ∈ Nat.digits 2 n, d < 2) ∧
      ∀ h : Nat.digits 2 n ≠ [], (Nat.digits 2 n).getLast h ≠ 0 := by
  refine ⟨Nat.ofDigits_digits 2 n, ?_, ?_⟩
  · intro d hd
    exact Nat.digits_lt_base (by decide) hd
  · intro h
    simpa using Nat.getLast_digit_ne_zero 2 (Nat.digits_ne_nil_iff_ne_zero.mp h)

/-- The canonical binary digit list of `n` expands to the textbook finite sum `∑ b_i 2^i`. -/
theorem binaryExpansionEqSumPow (n : ℕ) :
    n = ((Nat.digits 2 n).mapIdx fun i d ↦ d * 2 ^ i).sum := by
  calc
    n = Nat.ofDigits 2 (Nat.digits 2 n) := by symm; exact Nat.ofDigits_digits 2 n
    _ = ((Nat.digits 2 n).mapIdx fun i d ↦ d * 2 ^ i).sum :=
      Nat.ofDigits_eq_sum_mapIdx 2 (Nat.digits 2 n)

/-- A normalized base-`2` digit list representing `n` is the canonical list `Nat.digits 2 n`. -/
theorem binaryExpansion_eq_digits {n : ℕ} {L : List ℕ}
    (hL : Nat.ofDigits 2 L = n) (hdigits : ∀ d ∈ L, d < 2)
    (hnorm : ∀ h : L ≠ [], L.getLast h ≠ 0) :
    L = Nat.digits 2 n := by
  simpa [hL] using (Nat.digits_ofDigits 2 (by decide) L hdigits hnorm).symm

/-- Theorem 1.1 (2): a normalized base-`2` digit list representing `n` is uniquely the canonical
list `Nat.digits 2 n`. -/
theorem binaryExpansionUnique {n : ℕ} {L : List ℕ} :
    (Nat.ofDigits 2 L = n ∧ (∀ d ∈ L, d < 2) ∧ ∀ h : L ≠ [], L.getLast h ≠ 0) ↔
      L = Nat.digits 2 n := by
  constructor
  · rintro ⟨hL, hdigits, hlast⟩
    exact binaryExpansion_eq_digits hL hdigits hlast
  · rintro rfl
    exact binaryDigits_spec n

/-- Theorem 1.1 (3): for `n ≥ 1`, the highest binary exponent is `Nat.log2 n`, giving the usual
two-sided power bound. -/
theorem binaryExpansionBounds {n : ℕ} (hn : 1 ≤ n) :
    2 ^ Nat.log2 n ≤ n ∧ n < 2 ^ (Nat.log2 n + 1) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hn)
  constructor
  · simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hn0
  · simpa [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self Nat.one_lt_two n
