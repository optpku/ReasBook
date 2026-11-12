/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.RingTheory.Int.Basic

public section

namespace IntFamily

/-- Definition 1.36 (1): for a
finite integer family `a : Fin n → ℤ`, `gcd a` is the gcd of the absolute values of its coordinates,
viewed as a positive integer when `a ≠ 0`. -/
def gcd {n : ℕ} (a : Fin n → ℤ) : ℕ :=
  Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (a i))

/-- Definition 1.36 (2): the integers in a finite family `a : Fin n → ℤ` are relatively prime
when `gcd a = 1`. -/
def relativelyPrime {n : ℕ} (a : Fin n → ℤ) : Prop :=
  gcd a = 1

/-- The gcd of an integer family divides each coordinate. -/
theorem gcd_dvd {n : ℕ} (a : Fin n → ℤ) (i : Fin n) :
    ((gcd a : ℕ) : ℤ) ∣ a i := by
  -- Transport the coordinate divisibility supplied by `Finset.gcd_dvd` back to `ℤ`.
  rw [Int.natCast_dvd, gcd]
  exact Finset.gcd_dvd (Finset.mem_univ i)

/-- Any natural number dividing every coordinate of an integer family divides its gcd. -/
theorem dvd_gcd {n : ℕ} (a : Fin n → ℤ) {d : ℕ}
    (hd : ∀ i : Fin n, (d : ℤ) ∣ a i) :
    d ∣ gcd a := by
  -- Convert every integer divisibility hypothesis to one on natural absolute values.
  rw [gcd]
  apply Finset.dvd_gcd
  intro i _
  exact Int.natCast_dvd.mp (hd i)

/-- The gcd of an integer family vanishes exactly for the zero family. -/
theorem gcd_eq_zero_iff {n : ℕ} (a : Fin n → ℤ) :
    gcd a = 0 ↔ a = 0 := by
  -- Reduce vanishing of the finite gcd to vanishing of every absolute value.
  rw [gcd, Finset.gcd_eq_zero_iff]
  constructor
  · intro h
    -- Pointwise vanishing identifies the whole family with the zero function.
    funext i
    exact Int.natAbs_eq_zero.mp (h i (Finset.mem_univ i))
  · intro h i _
    -- A zero family has zero absolute value in every coordinate.
    rw [h]
    exact Int.natAbs_zero

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_definition_1_36.lean.
If `a ≠ 0`, then `gcd a` is a positive common divisor that is maximal among positive common divisors
of the coordinates of `a`. -/
theorem gcd_spec {n : ℕ} (a : Fin n → ℤ) (ha : a ≠ 0) :
    0 < gcd a ∧
      (∀ i : Fin n, ((gcd a : ℕ) : ℤ) ∣ a i) ∧
      ∀ d : ℕ, 0 < d → (∀ i : Fin n, (d : ℤ) ∣ a i) → d ≤ gcd a := by
  -- Nonvanishing of the family makes its natural gcd positive.
  have hgcd_ne : gcd a ≠ 0 := fun hgcd ↦ ha ((gcd_eq_zero_iff a).mp hgcd)
  have hgcd_pos : 0 < gcd a := Nat.pos_of_ne_zero hgcd_ne
  -- Assemble positivity and coordinate divisibility from the companion lemmas.
  refine ⟨hgcd_pos, gcd_dvd a, ?_⟩
  intro d _ hd
  -- A natural common divisor is bounded by the positive gcd.
  exact Nat.le_of_dvd hgcd_pos (dvd_gcd a hd)

/-- Relative primality is exactly the condition that the family gcd is `1`. -/
theorem relativelyPrime_iff {n : ℕ} (a : Fin n → ℤ) :
    relativelyPrime a ↔ gcd a = 1 := by
  -- This equivalence is the defining condition for relative primality.
  rfl

end IntFamily

end
