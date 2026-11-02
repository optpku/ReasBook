module

public import Mathlib.RingTheory.Int.Basic

public section

/-
Lemma 1.4
Let `p` be a prime number and let `a b ∈ ℤ`. If `(p : ℤ) ∣ a * b`, then
`(p : ℤ) ∣ a` or `(p : ℤ) ∣ b`.
-/
#check Int.Prime.dvd_mul'
