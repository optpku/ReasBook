/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.RingTheory.Int.Basic

public section

/-
Lemma 1.4
Let `p` be a prime number and let `a b ∈ ℤ`. If `(p : ℤ) ∣ a * b`, then
`(p : ℤ) ∣ a` or `(p : ℤ) ∣ b`.
-/
#check Int.Prime.dvd_mul'
