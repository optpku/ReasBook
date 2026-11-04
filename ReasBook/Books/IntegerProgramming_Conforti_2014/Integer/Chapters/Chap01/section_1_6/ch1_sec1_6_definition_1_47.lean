/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.NumberTheory.Divisors

public section

/- Definition 1.47: An integer `n ≥ 1` is called perfect if it equals the sum
of all positive divisors of `n` that are strictly less than `n`. This source
notion is formalized by the canonical mathlib predicate `Nat.Perfect`, and its
displayed divisor-sum characterization is exposed by
`Nat.perfect_iff_sum_properDivisors`. -/

#check Nat.Perfect
#check Nat.perfect_iff_sum_properDivisors
