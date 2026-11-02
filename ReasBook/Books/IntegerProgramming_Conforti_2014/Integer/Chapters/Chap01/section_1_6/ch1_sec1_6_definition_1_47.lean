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
