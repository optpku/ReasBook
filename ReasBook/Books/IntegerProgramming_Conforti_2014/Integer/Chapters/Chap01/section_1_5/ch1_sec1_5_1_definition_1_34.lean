/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Int.GCD

public section

/- Definition 1.34 [Greatest common divisor]. For integers `a`, `b` with
`(a, b) ≠ (0, 0)`, the source definition is formalized by the canonical owner
`Int.gcd : ℤ → ℤ → ℕ`. Its greatest-common-divisor characterization is exposed
by `Int.gcd_greatest`, and its common-divisor clauses are exposed by
`Int.gcd_dvd_left` and `Int.gcd_dvd_right`. -/

#check Int.gcd
#check Int.gcd_greatest
#check Int.gcd_dvd_left
#check Int.gcd_dvd_right

end
