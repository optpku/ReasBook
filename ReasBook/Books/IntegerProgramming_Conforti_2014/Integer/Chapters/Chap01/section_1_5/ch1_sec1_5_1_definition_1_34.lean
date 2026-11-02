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
