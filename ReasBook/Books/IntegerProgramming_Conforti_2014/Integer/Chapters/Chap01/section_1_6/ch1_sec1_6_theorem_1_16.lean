module

public import Mathlib.RingTheory.Int.Basic

public section

/-- Theorem 1.16: for integers `a`, `b`, `c`, the Diophantine equation `a * x + b * y = c` has
an integer solution if and only if `(Int.gcd a b : ℤ)` divides `c`. -/
theorem existsMulAddMulEq_iff_intGcdDvd (a b c : ℤ) :
    (∃ x y : ℤ, a * x + b * y = c) ↔ ((Int.gcd a b : ℤ) ∣ c) := by
  simpa [Int.coe_gcd, eq_comm] using
    ((gcd_dvd_iff_exists a b : gcd a b ∣ c ↔ ∃ x y, c = a * x + b * y)).symm
