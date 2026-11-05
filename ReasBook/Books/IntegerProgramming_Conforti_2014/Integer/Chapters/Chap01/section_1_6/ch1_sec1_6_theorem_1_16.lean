/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.RingTheory.Int.Basic

public section

/-- Theorem 1.16: for integers `a`, `b`, `c`, the Diophantine equation `a * x + b * y = c` has
an integer solution if and only if `(Int.gcd a b : ℤ)` divides `c`. -/
theorem existsMulAddMulEq_iff_intGcdDvd (a b c : ℤ) :
    (∃ x y : ℤ, a * x + b * y = c) ↔ ((Int.gcd a b : ℤ) ∣ c) := by
  simpa [Int.coe_gcd, eq_comm] using
    ((gcd_dvd_iff_exists a b : gcd a b ∣ c ↔ ∃ x y, c = a * x + b * y)).symm
