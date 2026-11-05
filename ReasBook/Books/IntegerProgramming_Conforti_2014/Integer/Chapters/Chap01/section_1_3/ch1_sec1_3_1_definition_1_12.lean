/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs

public section

open scoped BigOperators

namespace EncodingSize

/-- Definition 1.12 (1): the encoding size of an integer `z` is `Nat.size z.natAbs + 1`, i.e. the
binary length of `|z|` together with one sign bit. -/
def integer (z : ℤ) : ℕ :=
  Nat.size z.natAbs + 1

/-- The defining equation for `EncodingSize.integer`. -/
@[simp] theorem integer_eq (z : ℤ) :
    integer z = Nat.size z.natAbs + 1 :=
  by simp [integer]

/-- Definition 1.12 (2): the encoding size of a rational number `q` is the sum of one sign bit,
the binary length of `q.num.natAbs`, and the binary length of the positive denominator `q.den`. -/
def rational (q : ℚ) : ℕ :=
  Nat.size q.num.natAbs + Nat.size q.den + 1

/-- The defining equation for `EncodingSize.rational`. -/
@[simp] theorem rational_eq (q : ℚ) :
    rational q = Nat.size q.num.natAbs + Nat.size q.den + 1 :=
  by simp [rational]

/-- The entrywise sum of integer encoding sizes on a finite integer vector. -/
def integerVector {n : ℕ} (v : Fin n → ℤ) : ℕ :=
  ∑ i : Fin n, integer (v i)

/-- The defining sum formula for `EncodingSize.integerVector`. -/
@[simp] theorem integerVector_eq_sum {n : ℕ} (v : Fin n → ℤ) :
    integerVector v = ∑ i : Fin n, integer (v i) :=
  by simp [integerVector]

/-- Definition 1.12 (3): the encoding size of a rational vector is the sum of the encoding sizes
of its entries. -/
def rationalVector {n : ℕ} (v : Fin n → ℚ) : ℕ :=
  ∑ i : Fin n, rational (v i)

/-- The defining sum formula for `EncodingSize.rationalVector`. -/
@[simp] theorem rationalVector_eq_sum {n : ℕ} (v : Fin n → ℚ) :
    rationalVector v = ∑ i : Fin n, rational (v i) :=
  by simp [rationalVector]

/-- Definition 1.12 (4): the encoding size of a rational matrix is the sum of the encoding sizes
of its entries. -/
def rationalMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  ∑ i : Fin m, rationalVector (A i)

/-- The defining row-wise sum formula for `EncodingSize.rationalMatrix`. -/
@[simp] theorem rationalMatrix_eq_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    rationalMatrix A = ∑ i : Fin m, rationalVector (A i) :=
  by simp [rationalMatrix]

/-- Expanding `EncodingSize.rationalMatrix` all the way gives the sum of the encoding sizes of
its individual entries. -/
theorem rationalMatrix_eq_sum_entries {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    rationalMatrix A = ∑ i : Fin m, ∑ j : Fin n, rational (A i j) := by
  simp [rationalMatrix, rationalVector]

end EncodingSize
