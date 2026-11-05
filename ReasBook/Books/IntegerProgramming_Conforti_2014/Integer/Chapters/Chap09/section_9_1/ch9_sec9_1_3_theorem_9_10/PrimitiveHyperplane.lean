/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Algebra.GCDMonoid.Finset
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_theorem_2_3.LinearFunctional

section Theorem910PrimitiveHyperplane

variable {n : ℕ}

/-- An integral vector is primitive if it is nonzero and the gcd of the absolute values of its
coordinates is `1`. -/
def is_primitive_integer_vector (v : Fin n → ℤ) : Prop :=
  v ≠ 0 ∧ Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (v i)) = 1

/-- `is_primitive_integer_vector v` means that `v` is nonzero and its coordinates are relatively
prime. -/
theorem is_primitive_integer_vector_iff
    (v : Fin n → ℤ) :
    is_primitive_integer_vector v ↔
      v ≠ 0 ∧ Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (v i)) = 1 :=
  Iff.rfl

/-- The affine hyperplane cut out by the integral equation `v^T x = rhs`, viewed through the
Chapter 2 owner `linear_hyperplane`. -/
abbrev integer_hyperplane
    (v : Fin n → ℤ)
    (rhs : ℚ) : Set (Fin n → ℝ) :=
  linear_hyperplane (Int.cast ∘ v) (rhs : ℝ)

end Theorem910PrimitiveHyperplane
