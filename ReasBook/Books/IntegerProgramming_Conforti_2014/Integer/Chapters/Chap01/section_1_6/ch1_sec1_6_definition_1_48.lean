/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.NumberTheory.PythagoreanTriples

public section

/- Definition 1.48 [Pythagorean triple]: a triple `(x, y, z) ∈ ℤ × ℤ × ℤ` is a
Pythagorean triple when `x * x + y * y = z * z`. This source notion is
formalized by the canonical mathlib predicate `PythagoreanTriple`, and its
equation-facing view is exposed by `PythagoreanTriple.eq`. -/

#check PythagoreanTriple
#check PythagoreanTriple.eq
