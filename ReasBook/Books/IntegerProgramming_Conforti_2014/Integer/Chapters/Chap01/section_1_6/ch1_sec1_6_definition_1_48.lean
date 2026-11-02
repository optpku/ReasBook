module

public import Mathlib.NumberTheory.PythagoreanTriples

public section

/- Definition 1.48 [Pythagorean triple]: a triple `(x, y, z) ∈ ℤ × ℤ × ℤ` is a
Pythagorean triple when `x * x + y * y = z * z`. This source notion is
formalized by the canonical mathlib predicate `PythagoreanTriple`, and its
equation-facing view is exposed by `PythagoreanTriple.eq`. -/

#check PythagoreanTriple
#check PythagoreanTriple.eq
