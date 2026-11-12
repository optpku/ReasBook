/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.NumberTheory.PythagoreanTriples

public section

namespace PythagoreanTriple

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_proposition_1_24.lean.
Proposition 1.24 (Parametrization of Pythagorean triples): for integers `k`, `m`, and `n`,
`(k * (m ^ 2 - n ^ 2), k * (2 * m * n), k * (m ^ 2 + n ^ 2))` is a Pythagorean triple. -/
theorem parametrization (k m n : ℤ) :
    PythagoreanTriple (k * (m ^ 2 - n ^ 2)) (k * (2 * m * n)) (k * (m ^ 2 + n ^ 2)) := by
  -- Reduce the predicate to its quadratic equation, then normalize the polynomial identity.
  delta PythagoreanTriple
  ring

end PythagoreanTriple

end
