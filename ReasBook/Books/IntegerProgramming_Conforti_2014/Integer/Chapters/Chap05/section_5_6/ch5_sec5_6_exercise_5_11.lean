/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Order.PiLex

/- Exercise 5.11. A faithful statement requires upstream owners for program `(5.27)`, its
full associated basic solution and independently defined lexicographically optimal bases, and
an output-bearing simplex computation with termination and correctness specifications. The
verified reusable APIs currently available without those upstream owners are finite
lexicographic order and the canonical greatest-element predicate checked below. -/
#check toLex
#check IsGreatest
