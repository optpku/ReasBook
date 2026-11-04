/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_6

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling for this exercise:
-- * primary domain: finite linear inequality/equality systems and Farkas-type multiplier
--   certificates
-- * source-facing chapter owner:
--   `mixed_linear_system_feasible_iff_nonnegative_multiplier_evaluation`
-- * supporting canonical theorem: `farkas_lemma_linear_inequalities`
-- * primitive data: the matrices `A`, `B`, `C`, `D` and right-hand sides `f`, `g`
-- * derived API: the multiplier-side nonnegativity, annihilation, and evaluation conditions

/- Exercise 3.1. This exercise asks for a reproving of Theorem 3.6 via Farkas' Lemma. The public
mathematical content is already the chapter owner theorem
`mixed_linear_system_feasible_iff_nonnegative_multiplier_evaluation`; the Farkas-based proof route
is internal supporting provenance, not a second public theorem with a duplicate interface. -/
recall mixed_linear_system_feasible_iff_nonnegative_multiplier_evaluation
