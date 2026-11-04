/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_corollary_3_23

-- Domain sampling for this exercise:
-- * primary domain: valid inequalities of mixed equality/inequality polyhedra
-- * source-facing owner: `mixed_constraint_polyhedron`
-- * core/canonical owner: `is_valid_inequality`
-- * supporting chapter theorem: `valid_inequality_iff_exists_mixed_row_multiplier`
-- * primitive data: the mixed system matrices/right-hand sides and the inequality coefficients
-- * derived API: `mem_mixed_constraint_polyhedron` and the theorem's direct multiplier system

/- Exercise 3.17. This exercise asks for a reproving of Corollary 3.23. The public mathematical
content is already owned by `valid_inequality_iff_exists_mixed_row_multiplier`, together with the
source-facing mixed-system owners from the corollary file, so this exercise should recall those
declarations rather than duplicate them locally. -/
recall mixed_constraint_polyhedron
recall mem_mixed_constraint_polyhedron
recall valid_inequality_iff_exists_mixed_row_multiplier
