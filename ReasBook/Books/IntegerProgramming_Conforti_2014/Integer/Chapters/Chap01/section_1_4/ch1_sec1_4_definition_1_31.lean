/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1.Integral

/-
Definition 1.31 [Integral polyhedron]. The source notion is formalized by the
canonical owner `is_integral` for subsets of `ℝ^n`; its defining convex-hull
specification is exposed by `is_integral_iff`, while the source's linear-maxima
view belongs to later bridge theorems for rational polyhedra.
-/

#check is_integral
#check is_integral_iff
