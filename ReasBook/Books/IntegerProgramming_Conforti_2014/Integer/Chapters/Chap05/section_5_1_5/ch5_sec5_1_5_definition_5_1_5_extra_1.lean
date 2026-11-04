/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_5.ch5_sec5_1_5_theorem_5_12

/- Definition 5.1.5-extra-1 is a `source-facing` recall, not a second MIR owner:
the Chapter 5 canonical owner file
`ch5_sec5_1_5_theorem_5_12.lean`
already defines the mixed integer rounding inequality predicate, the mixed integer rounding
closure, and the corresponding membership theorem. This file therefore recalls those canonical
declarations directly instead of keeping a duplicate local API. -/
recall is_mixed_integer_rounding_inequality
recall mixed_integer_rounding_closure
recall mem_mixed_integer_rounding_closure_iff
