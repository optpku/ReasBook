/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_18

/- Definition 6.2-extra-1. The source notion of a lattice-free set in `ℝ^p` is the chapter's
canonical predicate `is_lattice_free`. -/
#check is_lattice_free

/- The source wording "the interior contains no embedded integer point" is already the canonical
specification theorem for `is_lattice_free`. -/
#check is_lattice_free_iff
