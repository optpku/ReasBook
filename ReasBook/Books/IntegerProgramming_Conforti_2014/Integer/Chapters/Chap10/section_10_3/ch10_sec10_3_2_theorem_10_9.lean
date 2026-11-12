/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4.ch5_sec5_4_definition_5_4_extra_1

/- Theorem 10.9. This Chapter 10 item is a `bridge/view` recall, not a new owner declaration:
the textbook identity for the coordinate lift-and-project set `P_j` is already the canonical
Chapter 5 theorem `coordinate_lift_project_hull_def` for the owner
`coordinate_lift_project_hull`. This file therefore recalls that owner theorem directly instead
of duplicating a parallel local statement. -/
recall coordinate_lift_project_hull_def
