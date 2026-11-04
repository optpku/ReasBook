/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_4.ch3_sec3_4_4_definition_3_4_4_extra_1

open scoped Pointwise

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition 3.5.2-extra-2. The finitely generated cone spanned by the rays `rays`, viewed
through the earlier Chapter 3 owner `cone`. -/
abbrev finitely_generated_cone {n q : ℕ} (rays : Fin q → Fin n → ℝ) : Set (Fin n → ℝ) :=
  cone (Set.range rays)
