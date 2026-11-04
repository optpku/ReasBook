/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_62.ZeroOneSet

/-!
`0`--`1` sets.

This item is formalized by the reusable owner `zeroOneSet`, together with its membership API and
the canonical bridge to Chapter 1 mixed `0,1` linear sets.
-/

/- Definition 2.62: for `A : Matrix (Fin m) (Fin n) ℝ` and `b : Fin m → ℝ`, a `0`--`1` set is a
set of the form `zeroOneSet A b = {x | is_zero_one_vector x ∧ A.mulVec x ≤ b}`. -/
#check zeroOneSet
#check mem_zeroOneSet_iff
#check mem_zeroOneSet_iff_mem_mixedZeroOneLinearSet
