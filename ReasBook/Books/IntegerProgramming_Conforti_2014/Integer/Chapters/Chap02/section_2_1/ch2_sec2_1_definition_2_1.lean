/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_1.ch2_sec2_1_definition_2_1.KnapsackSet

public section

/-!
Definition 2.1.

The reusable owner for the integer knapsack set and its explicit membership criterion live in the
item-local foundation module imported above. This file remains the source-facing labeled surface
for the textbook definition, under the standing source context `n ≥ 1` and `∀ i, 0 < a i`.
-/

/- Definition 2.1: the integer knapsack set. -/
#check knapsackSet

/- Companion API: the explicit membership criterion for the integer knapsack set. -/
#check mem_knapsackSet_iff
