/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_2.ch2_sec2_2_definition_2_4.KnapsackSet
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_2.ch2_sec2_2_definition_2_4.Cover
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_2.ch2_sec2_2_definition_2_4.Closure

public section

/-!
Definition 2.4.

The reusable owners for the `0`--`1` knapsack set, cover notions, and cover-inequality closure live
in the item-local foundation modules imported above. This file remains the source-facing labeled
surface for the four textbook notions.
-/

/- Definition 2.4 (1): the `0`--`1` knapsack set. -/
#check zero_one_knapsack_set

/- Definition 2.4 (2): a cover for the knapsack set. -/
#check IsKnapsackCover

/- Definition 2.4 (3): a minimal cover for the knapsack set. -/
#check IsMinimalKnapsackCover

/- Definition 2.4 (4): the cover-inequality closure. -/
#check cover_inequality_closure
