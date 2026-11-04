/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_definition_1_11.Problem

public section

/- Definition 1.11 (1). A problem is formalized by the reusable owner `Problem`, together with the
constructor `Problem.ofAnswerFamily` and the answer-family view `Problem.answers`. -/
#check Problem
#check Problem.ofAnswerFamily
#check Problem.answers

/- Definition 1.11 (2). An instance of a problem is an admissible input, formalized by
`Problem.instanceOf`. -/
#check Problem.instanceOf
