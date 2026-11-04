/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_20.NP

public section

/- Definition 1.20 [Complexity class `NP`].
   The complexity class `NP` is the class of all decision problems for which every "yes"
   instance admits a certificate verifiable in time polynomial in the encoding size of the
   instance. -/
#check DecisionProblem.inNP
