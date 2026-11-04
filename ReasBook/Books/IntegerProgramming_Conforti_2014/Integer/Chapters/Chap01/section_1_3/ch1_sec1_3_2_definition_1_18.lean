/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_2_definition_1_18.ClassP

public section

/- Definition 1.18 [Complexity class `P`].
   A decision problem belongs to the complexity class `P` exactly when, relative to the chosen
   finite encoding of its instances, it admits a deterministic TM2 decider running in time
   polynomial in the declared encoding size. The canonical owner is `DecisionProblem.inP`; the
   item-owned `ClassP` API provides both the lower-level TM2 witness expansion
   `DecisionProblem.inP_iff_exists_tm2Decider` and the source-facing bridge
   `DecisionProblem.inP_iff_exists_polynomialTimeMap`. -/
#check DecisionProblem.inP
