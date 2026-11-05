/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_19.YesSet

public section

/- Definition 1.19. A decision problem is specified by an instance type together with an
encoding-size function and a set of yes-instances; the source-facing yes-set presentation is the
canonical constructor `DecisionProblem.ofYesSet`, with the corresponding subset recovered by
`DecisionProblem.yesInstances`. -/
#check DecisionProblem.ofYesSet
