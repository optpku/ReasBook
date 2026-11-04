/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_2.Problem

public section

/- Definition 1.2 (1). A mixed integer linear program is formalized by the reusable owner
`MixedIntegerLinearProgram`, with its canonical LP-relaxation and feasible-set views. -/
#check MixedIntegerLinearProgram
#check MixedIntegerLinearProgram.lpRelaxation
#check MixedIntegerLinearProgram.feasibleSet

/- The program-attached mixed-linear objective and its attained-value set are formalized by
`MixedIntegerLinearProgram.objectiveValue` and `MixedIntegerLinearProgram.objectiveValues`. -/
#check MixedIntegerLinearProgram.objectiveValue
#check MixedIntegerLinearProgram.objectiveValues

end
