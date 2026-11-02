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
