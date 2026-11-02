module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_definition_1_7.Optimality

public section

/- Definition 1.7.

The source-facing optimality notions for a mixed-integer linear program `P` and
its LP relaxation are carried by the canonical Chapter 1 owner
`MixedIntegerLinearProgram`; the reusable support API lives in
`ch1_sec1_2_definition_1_7.Optimality`.
-/
#check MixedIntegerLinearProgram.isOptimalSolution
#check MixedIntegerLinearProgram.hasOptimalSolution
#check MixedIntegerLinearProgram.isLpRelaxationOptimalSolution
#check MixedIntegerLinearProgram.lpRelaxationHasOptimalSolution

end
