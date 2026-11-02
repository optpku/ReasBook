module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_19.YesSet

public section

/- Definition 1.19. A decision problem is specified by an instance type together with an
encoding-size function and a set of yes-instances; the source-facing yes-set presentation is the
canonical constructor `DecisionProblem.ofYesSet`, with the corresponding subset recovered by
`DecisionProblem.yesInstances`. -/
#check DecisionProblem.ofYesSet
