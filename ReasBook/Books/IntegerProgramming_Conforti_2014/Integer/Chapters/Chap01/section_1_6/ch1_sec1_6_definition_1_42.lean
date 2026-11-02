module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_6.ch1_sec1_6_definition_1_42.Problem

public section

/- Definition 1.42 [Integer program with bounds]: the optimization problem
`min {c ⬝ᵥ x : A *ᵥ x = b, l ≤ x, x ≤ u, x : Fin n → ℤ}` is formalized by the reusable owner
`BoundedIntegerProgram`, together with its feasible-set, objective, attained-value, and
optimal-solution API. -/
#check BoundedIntegerProgram
#check BoundedIntegerProgram.ofCoefficients
#check BoundedIntegerProgram.feasibleSet
#check BoundedIntegerProgram.mem_feasibleSet_iff
#check BoundedIntegerProgram.objectiveValue
#check BoundedIntegerProgram.objectiveValues
#check BoundedIntegerProgram.isOptimalSolution
#check BoundedIntegerProgram.hasOptimalSolution

end
