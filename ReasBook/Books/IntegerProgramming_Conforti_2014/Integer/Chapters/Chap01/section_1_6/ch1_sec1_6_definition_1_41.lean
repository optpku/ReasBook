module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_6.ch1_sec1_6_definition_1_41.Optimization

public section

/- Definition 1.41 (Approximation algorithm). Let `Π` be an optimization problem and let `α ≥ 1`.
An algorithm is called an `α`-approximation algorithm for `Π` if, for every instance of `Π`, it
runs in polynomial time and returns a feasible solution whose objective value is within a factor
`α` of the optimum value. -/
#check OptimizationProblem.IsApproximationAlgorithm
