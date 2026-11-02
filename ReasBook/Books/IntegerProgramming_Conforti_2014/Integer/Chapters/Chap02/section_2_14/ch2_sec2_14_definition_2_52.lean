module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_52.KnapsackSet

public section

/-!
Concrete `0`--`1` knapsack set from the exercise.

This item is formalized by the reusable owner namespace `Knapsack252`, with source-facing
concrete data `Knapsack252.weights`, `Knapsack252.capacity`, and the exercise feasible set
`Knapsack252.set`.
-/

/- Definition 2.52 (`0`--`1` knapsack set in the exercise): the textbook set
`S := {x ∈ {0,1}^4 | 90 * x 0 + 35 * x 1 + 26 * x 2 + 25 * x 3 ≤ 138}` is formalized by the
concrete specialized owner `Knapsack252.set`, with the displayed membership condition recovered by
`Knapsack252.mem_set_iff`. -/
#check Knapsack252.set
#check Knapsack252.mem_set_iff

end
