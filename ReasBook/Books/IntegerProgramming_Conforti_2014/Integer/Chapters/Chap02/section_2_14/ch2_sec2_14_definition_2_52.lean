/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

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
