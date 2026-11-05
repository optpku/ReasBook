/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_1.ch2_sec2_1_definition_2_3.Optimization
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_2.ch2_sec2_2_definition_2_4.KnapsackSet

public section

/-!
`0`--`1` knapsack set and `0`--`1` knapsack problem.

This item is formalized by the existing feasible-set owner `zero_one_knapsack_set` together with
the reusable optimization namespace `ZeroOneKnapsack`.
-/

/- Definition 2.3 (1): for `n ≥ 1`, a weight vector `a : Fin n → ℝ` with `a i > 0`, and
capacity `b : ℝ`, the `0`--`1` knapsack set
`K = {x ∈ {0,1}^n | ∑ i, a i * x i ≤ b}` is formalized by `zero_one_knapsack_set`. -/
#check zero_one_knapsack_set

/- Definition 2.3 (2): given `c : Fin n → ℝ`, the `0`--`1` knapsack problem `max {c x | x ∈ K}`
is formalized by the objective `ZeroOneKnapsack.objectiveValue`, the attained-value set
`ZeroOneKnapsack.objectiveValues`, its membership criterion
`ZeroOneKnapsack.mem_objectiveValues_iff`, and the optimizer predicate
`ZeroOneKnapsack.isOptimalSolution`. -/
#check ZeroOneKnapsack.objectiveValue
#check ZeroOneKnapsack.objectiveValues
#check ZeroOneKnapsack.mem_objectiveValues_iff
#check ZeroOneKnapsack.isOptimalSolution
