/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_6.ch1_sec1_6_definition_1_41.Optimization

public section

/- Definition 1.41 (Approximation algorithm). Let `Π` be an optimization problem and let `α ≥ 1`.
An algorithm is called an `α`-approximation algorithm for `Π` if, for every instance of `Π`, it
runs in polynomial time and returns a feasible solution whose objective value is within a factor
`α` of the optimum value. -/
#check OptimizationProblem.IsApproximationAlgorithm
