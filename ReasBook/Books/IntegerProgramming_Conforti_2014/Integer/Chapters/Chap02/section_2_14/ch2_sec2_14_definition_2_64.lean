/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_64.PenalizedQuadraticRelaxation

/-!
Penalized quadratic relaxation of a `0`--`1` linear program.

This item is formalized by the reusable owner namespace `PenalizedQuadraticRelaxation`, with a
source-facing feasible-set, penalty, objective-value, and attained-value API together with thin
bridges to `ZeroOneLinearProgram` and the Chapter 1 LP relaxation.
-/

/- Definition 2.64: let `c ∈ ℤ^n`, `A ∈ ℤ^(m × n)`, `b ∈ ℤ^m`, and `M ∈ ℝ`. The penalized
quadratic relaxation with objective `max c x - M * (x ⬝ᵥ (fun j ↦ 1 - x j))`, constraints
`A x ≤ b`, and box constraints `0 ≤ x ≤ 1` is formalized by the declarations below. -/
#check PenalizedQuadraticRelaxation.feasibleSet
#check PenalizedQuadraticRelaxation.mem_feasibleSet_iff
#check PenalizedQuadraticRelaxation.mem_feasibleSet_iff_mem_toMixedIntegerLinearProgram_lpRelaxation
#check PenalizedQuadraticRelaxation.zeroOneFeasibleSet_subset_feasibleSet
#check PenalizedQuadraticRelaxation.penalty
#check PenalizedQuadraticRelaxation.penalty_def
#check PenalizedQuadraticRelaxation.penalty_eq_zero_of_binary
#check PenalizedQuadraticRelaxation.objectiveValue
#check PenalizedQuadraticRelaxation.objectiveValue_def
#check PenalizedQuadraticRelaxation.objectiveValue_eq_zeroOneLinearProgram_objectiveValue_of_binary
#check PenalizedQuadraticRelaxation.objectiveValues
#check PenalizedQuadraticRelaxation.mem_objectiveValues_iff
