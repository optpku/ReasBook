/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_63.ZeroOneLinearProgram

/-!
`0`--`1` linear programming formulation.

This item is formalized by the reusable owner namespace `ZeroOneLinearProgram`, with a
source-facing feasible-set/objective/objective-values API and a canonical bridge to the Chapter 1
`MixedIntegerLinearProgram`.
-/

/- Definition 2.63: let `c ∈ ℤ^n`, `A ∈ ℤ^{m × n}`, and `b ∈ ℤ^m`. The associated `0`--`1`
linear program with objective `max c x`, constraints `A x ≤ b`, and binary vector condition
`x ∈ {0, 1}^n` is formalized by the declarations below. -/
#check ZeroOneLinearProgram.toMixedIntegerLinearProgram
#check ZeroOneLinearProgram.feasibleSet
#check ZeroOneLinearProgram.mem_feasibleSet_iff
#check ZeroOneLinearProgram.mem_toMixedIntegerLinearProgram_feasibleSet_iff
#check ZeroOneLinearProgram.objectiveValue
#check ZeroOneLinearProgram.objectiveValue_def
#check ZeroOneLinearProgram.objectiveValue_eq_toMixedIntegerLinearProgram_objectiveValue
#check ZeroOneLinearProgram.objectiveValues
#check ZeroOneLinearProgram.mem_objectiveValues_iff
#check ZeroOneLinearProgram.toMixedIntegerLinearProgram_isMixedZeroOne
#check ZeroOneLinearProgram.objectiveValues_eq_toMixedIntegerLinearProgram_objectiveValues
