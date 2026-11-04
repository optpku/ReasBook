/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_6.ch2_sec2_6_definition_2_32.Sudoku

/-!
Sudoku integer-programming completion model.

The reusable owner is `Sudoku.feasibleSet`. Here `Fin 9` encodes the textbook indices
`1, …, 9`, and `Fin 3` indexes the `3 × 3` blocks corresponding to the starts `1, 4, 7`.
-/

/- Definition 2.32 [Integer programming model of Sudoku]: the Sudoku completion model is
formalized by `Sudoku.feasibleSet`, and its displayed row, column, block, cell, binary, and
clue-fixing constraints are exposed by `Sudoku.mem_feasibleSet_iff`. -/

#check Sudoku.feasibleSet
#check Sudoku.mem_feasibleSet_iff
