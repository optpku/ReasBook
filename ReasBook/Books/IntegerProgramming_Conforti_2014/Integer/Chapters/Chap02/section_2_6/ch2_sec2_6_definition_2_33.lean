/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_6.ch2_sec2_6_definition_2_33.Constraints

/-!
Sudoku constraint-programming completion model.

The reusable owner is `Sudoku.constraints`, with the set-valued view
`Sudoku.constraintSet` and membership companion `Sudoku.mem_constraintSet_iff`.
Here `Fin 9` encodes the textbook indices and digits `1, …, 9`, and `Fin 3`
indexes the `3 × 3` blocks corresponding to the starts `1, 4, 7`.
-/

/- Definition 2.33 [Constraint-programming formulation of Sudoku]: the Sudoku
constraint-programming model is formalized by `Sudoku.constraints`; its
displayed row, column, block, and clue conditions are exposed by
`Sudoku.constraints_iff`, and membership in the source-style solution set
`Sudoku.constraintSet` is exposed by `Sudoku.mem_constraintSet_iff`. -/

#check Sudoku.constraints
#check Sudoku.constraints_iff
#check Sudoku.constraintSet
#check Sudoku.mem_constraintSet_iff
