/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_proposition_1_22.ColumnOperations

public section

/- Definition 1.39 [Unimodular column operations]. The canonical reusable owner for this item is
`Matrix.IsElementaryUnimodularColumnMatrix`. Its three source operations are represented by
`Matrix.columnSwapMatrix`, `Matrix.columnAddMatrix`, and `Matrix.columnNegMatrix`. -/
#check Matrix.IsElementaryUnimodularColumnMatrix
#check Matrix.columnSwapMatrix
#check Matrix.columnAddMatrix
#check Matrix.columnNegMatrix

end
