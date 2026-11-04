/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_3.ch2_sec2_3_algorithm_2_1

public section

/- Proposition 2.3 (Dual of the LP relaxation of the pattern-based model).
This item is formalized by the existing restricted/full master LP owners in
`CuttingStockColumnGeneration`. -/

#check CuttingStockColumnGeneration.master_feasible
#check CuttingStockColumnGeneration.master_feasible_iff
#check CuttingStockColumnGeneration.master_objective
#check CuttingStockColumnGeneration.master_objective_values
#check CuttingStockColumnGeneration.master_dual_feasible
#check CuttingStockColumnGeneration.master_dual_feasible_iff
#check CuttingStockColumnGeneration.master_dual_objective
#check CuttingStockColumnGeneration.master_dual_objective_values

end
