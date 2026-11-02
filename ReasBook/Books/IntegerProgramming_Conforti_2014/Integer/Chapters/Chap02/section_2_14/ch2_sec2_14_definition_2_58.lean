module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_58.LotSizing

public section

/-!
Lot-sizing MILP formulation.

This item is formalized by the reusable owner namespace `LotSizing`, with source-facing
feasibility predicate `LotSizing.feasible`, objective `LotSizing.objective`, and attained-value
set `LotSizing.objectiveValues`.
-/

/- Definition 2.58 (Lot-sizing: MILP): the textbook feasibility constraints are formalized by
`LotSizing.feasible`, the lot-sizing objective by `LotSizing.objective`, and the attained-value
set by `LotSizing.objectiveValues`. -/
#check LotSizing.feasible
#check LotSizing.objective
#check LotSizing.objectiveValues

/- Definition 2.58 (Lot-sizing: MILP): a real number `r` belongs to
`LotSizing.objectiveValues d f p i M s0` exactly when there are production variables
`q : Fin n → ℝ`, an inventory path `stock : Fin (n + 1) → ℝ`, and setup variables
`y : Fin n → ℝ` satisfying `LotSizing.feasible d M s0 q stock y` and attaining objective value
`r`. This is the canonical companion theorem for `LotSizing.objectiveValues`. -/
#check LotSizing.mem_objectiveValues_iff

end
