module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_10.ch2_sec2_10_definition_2_44.Model

public section

/-!
Fixed-charge big-`M` formulation.

The reusable owner is `FixedChargeBigM`, with constructor companion
`FixedChargeBigM.ofData`, feasibility predicate `FixedChargeBigM.feasible`, objective
`FixedChargeBigM.objectiveValue`, source-facing cost `FixedChargeBigM.modeledCost`, and the key
modeling theorems in the item-local foundation module.
-/

/- Definition 2.44 [Fixed-charge cost via a big-`M` formulation]: the scalar formulation with
binary activation variable `x`, nonnegative usage variable `y`, linking bound
`y ≤ P.upperBound * x`, and linear objective `P.fixedCost * x + P.variableCost * y` is
formalized by the declarations below. -/
#check FixedChargeBigM
#check FixedChargeBigM.ofData
#check FixedChargeBigM.feasible
#check FixedChargeBigM.feasible_iff
#check FixedChargeBigM.objectiveValue
#check FixedChargeBigM.objectiveValue_def
#check FixedChargeBigM.modeledCost
#check FixedChargeBigM.modeledCost_zero
#check FixedChargeBigM.modeledCost_pos
#check FixedChargeBigM.exists_feasible_iff
#check FixedChargeBigM.positive_usage_forces_activation
#check FixedChargeBigM.objectiveValue_eq_modeledCost_of_pos
#check FixedChargeBigM.modeledCost_le_objectiveValue_of_feasible
#check FixedChargeBigM.exists_activation_eq_modeledCost

end
