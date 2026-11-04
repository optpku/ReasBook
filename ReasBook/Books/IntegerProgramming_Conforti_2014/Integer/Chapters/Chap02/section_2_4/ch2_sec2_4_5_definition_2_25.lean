/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_5_definition_2_25.SetCovering

public section

/-!
Crew scheduling set covering formulation.

The reusable owner is `SetCovering`; Definition 2.25 records that the feasible region, objective,
and attained-value set are given by the generic set-covering API in the item-local foundation
module.
-/

/- Definition 2.25 (Crew scheduling set covering formulation): the feasible region `S^C(A)` is
formalized by `SetCovering.feasibleSet A`, and minimizing the number of crews is formalized by
`SetCovering.cardinalityObjective` together with the attained-value set
`SetCovering.objectiveValues A`. -/
#check SetCovering.feasibleSet
#check SetCovering.mem_feasibleSet_iff
#check SetCovering.cardinalityObjective
#check SetCovering.objectiveValues

/- Definition 2.25 (Crew scheduling set covering formulation): a value `z` belongs to
`SetCovering.objectiveValues A` exactly when some feasible binary cover vector for the
flight-schedule incidence matrix `A` attains objective value `z`. This is the canonical
companion theorem for `SetCovering.objectiveValues`. -/
#check SetCovering.mem_objectiveValues_iff
