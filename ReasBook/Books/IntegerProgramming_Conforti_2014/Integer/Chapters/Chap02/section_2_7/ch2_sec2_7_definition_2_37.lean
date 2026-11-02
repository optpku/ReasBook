import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_definition_2_37.LegIndexed

/-!
Definition 2.37: time-indexed (leg-indexed) formulation for the asymmetric traveling salesman
problem.

This item is formalized by the reusable formulation declarations
`AsymmetricTravelingSalesmanProblem.LegIndexed.feasible`,
`AsymmetricTravelingSalesmanProblem.LegIndexed.objective`, and
`AsymmetricTravelingSalesmanProblem.LegIndexed.objectiveValues`.
-/

namespace AsymmetricTravelingSalesmanProblem

/- Definition 2.37 (1): the canonical companion API for the leg-indexed ATSP formulation. -/
#check LegIndexed.feasible
#check LegIndexed.objective
#check LegIndexed.objectiveValues

/- Definition 2.37 (2) (time-indexed (leg-indexed) formulation for ATSP): the source-facing
attained-value characterization is the canonical companion theorem
`LegIndexed.mem_objectiveValues_iff`. -/
#check LegIndexed.mem_objectiveValues_iff

end AsymmetricTravelingSalesmanProblem
