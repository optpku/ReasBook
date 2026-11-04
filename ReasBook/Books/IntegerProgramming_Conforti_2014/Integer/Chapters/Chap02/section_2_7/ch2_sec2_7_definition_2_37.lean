/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

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
