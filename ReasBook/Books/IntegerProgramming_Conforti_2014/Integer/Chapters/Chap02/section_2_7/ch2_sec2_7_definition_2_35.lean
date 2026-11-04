/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_definition_2_35.DFJ

/-!
Definition 2.35: DFJ formulation for the asymmetric traveling salesman problem.

This item is formalized by the reusable formulation declarations
`AsymmetricTravelingSalesmanProblem.DFJ.feasible`,
`AsymmetricTravelingSalesmanProblem.DFJ.objective`, and
`AsymmetricTravelingSalesmanProblem.DFJ.objectiveValues`.
-/

namespace AsymmetricTravelingSalesmanProblem

/- Definition 2.35 (1): the canonical companion API for the asymmetric DFJ formulation. -/
#check DFJ.feasible
#check DFJ.objective
#check DFJ.objectiveValues

/- Definition 2.35 (2) (Dantzig--Fulkerson--Johnson (DFJ) formulation for the ATSP): the
source-facing attained-value characterization is the canonical companion theorem
`DFJ.mem_objectiveValues_iff`. -/
#check DFJ.mem_objectiveValues_iff

end AsymmetricTravelingSalesmanProblem
