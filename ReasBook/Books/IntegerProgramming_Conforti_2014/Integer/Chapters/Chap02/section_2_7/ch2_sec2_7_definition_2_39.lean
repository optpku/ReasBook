/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_definition_2_39.DFJ

/-!
Definition 2.39: DFJ formulation for the symmetric traveling salesman problem.

This item is formalized by the reusable formulation declarations
`SymmetricTravelingSalesmanProblem.DFJ.feasible`,
`SymmetricTravelingSalesmanProblem.DFJ.objective`, and
`SymmetricTravelingSalesmanProblem.DFJ.objectiveValues`.
-/

namespace SymmetricTravelingSalesmanProblem

universe u

/- Definition 2.39 (1): the canonical companion API for the symmetric DFJ formulation. -/
#check SymmetricTravelingSalesmanProblem.DFJ.feasible
#check SymmetricTravelingSalesmanProblem.DFJ.objective
#check SymmetricTravelingSalesmanProblem.DFJ.objectiveValues

section Definition_2_39

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (P : SymmetricTravelingSalesmanProblem V)

/-- Definition 2.39 (2) (Dantzig--Fulkerson--Johnson (DFJ) formulation for the STSP): a real
number `r` belongs to `DFJ.objectiveValues P` exactly when there is an edge vector
`x : P.graph.edgeSet → ℝ` satisfying the degree equations over
`incidentEdgeFinset P.graph v`, the proper-cut subtour inequalities, the binary conditions
`x e = 0 ∨ x e = 1`, and attaining objective value `r`. -/
theorem dfjFormulation_iff
    {r : ℝ} :
    r ∈ DFJ.objectiveValues P ↔
      ∃ x : P.graph.edgeSet → ℝ,
        DFJ.feasible P x ∧
          DFJ.objective P x = r := by
  rfl

end Definition_2_39

end SymmetricTravelingSalesmanProblem
