/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_2.Problem

@[expose] public section

open scoped Matrix

section Definition17

variable {m n p : ℕ}

namespace MixedIntegerLinearProgram

/-- The set of objective values attained on the LP relaxation of `P`. -/
def lpRelaxationObjectiveValues (P : MixedIntegerLinearProgram m n p) : Set ℝ :=
  P.objectiveValue '' P.lpRelaxation

/-- Unfolding equation for `P.lpRelaxationObjectiveValues`. -/
theorem lpRelaxationObjectiveValues_def
    (P : MixedIntegerLinearProgram m n p) :
    P.lpRelaxationObjectiveValues = P.objectiveValue '' P.lpRelaxation :=
  rfl

/-- Membership in `P.lpRelaxationObjectiveValues` means that the value is attained at some point
of the LP relaxation. -/
theorem mem_lpRelaxationObjectiveValues_iff
    (P : MixedIntegerLinearProgram m n p)
    (z : ℝ) :
    z ∈ P.lpRelaxationObjectiveValues ↔ ∃ xy ∈ P.lpRelaxation, P.objectiveValue xy = z :=
  Iff.rfl

/-- A candidate mixed point is MILP-optimal when it is feasible for `P` and its objective value is
the greatest value attained on `P.feasibleSet`. -/
def isOptimalSolution
    (P : MixedIntegerLinearProgram m n p)
    (xy : MixedRealPoint n p) : Prop :=
  xy ∈ P.feasibleSet ∧ IsGreatest P.objectiveValues (P.objectiveValue xy)

/-- The MILP optimality predicate unfolds to feasibility in `P.feasibleSet` together with
`IsGreatest` for the attained objective value. -/
theorem isOptimalSolution_iff
    (P : MixedIntegerLinearProgram m n p)
    (xy : MixedRealPoint n p) :
    P.isOptimalSolution xy ↔
      xy ∈ P.feasibleSet ∧ IsGreatest P.objectiveValues (P.objectiveValue xy) :=
  Iff.rfl

namespace isOptimalSolution

/-- An MILP-optimal mixed point is feasible for `P`. -/
theorem mem_feasibleSet
    {P : MixedIntegerLinearProgram m n p}
    {xy : MixedRealPoint n p}
    (hxy : P.isOptimalSolution xy) :
    xy ∈ P.feasibleSet :=
  hxy.1

/-- An MILP-optimal mixed point attains the greatest element of `P.objectiveValues`. -/
theorem objectiveIsGreatest
    {P : MixedIntegerLinearProgram m n p}
    {xy : MixedRealPoint n p}
    (hxy : P.isOptimalSolution xy) :
    IsGreatest P.objectiveValues (P.objectiveValue xy) :=
  hxy.2

end isOptimalSolution

/-- Definition 1.7 (3). The MILP `P` has an optimal solution when there exists a feasible point
whose objective value is the greatest element of the attained MILP objective set. -/
def hasOptimalSolution
    (P : MixedIntegerLinearProgram m n p) : Prop :=
  ∃ xy, P.isOptimalSolution xy

/-- The MILP optimal-solution existence statement is equivalent to the existence of a mixed point
that satisfies `P.isOptimalSolution`. -/
theorem hasOptimalSolution_iff
    (P : MixedIntegerLinearProgram m n p) :
    P.hasOptimalSolution ↔ ∃ xy, P.isOptimalSolution xy :=
  Iff.rfl

/-- A candidate mixed point is LP-relaxation-optimal when it is feasible for `P.lpRelaxation` and
its objective value is the greatest value attained on `P.lpRelaxation`. -/
def isLpRelaxationOptimalSolution
    (P : MixedIntegerLinearProgram m n p)
    (xy : MixedRealPoint n p) : Prop :=
  xy ∈ P.lpRelaxation ∧
    IsGreatest P.lpRelaxationObjectiveValues (P.objectiveValue xy)

/-- The LP-relaxation optimality predicate unfolds to feasibility in `P.lpRelaxation` together
with `IsGreatest` for the attained objective value. -/
theorem isLpRelaxationOptimalSolution_iff
    (P : MixedIntegerLinearProgram m n p)
    (xy : MixedRealPoint n p) :
    P.isLpRelaxationOptimalSolution xy ↔
      xy ∈ P.lpRelaxation ∧
        IsGreatest P.lpRelaxationObjectiveValues (P.objectiveValue xy) :=
  Iff.rfl

namespace isLpRelaxationOptimalSolution

/-- An LP-relaxation-optimal mixed point belongs to `P.lpRelaxation`. -/
theorem mem_lpRelaxation
    {P : MixedIntegerLinearProgram m n p}
    {xy : MixedRealPoint n p}
    (hxy : P.isLpRelaxationOptimalSolution xy) :
    xy ∈ P.lpRelaxation :=
  hxy.1

/-- An LP-relaxation-optimal mixed point attains the greatest value on
`P.lpRelaxationObjectiveValues`. -/
theorem objectiveIsGreatest
    {P : MixedIntegerLinearProgram m n p}
    {xy : MixedRealPoint n p}
    (hxy : P.isLpRelaxationOptimalSolution xy) :
    IsGreatest P.lpRelaxationObjectiveValues (P.objectiveValue xy) :=
  hxy.2

end isLpRelaxationOptimalSolution

/-- Definition 1.7 (4). The LP relaxation of `P` has an optimal solution when there exists a
point of `P.lpRelaxation` whose objective value is the greatest attained LP-relaxation value. -/
def lpRelaxationHasOptimalSolution
    (P : MixedIntegerLinearProgram m n p) : Prop :=
  ∃ xy, P.isLpRelaxationOptimalSolution xy

/-- The LP-relaxation optimal-solution existence statement is equivalent to the existence of a
mixed point that satisfies `P.isLpRelaxationOptimalSolution`. -/
theorem lpRelaxationHasOptimalSolution_iff
    (P : MixedIntegerLinearProgram m n p) :
    P.lpRelaxationHasOptimalSolution ↔
      ∃ xy, P.isLpRelaxationOptimalSolution xy :=
  Iff.rfl

end MixedIntegerLinearProgram

end Definition17

end
