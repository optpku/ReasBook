module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_12.ch2_sec2_12_definition_2_50.Problem

public section

/-!
Quadratic assignment problem.

Definition 2.50 is formalized by the reusable owner `QuadraticAssignmentProblem`, with its
canonical constructor, feasible-set predicate, quadratic objective, and attained-value set in the
item-local foundation module.
-/

/- Definition 2.50 (Quadratic assignment problem): the problem data of a distance matrix and a
flow matrix is formalized by the declarations below. -/
#check QuadraticAssignmentProblem
#check QuadraticAssignmentProblem.ofData
#check QuadraticAssignmentProblem.feasibleSet
#check QuadraticAssignmentProblem.mem_feasibleSet_iff
#check QuadraticAssignmentProblem.objectiveValue
#check QuadraticAssignmentProblem.objectiveValue_eq_sum
#check QuadraticAssignmentProblem.objectiveValues
#check QuadraticAssignmentProblem.objectiveValue_mem_objectiveValues

namespace QuadraticAssignmentProblem

/-- Definition 2.50 (Quadratic assignment problem): for a problem instance `P`, membership of `r`
in `P.objectiveValues` is equivalent to the existence of a feasible assignment matrix `x` whose
quadratic objective value is `r`. This is the canonical companion theorem for
`QuadraticAssignmentProblem.objectiveValues`. -/
theorem mem_objectiveValues_iff
    {n : ℕ}
    {P : QuadraticAssignmentProblem n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : Matrix (Fin n) (Fin n) ℝ, x ∈ P.feasibleSet ∧ P.objectiveValue x = r := by
  exact mem_objectiveValues_iff_exists_feasible

end QuadraticAssignmentProblem

end
