module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_8.ch2_sec2_8_definition_2_40.Problem

public section

/-!
Generalized assignment problem.

Definition 2.40 is formalized by the reusable owner `GeneralizedAssignmentProblem`, with its
canonical constructor, feasible-set predicate, objective, and attained-value set in the item-local
foundation module.
-/

/- Definition 2.40 (Generalized assignment problem): the problem data of objective coefficients,
resource coefficients, and capacities is formalized by the declarations below. -/
#check GeneralizedAssignmentProblem
#check GeneralizedAssignmentProblem.ofData
#check GeneralizedAssignmentProblem.feasibleSet
#check GeneralizedAssignmentProblem.mem_feasibleSet_iff
#check GeneralizedAssignmentProblem.objectiveValue
#check GeneralizedAssignmentProblem.objectiveValue_def
#check GeneralizedAssignmentProblem.objectiveValues

namespace GeneralizedAssignmentProblem

/-- Definition 2.40 (Generalized assignment problem): for a problem instance `P`, membership of
`r` in `P.objectiveValues` is equivalent to the existence of a binary assignment matrix `x` whose
rows satisfy `∑ j, x i j = 1`, whose capacity constraints satisfy
`∑ i, P.resourceCoeff i j * x i j ≤ P.capacity j`, and whose objective value is
`∑ i, ∑ j, P.objectiveCoeff i j * x i j = r`. This is the canonical companion theorem for
`GeneralizedAssignmentProblem.objectiveValues`. -/
theorem mem_objectiveValues_iff
    {m n : ℕ}
    {P : GeneralizedAssignmentProblem m n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : Matrix (Fin m) (Fin n) ℝ, x ∈ P.feasibleSet ∧ P.objectiveValue x = r := by
  -- Re-expose the source-facing attained-value criterion from the reusable foundation module.
  exact mem_objectiveValues_iff_exists_feasible

end GeneralizedAssignmentProblem

end
