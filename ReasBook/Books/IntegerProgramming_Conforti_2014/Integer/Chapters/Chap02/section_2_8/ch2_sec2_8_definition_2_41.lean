import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_8.ch2_sec2_8_definition_2_41.Problem

/-!
Operating room scheduling problem.

Definition 2.41 is formalized by the reusable owner `OperatingRoomSchedulingProblem`, together
with its canonical bridge `OperatingRoomSchedulingProblem.toMixedIntegerLinearProgram` to the
Chapter 1 `MixedIntegerLinearProgram` and the derived source-facing feasible/objective API in the
item-local foundation module.
-/

/-
Definition 2.41 (Operating room scheduling problem): the problem data of surgery times and a
room-time bound is formalized by the declarations below.
-/
#check OperatingRoomSchedulingProblem
#check OperatingRoomSchedulingProblem.ofData
#check OperatingRoomSchedulingProblem.toMixedIntegerLinearProgram
#check OperatingRoomSchedulingProblem.toMixedIntegerLinearProgram_isMixedZeroOne
#check OperatingRoomSchedulingProblem.feasibleSet
#check OperatingRoomSchedulingProblem.mem_feasibleSet_iff
#check OperatingRoomSchedulingProblem.objectiveValue
#check OperatingRoomSchedulingProblem.objectiveValue_def
#check OperatingRoomSchedulingProblem.objectiveValues
#check OperatingRoomSchedulingProblem.objectiveValues_eq_toMixedIntegerLinearProgram_objectiveValues

namespace OperatingRoomSchedulingProblem

/-- Definition 2.41 (Operating room scheduling problem): for a problem instance `P`, membership of
`r` in `P.objectiveValues` is equivalent to the existence of a binary schedule matrix `x` whose
rows satisfy `∑ j, x i j ≤ 1`, whose room-time constraints satisfy
`∑ i, P.surgeryTime i j * x i j ≤ P.timeBound`, and whose objective value is
`∑ i, ∑ j, P.surgeryTime i j * x i j = r`. This is the canonical companion theorem for
`OperatingRoomSchedulingProblem.objectiveValues`. -/
theorem mem_objectiveValues_iff
    {m n : ℕ}
    {P : OperatingRoomSchedulingProblem m n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : Matrix (Fin m) (Fin n) ℝ, x ∈ P.feasibleSet ∧ P.objectiveValue x = r := by
  -- Re-expose the source-facing attained-value criterion from the reusable foundation module.
  exact mem_objectiveValues_iff_exists_feasible

end OperatingRoomSchedulingProblem
