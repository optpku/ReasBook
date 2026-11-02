module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_6.ch1_sec1_6_definition_1_42.Problem

open scoped Matrix

public section

variable {m n : ℕ}

namespace BoundedIntegerProgram

/-- Definition 1.43 [Improving direction]: for a bounded integer program `P`, a direction `z`
at a feasible base point `x₀` is improving when both `x₀` and `x₀ + z` belong to `P.feasibleSet`
and the translated point strictly lowers the objective value. -/
structure isImprovingDirection
    (P : BoundedIntegerProgram m n)
    (x₀ z : Fin n → ℤ) : Prop where
  /-- The base point `x₀` is feasible for `P`. -/
  mem_feasibleSet : x₀ ∈ P.feasibleSet
  /-- The translated point `x₀ + z` is feasible for `P`. -/
  add_mem_feasibleSet : x₀ + z ∈ P.feasibleSet
  /-- The translated point strictly lowers the objective value relative to `x₀`. -/
  objectiveValue_lt : P.objectiveValue (x₀ + z) < P.objectiveValue x₀

/-- `P.isImprovingDirection x₀ z` unfolds to feasibility of `x₀`, feasibility of `x₀ + z`, and
strict decrease of the objective value from `x₀` to `x₀ + z`. -/
theorem isImprovingDirection_iff
    (P : BoundedIntegerProgram m n)
    (x₀ z : Fin n → ℤ) :
    P.isImprovingDirection x₀ z ↔
      x₀ ∈ P.feasibleSet ∧
        x₀ + z ∈ P.feasibleSet ∧
        P.objectiveValue (x₀ + z) < P.objectiveValue x₀ := by
  constructor
  · intro hz
    exact ⟨hz.mem_feasibleSet, hz.add_mem_feasibleSet, hz.objectiveValue_lt⟩
  · rintro ⟨hx₀, hx₀z, hobj⟩
    exact ⟨hx₀, hx₀z, hobj⟩

namespace isImprovingDirection

/-- Construct an improving direction from the three defining conditions in Definition 1.43. -/
def ofConditions
    {P : BoundedIntegerProgram m n}
    {x₀ z : Fin n → ℤ}
    (hx₀ : x₀ ∈ P.feasibleSet)
    (hx₀z : x₀ + z ∈ P.feasibleSet)
    (hobj : P.objectiveValue (x₀ + z) < P.objectiveValue x₀) :
    P.isImprovingDirection x₀ z :=
  { mem_feasibleSet := hx₀
    add_mem_feasibleSet := hx₀z
    objectiveValue_lt := hobj }

/-- The translated point of an improving direction attains an objective value in
`P.objectiveValues`. -/
theorem add_objectiveValue_mem_objectiveValues
    {P : BoundedIntegerProgram m n}
    {x₀ z : Fin n → ℤ}
    (hz : P.isImprovingDirection x₀ z) :
    P.objectiveValue (x₀ + z) ∈ P.objectiveValues :=
  (P.mem_objectiveValues_iff (P.objectiveValue (x₀ + z))).2
    ⟨x₀ + z, hz.add_mem_feasibleSet, rfl⟩

/-- An improving direction at `x₀` certifies that `x₀` is not an optimal solution of `P`. -/
theorem not_isOptimalSolution
    {P : BoundedIntegerProgram m n}
    {x₀ z : Fin n → ℤ}
    (hz : P.isImprovingDirection x₀ z) :
    ¬ P.isOptimalSolution x₀ := by
  intro hx₀
  have hleast : IsLeast P.objectiveValues (P.objectiveValue x₀) :=
    BoundedIntegerProgram.isOptimalSolution.objectiveIsLeast hx₀
  have hle : P.objectiveValue x₀ ≤ P.objectiveValue (x₀ + z) :=
    hleast.2 (add_objectiveValue_mem_objectiveValues hz)
  exact (not_le_of_gt hz.objectiveValue_lt) hle

end isImprovingDirection

end BoundedIntegerProgram

end
