module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_3.ch2_sec2_3_definition_2_6.Comparison

public section

open scoped BigOperators

/-!
Roll-indexed cutting stock formulation.

Definition 2.6 is formalized by the reusable owner `CuttingStock.RollIndexed`, with constructor
`CuttingStock.RollIndexed.ofData`, feasible region `CuttingStock.RollIndexed.feasibleSet`,
objective `CuttingStock.RollIndexed.objectiveValue`, attained-value set
`CuttingStock.RollIndexed.objectiveValues`, and canonical Chapter 1 comparison
`CuttingStock.RollIndexed.toMixedIntegerLinearProgram` in the item-local foundation module.
-/

/- The reusable owner and its core API for the roll-indexed cutting stock formulation are exposed
by the declarations below. -/
#check CuttingStock.RollIndexed
#check CuttingStock.RollIndexed.ofData
#check CuttingStock.RollIndexed.feasibleSet
#check CuttingStock.RollIndexed.mem_feasibleSet_iff
#check CuttingStock.RollIndexed.feasible_width_bound
#check CuttingStock.RollIndexed.feasible_demand_cover
#check CuttingStock.RollIndexed.feasible_roll_binary
#check CuttingStock.RollIndexed.toMixedPoint
#check CuttingStock.RollIndexed.toMixedIntegerLinearProgram
#check CuttingStock.RollIndexed.mem_toMixedIntegerLinearProgram_feasibleSet_iff
#check CuttingStock.RollIndexed.objectiveValue
#check CuttingStock.RollIndexed.objectiveValue_def
#check CuttingStock.RollIndexed.objectiveValue_eq_toMixedIntegerLinearProgram_objectiveValue
#check CuttingStock.RollIndexed.objectiveValues
#check CuttingStock.RollIndexed.mem_objectiveValues_iff_exists_feasible
#check CuttingStock.RollIndexed.mem_toMixedIntegerLinearProgram_objectiveValues_iff
#check
  CuttingStock.RollIndexed.objectiveValues_natCast_eq_toMixedIntegerLinearProgram_objectiveValues

namespace CuttingStock.RollIndexed

/-- Definition 2.6 (Cutting stock problem: roll-indexed formulation): for a roll-indexed cutting
stock instance `P`, membership of `r` in `P.objectiveValues` is equivalent to the existence of
roll-use variables `y : Fin p → ℕ` and cut-count variables `z : Matrix (Fin m) (Fin p) ℕ`
such that `(y, z) ∈ P.feasibleSet` and the displayed objective equation `∑ j, y j = r` holds. -/
theorem mem_objectiveValues_iff
    {m p : ℕ}
    {P : CuttingStock.RollIndexed m p}
    {r : ℕ} :
    r ∈ P.objectiveValues ↔
      ∃ y : Fin p → ℕ, ∃ z : Matrix (Fin m) (Fin p) ℕ,
        (y, z) ∈ P.feasibleSet ∧
        (∑ j : Fin p, y j) = r := by
  constructor
  · intro hr
    rcases mem_objectiveValues_iff_exists_feasible.mp hr with ⟨y, z, hyz, hobj⟩
    refine ⟨y, z, hyz, ?_⟩
    simpa [objectiveValue_def] using hobj
  · rintro ⟨y, z, hyz, hsum⟩
    exact mem_objectiveValues_iff_exists_feasible.2
      ⟨y, z, hyz, by simpa [objectiveValue_def] using hsum⟩

end CuttingStock.RollIndexed

end
