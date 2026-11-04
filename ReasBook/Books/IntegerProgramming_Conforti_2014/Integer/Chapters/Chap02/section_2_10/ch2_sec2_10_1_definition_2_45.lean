/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_10.ch2_sec2_10_1_definition_2_45.Model

public section

open scoped BigOperators

/-!
Capacitated facility location formulation.

The reusable owner is `CapacitatedFacilityLocation` on arbitrary customer and facility types,
with constructor
`CapacitatedFacilityLocation.ofData`, feasible region
`CapacitatedFacilityLocation.feasibleSet`, objective
`CapacitatedFacilityLocation.objectiveValue`, and attained-value set
`CapacitatedFacilityLocation.objectiveValues` in the item-local foundation module.
-/

/- The mixed-integer capacitated facility-location model with facility-opening variables `x`,
fractional assignment variables `y`, row equations `∑ j, y i j = 1`, capacity inequalities
`∑ i, P.demand i * y i j ≤ P.capacity j * x j`, assignment nonnegativity, binary opening
variables, and the displayed objective is formalized by the declarations below. -/
#check CapacitatedFacilityLocation
#check CapacitatedFacilityLocation.ofData
#check CapacitatedFacilityLocation.feasibleSet
#check CapacitatedFacilityLocation.mem_feasibleSet_iff
#check CapacitatedFacilityLocation.feasible_rowSum_eq_one
#check CapacitatedFacilityLocation.feasible_columnDemand_le_capacityOpen
#check CapacitatedFacilityLocation.feasible_assignment_nonneg
#check CapacitatedFacilityLocation.feasible_open_binary
#check CapacitatedFacilityLocation.objectiveValue
#check CapacitatedFacilityLocation.objectiveValue_def
#check CapacitatedFacilityLocation.objectiveValues
#check CapacitatedFacilityLocation.mem_objectiveValues_iff_exists_feasible

namespace CapacitatedFacilityLocation

/-- Definition 2.45 [Capacitated facility location problem]: for a problem instance `P`,
membership of `r` in `P.objectiveValues` is equivalent to the existence of `Fin`-indexed
facility-opening variables `x : Fin n → ℝ` and assignment variables
`y : Matrix (Fin m) (Fin n) ℝ` such that each customer row satisfies `∑ j, y i j = 1`, each
facility satisfies the weighted capacity inequality
`∑ i, P.demand i * y i j ≤ P.capacity j * x j`, every assignment entry is nonnegative, each
opening variable is binary, and the displayed capacitated facility-location objective equals
`r`. -/
theorem mem_objectiveValues_iff
    {m n : ℕ}
    {P : CapacitatedFacilityLocation (Fin m) (Fin n)}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ (x : Fin n → ℝ) (y : Matrix (Fin m) (Fin n) ℝ),
          (∀ i : Fin m, ∑ j : Fin n, y i j = 1) ∧
          (∀ j : Fin n, ∑ i : Fin m, P.demand i * y i j ≤ P.capacity j * x j) ∧
          (∀ i : Fin m, ∀ j : Fin n, 0 ≤ y i j) ∧
          (∀ j : Fin n, x j = 0 ∨ x j = 1) ∧
          ((∑ i : Fin m, ∑ j : Fin n, P.unitServiceCost i j * P.demand i * y i j) +
            ∑ j : Fin n, P.fixedCost j * x j = r) := by
  constructor
  · intro hr
    rcases (mem_objectiveValues_iff_exists_feasible P r).mp hr with ⟨⟨x, y⟩, hxy, hobj⟩
    rcases (mem_feasibleSet_iff P (x, y)).mp hxy with ⟨hrow, hcap, hnonneg, hbin⟩
    exact ⟨x, y, hrow, hcap, hnonneg, hbin, by simpa [objectiveValue_def] using hobj⟩
  · rintro ⟨x, y, hrow, hcap, hnonneg, hbin, hobj⟩
    refine (mem_objectiveValues_iff_exists_feasible P r).mpr ?_
    refine ⟨(x, y), (mem_feasibleSet_iff P (x, y)).mpr ?_, by simpa [objectiveValue_def] using hobj⟩
    exact ⟨hrow, hcap, hnonneg, hbin⟩

end CapacitatedFacilityLocation

end
