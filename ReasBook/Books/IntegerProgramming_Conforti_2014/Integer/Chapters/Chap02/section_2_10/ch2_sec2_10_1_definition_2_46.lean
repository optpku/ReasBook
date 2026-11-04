/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_10.ch2_sec2_10_1_definition_2_46.Model

public section

/-!
Uncapacitated facility location formulation.

The reusable owner is `UncapacitatedFacilityLocation`, with constructor
`UncapacitatedFacilityLocation.ofData`, feasible region
`UncapacitatedFacilityLocation.feasibleSet`, objective
`UncapacitatedFacilityLocation.objectiveValue`, and attained-value set
`UncapacitatedFacilityLocation.objectiveValues` in the item-local foundation module.
-/

/- Definition 2.46 [Uncapacitated facility location problem (UFL)]: the aggregated binary
facility-location model with facility-opening variables `x`, assignment variables `y`, row
equations `∑ j, y i j = 1`, aggregated linking inequalities
`∑ i, y i j ≤ (m : ℝ) * x j`, and the displayed objective is formalized by the declarations
below. -/
#check UncapacitatedFacilityLocation
#check UncapacitatedFacilityLocation.ofData
#check UncapacitatedFacilityLocation.feasibleSet
#check UncapacitatedFacilityLocation.mem_feasibleSet_iff
#check UncapacitatedFacilityLocation.feasible_rowSum_eq_one
#check UncapacitatedFacilityLocation.feasible_columnSum_le_scaledOpen
#check UncapacitatedFacilityLocation.feasible_open_binary
#check UncapacitatedFacilityLocation.feasible_assignment_binary
#check UncapacitatedFacilityLocation.objectiveValue
#check UncapacitatedFacilityLocation.objectiveValue_def
#check UncapacitatedFacilityLocation.objectiveValues
#check UncapacitatedFacilityLocation.mem_objectiveValues_iff_exists_feasible

namespace UncapacitatedFacilityLocation

/-- Definition 2.46 [Uncapacitated facility location problem (UFL)]: for a problem instance
`P`, membership of `r` in `P.objectiveValues` is equivalent to the existence of
facility-opening variables `x : Fin n → ℝ` and assignment variables
`y : Matrix (Fin m) (Fin n) ℝ` such that `(x, y) ∈ P.feasibleSet` and
`P.objectiveValue (x, y) = r`. -/
theorem mem_objectiveValues_iff
    {m n : ℕ}
    {P : UncapacitatedFacilityLocation m n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : Fin n → ℝ, ∃ y : Matrix (Fin m) (Fin n) ℝ,
        (x, y) ∈ P.feasibleSet ∧ P.objectiveValue (x, y) = r := by
  constructor
  · intro hr
    -- Repackage the imported product witness into separate `x` and `y` witnesses.
    rcases (mem_objectiveValues_iff_exists_feasible (P := P) (r := r)).mp hr with
      ⟨xy, hxy, hobj⟩
    exact ⟨xy.1, xy.2, hxy, hobj⟩
  · rintro ⟨x, y, hxy, hobj⟩
    -- Package the separated witnesses back into the pair expected by the companion theorem.
    exact (mem_objectiveValues_iff_exists_feasible (P := P) (r := r)).mpr ⟨(x, y), hxy, hobj⟩

end UncapacitatedFacilityLocation

end
