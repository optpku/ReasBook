module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_10.ch2_sec2_10_1_definition_2_47.Model

public section

open scoped BigOperators

/-!
Disaggregated uncapacitated facility location formulation.

The reusable owner is `UncapacitatedFacilityLocation.Disaggregated`, with constructor
`UncapacitatedFacilityLocation.Disaggregated.ofData`, feasible region
`UncapacitatedFacilityLocation.Disaggregated.feasibleSet`, objective
`UncapacitatedFacilityLocation.Disaggregated.objectiveValue`, and attained-value set
`UncapacitatedFacilityLocation.Disaggregated.objectiveValues` in the item-local foundation module.
-/

/- Definition 2.47 [Disaggregated UFL formulation]: the disaggregated binary uncapacitated
facility-location model with facility-opening variables `x`, assignment variables `y`, assignment
equations, linking inequalities, and the displayed objective is formalized by the declarations
below. -/
#check UncapacitatedFacilityLocation.Disaggregated
#check UncapacitatedFacilityLocation.Disaggregated.ofData
#check UncapacitatedFacilityLocation.Disaggregated.feasibleSet
#check UncapacitatedFacilityLocation.Disaggregated.mem_feasibleSet_iff
#check UncapacitatedFacilityLocation.Disaggregated.feasible_rowSum_eq_one
#check UncapacitatedFacilityLocation.Disaggregated.feasible_assignment_le_open
#check UncapacitatedFacilityLocation.Disaggregated.feasible_open_binary
#check UncapacitatedFacilityLocation.Disaggregated.feasible_assignment_binary
#check UncapacitatedFacilityLocation.Disaggregated.objectiveValue
#check UncapacitatedFacilityLocation.Disaggregated.objectiveValue_def
#check UncapacitatedFacilityLocation.Disaggregated.objectiveValues
#check UncapacitatedFacilityLocation.Disaggregated.mem_objectiveValues_iff_exists_feasible

namespace UncapacitatedFacilityLocation.Disaggregated

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_10/ch2_sec2_10_1_definition_2_47.lean:
For a problem instance `P`, membership of `r` in `P.objectiveValues` is equivalent to the
existence of facility-opening variables
`x : Fin n → ℝ` and assignment variables `y : Matrix (Fin m) (Fin n) ℝ` such that every customer
row satisfies `∑ j, y i j = 1`, every assignment satisfies `y i j ≤ x j`, both `x` and `y` are
binary, and the displayed objective
`∑ i, ∑ j, P.unitServiceCost i j * P.demand i * y i j + ∑ j, P.fixedCost j * x j`
attains the value `r`. -/
theorem mem_objectiveValues_iff
    {m n : ℕ}
    {P : UncapacitatedFacilityLocation.Disaggregated m n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : Fin n → ℝ, ∃ y : Matrix (Fin m) (Fin n) ℝ,
        (∀ i : Fin m, ∑ j : Fin n, y i j = 1) ∧
        (∀ i : Fin m, ∀ j : Fin n, y i j ≤ x j) ∧
        (∀ i : Fin m, ∀ j : Fin n, y i j = 0 ∨ y i j = 1) ∧
        (∀ j : Fin n, x j = 0 ∨ x j = 1) ∧
        ((∑ i : Fin m, ∑ j : Fin n, P.unitServiceCost i j * P.demand i * y i j) +
          ∑ j : Fin n, P.fixedCost j * x j = r) := by
  constructor
  · -- Extract the feasible solution attaining the given objective value.
    intro hr
    rcases mem_objectiveValues_iff_exists_feasible.mp hr with ⟨x, y, hxy, hvalue⟩
    rcases mem_feasibleSet_iff.mp hxy with ⟨hrow, hlink, hassignBinary, hopenBinary⟩
    -- Rewrite the abstract objective equation into the displayed finite-sum formula.
    have hdisplayed :
        (∑ i : Fin m, ∑ j : Fin n, P.unitServiceCost i j * P.demand i * y i j) +
            ∑ j : Fin n, P.fixedCost j * x j = r := by
      simpa only [objectiveValue_def] using hvalue
    exact ⟨x, y, hrow, hlink, hassignBinary, hopenBinary, hdisplayed⟩
  · -- Reassemble the explicit constraints into feasibility and attained-value membership.
    rintro ⟨x, y, hrow, hlink, hassignBinary, hopenBinary, hdisplayed⟩
    have hxy : (x, y) ∈ P.feasibleSet :=
      mem_feasibleSet_iff.mpr ⟨hrow, hlink, hassignBinary, hopenBinary⟩
    -- Fold the displayed sum back to the canonical objective function.
    have hvalue : P.objectiveValue (x, y) = r := by
      simpa only [objectiveValue_def] using hdisplayed
    exact mem_objectiveValues_iff_exists_feasible.mpr ⟨x, y, hxy, hvalue⟩

end UncapacitatedFacilityLocation.Disaggregated

end
