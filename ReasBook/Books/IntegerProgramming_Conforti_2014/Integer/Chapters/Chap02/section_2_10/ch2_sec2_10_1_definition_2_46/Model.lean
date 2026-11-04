/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Image

public section

open scoped BigOperators

/-- An uncapacitated facility location instance with customer demands, facility opening costs,
and unit service costs. -/
structure UncapacitatedFacilityLocation (m n : ℕ) where
  demand : Fin m → ℝ
  fixedCost : Fin n → ℝ
  unitServiceCost : Matrix (Fin m) (Fin n) ℝ

namespace UncapacitatedFacilityLocation

/-- Construct an uncapacitated facility location instance from its demand, opening-cost, and
unit-service-cost data. -/
def ofData
    {m n : ℕ}
    (demand : Fin m → ℝ)
    (fixedCost : Fin n → ℝ)
    (unitServiceCost : Matrix (Fin m) (Fin n) ℝ) :
    UncapacitatedFacilityLocation m n :=
  { demand := demand
    fixedCost := fixedCost
    unitServiceCost := unitServiceCost }

/-- The feasible opening vectors and assignment matrices `(x, y)` of `P`: every customer is
assigned exactly once, every facility column satisfies the aggregated linking inequality
`∑ i, y i j ≤ (m : ℝ) * x j`, and both `x` and `y` are binary. -/
def feasibleSet
    {m n : ℕ}
    (P : UncapacitatedFacilityLocation m n) :
    Set ((Fin n → ℝ) × Matrix (Fin m) (Fin n) ℝ) :=
  let _ := P
  { xy |
      (∀ i : Fin m, ∑ j : Fin n, xy.2 i j = 1) ∧
      (∀ j : Fin n, ∑ i : Fin m, xy.2 i j ≤ (m : ℝ) * xy.1 j) ∧
      (∀ i : Fin m, ∀ j : Fin n, xy.2 i j = 0 ∨ xy.2 i j = 1) ∧
      (∀ j : Fin n, xy.1 j = 0 ∨ xy.1 j = 1) }

/-- Membership in `P.feasibleSet` is exactly the conjunction of the displayed assignment,
aggregated linking, and binary constraints. -/
theorem mem_feasibleSet_iff
    {m n : ℕ}
    {P : UncapacitatedFacilityLocation m n}
    {xy : (Fin n → ℝ) × Matrix (Fin m) (Fin n) ℝ} :
    xy ∈ P.feasibleSet ↔
      (∀ i : Fin m, ∑ j : Fin n, xy.2 i j = 1) ∧
      (∀ j : Fin n, ∑ i : Fin m, xy.2 i j ≤ (m : ℝ) * xy.1 j) ∧
      (∀ i : Fin m, ∀ j : Fin n, xy.2 i j = 0 ∨ xy.2 i j = 1) ∧
      (∀ j : Fin n, xy.1 j = 0 ∨ xy.1 j = 1) := by
  -- The feasible set is defined by exactly these four constraint families.
  rfl

/-- A feasible uncapacitated facility location solution assigns each customer row to exactly one
facility. -/
theorem feasible_rowSum_eq_one
    {m n : ℕ}
    {P : UncapacitatedFacilityLocation m n}
    {x : Fin n → ℝ}
    {y : Matrix (Fin m) (Fin n) ℝ}
    (hxy : (x, y) ∈ P.feasibleSet)
    (i : Fin m) :
    ∑ j : Fin n, y i j = 1 := by
  -- Project the row-sum constraint from feasible-set membership.
  exact ((mem_feasibleSet_iff (P := P) (xy := (x, y))).mp hxy).1 i

/-- A feasible uncapacitated facility location solution satisfies the aggregated linking
inequalities `∑ i, y i j ≤ (m : ℝ) * x j`. -/
theorem feasible_columnSum_le_scaledOpen
    {m n : ℕ}
    {P : UncapacitatedFacilityLocation m n}
    {x : Fin n → ℝ}
    {y : Matrix (Fin m) (Fin n) ℝ}
    (hxy : (x, y) ∈ P.feasibleSet)
    (j : Fin n) :
    ∑ i : Fin m, y i j ≤ (m : ℝ) * x j := by
  -- Project the aggregated linking inequality from feasible-set membership.
  exact ((mem_feasibleSet_iff (P := P) (xy := (x, y))).mp hxy).2.1 j

/-- Every facility-opening variable of a feasible uncapacitated facility location solution is
binary. -/
theorem feasible_open_binary
    {m n : ℕ}
    {P : UncapacitatedFacilityLocation m n}
    {x : Fin n → ℝ}
    {y : Matrix (Fin m) (Fin n) ℝ}
    (hxy : (x, y) ∈ P.feasibleSet)
    (j : Fin n) :
    x j = 0 ∨ x j = 1 := by
  -- Project the binary-opening constraint from feasible-set membership.
  exact ((mem_feasibleSet_iff (P := P) (xy := (x, y))).mp hxy).2.2.2 j

/-- Every assignment variable of a feasible uncapacitated facility location solution is binary. -/
theorem feasible_assignment_binary
    {m n : ℕ}
    {P : UncapacitatedFacilityLocation m n}
    {x : Fin n → ℝ}
    {y : Matrix (Fin m) (Fin n) ℝ}
    (hxy : (x, y) ∈ P.feasibleSet)
    (i : Fin m)
    (j : Fin n) :
    y i j = 0 ∨ y i j = 1 := by
  -- Project the binary-assignment constraint from feasible-set membership.
  exact ((mem_feasibleSet_iff (P := P) (xy := (x, y))).mp hxy).2.2.1 i j

/-- The uncapacitated facility location objective value of `(x, y)` is the displayed shipping-cost
double sum plus the facility-opening-cost sum. -/
def objectiveValue
    {m n : ℕ}
    (P : UncapacitatedFacilityLocation m n) :
    ((Fin n → ℝ) × Matrix (Fin m) (Fin n) ℝ) → ℝ :=
  fun xy ↦
    (∑ i : Fin m, ∑ j : Fin n, P.unitServiceCost i j * P.demand i * xy.2 i j) +
      ∑ j : Fin n, P.fixedCost j * xy.1 j

/-- Unfolding equation for the uncapacitated facility location objective of `P`. -/
theorem objectiveValue_def
    {m n : ℕ}
    (P : UncapacitatedFacilityLocation m n)
    (xy : (Fin n → ℝ) × Matrix (Fin m) (Fin n) ℝ) :
    P.objectiveValue xy =
      (∑ i : Fin m, ∑ j : Fin n, P.unitServiceCost i j * P.demand i * xy.2 i j) +
        ∑ j : Fin n, P.fixedCost j * xy.1 j := by
  -- Unfold the objective-value definition.
  rfl

/-- The objective values attained by feasible uncapacitated facility location solutions of `P`. -/
def objectiveValues
    {m n : ℕ}
    (P : UncapacitatedFacilityLocation m n) :
    Set ℝ :=
  P.objectiveValue '' P.feasibleSet

/-- Membership in `P.objectiveValues` means that the value is attained by some feasible choice of
facility-opening variables and assignment variables. -/
theorem mem_objectiveValues_iff_exists_feasible
    {m n : ℕ}
    {P : UncapacitatedFacilityLocation m n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ xy : (Fin n → ℝ) × Matrix (Fin m) (Fin n) ℝ,
        xy ∈ P.feasibleSet ∧ P.objectiveValue xy = r := by
  -- The attained-value set is the image of the objective on the feasible set.
  rfl

end UncapacitatedFacilityLocation
