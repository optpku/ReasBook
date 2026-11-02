module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Image

public section

open scoped BigOperators

namespace UncapacitatedFacilityLocation

/-- A disaggregated uncapacitated facility location instance with customer demands, facility
opening costs, and unit service costs. -/
structure Disaggregated (m n : ℕ) where
  demand : Fin m → ℝ
  fixedCost : Fin n → ℝ
  unitServiceCost : Matrix (Fin m) (Fin n) ℝ
  demand_nonneg : ∀ i, 0 ≤ demand i
  fixedCost_nonneg : ∀ j, 0 ≤ fixedCost j
  unitServiceCost_nonneg : ∀ i j, 0 ≤ unitServiceCost i j

namespace Disaggregated

/-- Construct a disaggregated uncapacitated facility location instance from its demand, opening
cost, and unit-service-cost data. -/
def ofData
    {m n : ℕ}
    (demand : Fin m → ℝ)
    (fixedCost : Fin n → ℝ)
    (unitServiceCost : Matrix (Fin m) (Fin n) ℝ)
    (h_demand_nonneg : ∀ i, 0 ≤ demand i)
    (h_fixedCost_nonneg : ∀ j, 0 ≤ fixedCost j)
    (h_unitServiceCost_nonneg : ∀ i j, 0 ≤ unitServiceCost i j) :
    Disaggregated m n :=
  { demand := demand
    fixedCost := fixedCost
    unitServiceCost := unitServiceCost
    demand_nonneg := h_demand_nonneg
    fixedCost_nonneg := h_fixedCost_nonneg
    unitServiceCost_nonneg := h_unitServiceCost_nonneg }

/-- The feasible opening vectors and assignment matrices `(x, y)` of `P`: every customer is
assigned exactly once, assignments are linked to opened facilities, and both `x` and `y` are
binary. -/
def feasibleSet
    {m n : ℕ}
    (P : Disaggregated m n) :
    Set ((Fin n → ℝ) × Matrix (Fin m) (Fin n) ℝ) :=
  let _ := P
  { xy |
      (∀ i : Fin m, ∑ j : Fin n, xy.2 i j = 1) ∧
      (∀ i : Fin m, ∀ j : Fin n, xy.2 i j ≤ xy.1 j) ∧
      (∀ i : Fin m, ∀ j : Fin n, xy.2 i j = 0 ∨ xy.2 i j = 1) ∧
      (∀ j : Fin n, xy.1 j = 0 ∨ xy.1 j = 1) }

/-- Membership in `P.feasibleSet` is exactly the conjunction of the displayed assignment,
linking, and binary constraints. -/
theorem mem_feasibleSet_iff
    {m n : ℕ}
    {P : Disaggregated m n}
    {xy : (Fin n → ℝ) × Matrix (Fin m) (Fin n) ℝ} :
    xy ∈ P.feasibleSet ↔
      (∀ i : Fin m, ∑ j : Fin n, xy.2 i j = 1) ∧
      (∀ i : Fin m, ∀ j : Fin n, xy.2 i j ≤ xy.1 j) ∧
      (∀ i : Fin m, ∀ j : Fin n, xy.2 i j = 0 ∨ xy.2 i j = 1) ∧
      (∀ j : Fin n, xy.1 j = 0 ∨ xy.1 j = 1) := by
  -- Unfolding membership exposes exactly the four defining constraints.
  rfl

/-- A feasible disaggregated UFL solution assigns each customer row to exactly one facility. -/
theorem feasible_rowSum_eq_one
    {m n : ℕ}
    {P : Disaggregated m n}
    {x : Fin n → ℝ}
    {y : Matrix (Fin m) (Fin n) ℝ}
    (hxy : (x, y) ∈ P.feasibleSet)
    (i : Fin m) :
    ∑ j : Fin n, y i j = 1 := by
  -- Project the row-sum constraint from the feasible-set characterization.
  exact (mem_feasibleSet_iff.mp hxy).1 i

/-- A feasible disaggregated UFL solution satisfies the linking inequalities `y i j ≤ x j`. -/
theorem feasible_assignment_le_open
    {m n : ℕ}
    {P : Disaggregated m n}
    {x : Fin n → ℝ}
    {y : Matrix (Fin m) (Fin n) ℝ}
    (hxy : (x, y) ∈ P.feasibleSet)
    (i : Fin m)
    (j : Fin n) :
    y i j ≤ x j := by
  -- Project the linking constraint and specialize it to the chosen indices.
  exact (mem_feasibleSet_iff.mp hxy).2.1 i j

/-- Every facility-opening variable of a feasible disaggregated UFL solution is binary. -/
theorem feasible_open_binary
    {m n : ℕ}
    {P : Disaggregated m n}
    {x : Fin n → ℝ}
    {y : Matrix (Fin m) (Fin n) ℝ}
    (hxy : (x, y) ∈ P.feasibleSet)
    (j : Fin n) :
    x j = 0 ∨ x j = 1 := by
  -- Project the opening-variable binary constraint from feasibility.
  exact (mem_feasibleSet_iff.mp hxy).2.2.2 j

/-- Every assignment variable of a feasible disaggregated UFL solution is binary. -/
theorem feasible_assignment_binary
    {m n : ℕ}
    {P : Disaggregated m n}
    {x : Fin n → ℝ}
    {y : Matrix (Fin m) (Fin n) ℝ}
    (hxy : (x, y) ∈ P.feasibleSet)
    (i : Fin m)
    (j : Fin n) :
    y i j = 0 ∨ y i j = 1 := by
  -- Project the assignment-variable binary constraint from feasibility.
  exact (mem_feasibleSet_iff.mp hxy).2.2.1 i j

/-- The disaggregated UFL objective value of `(x, y)` is the displayed shipping-cost double sum
plus the facility-opening-cost sum. -/
def objectiveValue
    {m n : ℕ}
    (P : Disaggregated m n) :
    ((Fin n → ℝ) × Matrix (Fin m) (Fin n) ℝ) → ℝ :=
  fun xy ↦
    (∑ i : Fin m, ∑ j : Fin n, P.unitServiceCost i j * P.demand i * xy.2 i j) +
      ∑ j : Fin n, P.fixedCost j * xy.1 j

/-- Unfolding equation for the disaggregated UFL objective of `P`. -/
theorem objectiveValue_def
    {m n : ℕ}
    (P : Disaggregated m n)
    (xy : (Fin n → ℝ) × Matrix (Fin m) (Fin n) ℝ) :
    P.objectiveValue xy =
      (∑ i : Fin m, ∑ j : Fin n, P.unitServiceCost i j * P.demand i * xy.2 i j) +
        ∑ j : Fin n, P.fixedCost j * xy.1 j := by
  -- The public equation is the defining equation of the objective function.
  rfl

/-- The objective values attained by feasible disaggregated UFL solutions of `P`. -/
def objectiveValues
    {m n : ℕ}
    (P : Disaggregated m n) :
    Set ℝ :=
  P.objectiveValue '' P.feasibleSet

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_10/ch2_sec2_10_1_definition_2_47/Model.lean:
Membership in `P.objectiveValues` means that the value is attained by some feasible choice of
facility-opening variables `x` and assignment variables `y`. -/
theorem mem_objectiveValues_iff_exists_feasible
    {m n : ℕ}
    {P : Disaggregated m n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : Fin n → ℝ, ∃ y : Matrix (Fin m) (Fin n) ℝ,
        (x, y) ∈ P.feasibleSet ∧ P.objectiveValue (x, y) = r := by
  constructor
  · -- Split the product witness supplied by membership in the image.
    rintro ⟨⟨x, y⟩, hxy, hvalue⟩
    exact ⟨x, y, hxy, hvalue⟩
  · -- Repackage the nested witnesses as the product witness required by the image.
    rintro ⟨x, y, hxy, hvalue⟩
    exact ⟨(x, y), hxy, hvalue⟩

end Disaggregated
end UncapacitatedFacilityLocation
