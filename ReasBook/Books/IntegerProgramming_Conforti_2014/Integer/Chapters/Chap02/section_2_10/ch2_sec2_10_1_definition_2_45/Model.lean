/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Image

public section

open scoped BigOperators

universe u v

/-- A capacitated facility location instance with customer demands, facility capacities, fixed
opening costs, and unit transportation costs. -/
structure CapacitatedFacilityLocation (Customer : Type u) (Facility : Type v) where
  demand : Customer → ℝ
  capacity : Facility → ℝ
  fixedCost : Facility → ℝ
  unitServiceCost : Matrix Customer Facility ℝ
  demand_nonneg : ∀ i, 0 ≤ demand i
  capacity_nonneg : ∀ j, 0 ≤ capacity j
  fixedCost_nonneg : ∀ j, 0 ≤ fixedCost j
  unitServiceCost_nonneg : ∀ i j, 0 ≤ unitServiceCost i j

namespace CapacitatedFacilityLocation

variable {Customer : Type u} {Facility : Type v}
variable [Fintype Customer] [Fintype Facility]

/-- Construct a capacitated facility location instance from its demand, capacity, fixed-cost, and
unit-service-cost data. -/
def ofData
    (demand : Customer → ℝ)
    (capacity : Facility → ℝ)
    (fixedCost : Facility → ℝ)
    (unitServiceCost : Matrix Customer Facility ℝ)
    (h_demand_nonneg : ∀ i, 0 ≤ demand i)
    (h_capacity_nonneg : ∀ j, 0 ≤ capacity j)
    (h_fixedCost_nonneg : ∀ j, 0 ≤ fixedCost j)
    (h_unitServiceCost_nonneg : ∀ i j, 0 ≤ unitServiceCost i j) :
    CapacitatedFacilityLocation Customer Facility :=
  { demand := demand
    capacity := capacity
    fixedCost := fixedCost
    unitServiceCost := unitServiceCost
    demand_nonneg := h_demand_nonneg
    capacity_nonneg := h_capacity_nonneg
    fixedCost_nonneg := h_fixedCost_nonneg
    unitServiceCost_nonneg := h_unitServiceCost_nonneg }

/-- The feasible opening vectors and assignment matrices `(x, y)` of `P`: every customer is
assigned in total fraction `1`, every facility satisfies the weighted capacity inequality,
assignment variables are nonnegative, and opening variables are binary. -/
@[expose]
def feasibleSet
    (P : CapacitatedFacilityLocation Customer Facility) :
    Set ((Facility → ℝ) × Matrix Customer Facility ℝ) :=
  { xy |
      (∀ i : Customer, ∑ j : Facility, xy.2 i j = 1) ∧
      (∀ j : Facility, ∑ i : Customer, P.demand i * xy.2 i j ≤ P.capacity j * xy.1 j) ∧
      (∀ i : Customer, ∀ j : Facility, 0 ≤ xy.2 i j) ∧
      (∀ j : Facility, xy.1 j = 0 ∨ xy.1 j = 1) }

/-- Membership in `P.feasibleSet` is exactly the conjunction of the displayed assignment,
capacity, nonnegativity, and binary-opening constraints. -/
theorem mem_feasibleSet_iff
    (P : CapacitatedFacilityLocation Customer Facility)
    (xy : (Facility → ℝ) × Matrix Customer Facility ℝ) :
    xy ∈ P.feasibleSet ↔
      (∀ i : Customer, ∑ j : Facility, xy.2 i j = 1) ∧
      (∀ j : Facility, ∑ i : Customer, P.demand i * xy.2 i j ≤ P.capacity j * xy.1 j) ∧
      (∀ i : Customer, ∀ j : Facility, 0 ≤ xy.2 i j) ∧
      (∀ j : Facility, xy.1 j = 0 ∨ xy.1 j = 1) :=
  Iff.rfl

/-- A feasible capacitated facility location solution assigns each customer row total fraction
`1`. -/
theorem feasible_rowSum_eq_one
    (P : CapacitatedFacilityLocation Customer Facility)
    {x : Facility → ℝ}
    {y : Matrix Customer Facility ℝ}
    (hxy : (x, y) ∈ P.feasibleSet)
    (i : Customer) :
    ∑ j : Facility, y i j = 1 :=
  ((mem_feasibleSet_iff P (x, y)).mp hxy).1 i

/-- A feasible capacitated facility location solution satisfies the weighted capacity
inequalities `∑ i, P.demand i * y i j ≤ P.capacity j * x j`. -/
theorem feasible_columnDemand_le_capacityOpen
    (P : CapacitatedFacilityLocation Customer Facility)
    {x : Facility → ℝ}
    {y : Matrix Customer Facility ℝ}
    (hxy : (x, y) ∈ P.feasibleSet)
    (j : Facility) :
    ∑ i : Customer, P.demand i * y i j ≤ P.capacity j * x j :=
  ((mem_feasibleSet_iff P (x, y)).mp hxy).2.1 j

/-- Every assignment variable of a feasible capacitated facility location solution is
nonnegative. -/
theorem feasible_assignment_nonneg
    (P : CapacitatedFacilityLocation Customer Facility)
    {x : Facility → ℝ}
    {y : Matrix Customer Facility ℝ}
    (hxy : (x, y) ∈ P.feasibleSet)
    (i : Customer)
    (j : Facility) :
    0 ≤ y i j :=
  ((mem_feasibleSet_iff P (x, y)).mp hxy).2.2.1 i j

/-- Every facility-opening variable of a feasible capacitated facility location solution is
binary. -/
theorem feasible_open_binary
    (P : CapacitatedFacilityLocation Customer Facility)
    {x : Facility → ℝ}
    {y : Matrix Customer Facility ℝ}
    (hxy : (x, y) ∈ P.feasibleSet)
    (j : Facility) :
    x j = 0 ∨ x j = 1 :=
  ((mem_feasibleSet_iff P (x, y)).mp hxy).2.2.2 j

/-- The capacitated facility location objective value of `(x, y)` is the displayed shipping-cost
double sum plus the facility-opening-cost sum. -/
@[expose]
def objectiveValue
    (P : CapacitatedFacilityLocation Customer Facility) :
    ((Facility → ℝ) × Matrix Customer Facility ℝ) → ℝ :=
  fun xy ↦
    (∑ i : Customer, ∑ j : Facility, P.unitServiceCost i j * P.demand i * xy.2 i j) +
      ∑ j : Facility, P.fixedCost j * xy.1 j

/-- Unfolding equation for the capacitated facility location objective of `P`. -/
theorem objectiveValue_def
    (P : CapacitatedFacilityLocation Customer Facility)
    (xy : (Facility → ℝ) × Matrix Customer Facility ℝ) :
    P.objectiveValue xy =
      (∑ i : Customer, ∑ j : Facility, P.unitServiceCost i j * P.demand i * xy.2 i j) +
        ∑ j : Facility, P.fixedCost j * xy.1 j :=
  rfl

/-- The objective values attained by feasible capacitated facility location solutions of `P`. -/
def objectiveValues
    (P : CapacitatedFacilityLocation Customer Facility) :
    Set ℝ :=
  P.objectiveValue '' P.feasibleSet

/-- Membership in `P.objectiveValues` means that the value is attained by some feasible choice of
facility-opening variables `x` and assignment variables `y`. -/
theorem mem_objectiveValues_iff_exists_feasible
    (P : CapacitatedFacilityLocation Customer Facility)
    (r : ℝ) :
    r ∈ P.objectiveValues ↔
      ∃ xy : (Facility → ℝ) × Matrix Customer Facility ℝ,
        xy ∈ P.feasibleSet ∧ P.objectiveValue xy = r :=
  Iff.rfl

end CapacitatedFacilityLocation
