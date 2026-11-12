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

/-- A generalized assignment problem with objective coefficients, resource coefficients, and
capacities. -/
structure GeneralizedAssignmentProblem (m n : ℕ) where
  objectiveCoeff : Matrix (Fin m) (Fin n) ℝ
  resourceCoeff : Matrix (Fin m) (Fin n) ℝ
  capacity : Fin n → ℝ

namespace GeneralizedAssignmentProblem

/-- Construct a generalized assignment problem from its objective matrix, resource matrix, and
capacity vector. -/
def ofData
    {m n : ℕ}
    (objectiveCoeff : Matrix (Fin m) (Fin n) ℝ)
    (resourceCoeff : Matrix (Fin m) (Fin n) ℝ)
    (capacity : Fin n → ℝ) :
    GeneralizedAssignmentProblem m n :=
  { objectiveCoeff := objectiveCoeff
    resourceCoeff := resourceCoeff
    capacity := capacity }

/-- The feasible decision matrices of `P`, cut out by the row-sum, capacity, and binary-entry
constraints of the generalized assignment problem. -/
def feasibleSet
    {m n : ℕ}
    (P : GeneralizedAssignmentProblem m n) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  {x |
    (∀ i : Fin m, ∑ j : Fin n, x i j = 1) ∧
      (∀ j : Fin n, ∑ i : Fin m, P.resourceCoeff i j * x i j ≤ P.capacity j) ∧
        ∀ i : Fin m, ∀ j : Fin n, x i j = 0 ∨ x i j = 1}

/-- Membership in `P.feasibleSet` is exactly the conjunction of the displayed row-sum, capacity,
and binary constraints. -/
theorem mem_feasibleSet_iff
    {m n : ℕ}
    {P : GeneralizedAssignmentProblem m n}
    {x : Matrix (Fin m) (Fin n) ℝ} :
    x ∈ P.feasibleSet ↔
      (∀ i : Fin m, ∑ j : Fin n, x i j = 1) ∧
        (∀ j : Fin n, ∑ i : Fin m, P.resourceCoeff i j * x i j ≤ P.capacity j) ∧
          ∀ i : Fin m, ∀ j : Fin n, x i j = 0 ∨ x i j = 1 := by
  -- This is exactly the set-builder predicate used to define `P.feasibleSet`.
  rfl

/-- A feasible generalized-assignment matrix has row sum `1` in every item row. -/
theorem feasible_rowSum_eq_one
    {m n : ℕ}
    {P : GeneralizedAssignmentProblem m n}
    {x : Matrix (Fin m) (Fin n) ℝ}
    (hx : x ∈ P.feasibleSet)
    (i : Fin m) :
    ∑ j : Fin n, x i j = 1 := by
  -- Project the row-sum constraint from the canonical feasible-set normal form.
  exact (mem_feasibleSet_iff.mp hx).1 i

/-- A feasible generalized-assignment matrix satisfies the capacity inequality in every agent
column. -/
theorem feasible_capacity_le
    {m n : ℕ}
    {P : GeneralizedAssignmentProblem m n}
    {x : Matrix (Fin m) (Fin n) ℝ}
    (hx : x ∈ P.feasibleSet)
    (j : Fin n) :
    ∑ i : Fin m, P.resourceCoeff i j * x i j ≤ P.capacity j := by
  -- Project the column-capacity constraint from feasible-set membership.
  exact (mem_feasibleSet_iff.mp hx).2.1 j

/-- Every entry of a feasible generalized-assignment matrix is binary. -/
theorem feasible_binary
    {m n : ℕ}
    {P : GeneralizedAssignmentProblem m n}
    {x : Matrix (Fin m) (Fin n) ℝ}
    (hx : x ∈ P.feasibleSet)
    (i : Fin m)
    (j : Fin n) :
    x i j = 0 ∨ x i j = 1 := by
  -- Project the binary-entry constraint from feasible-set membership.
  exact (mem_feasibleSet_iff.mp hx).2.2 i j

/-- The generalized-assignment objective value of `x` is the displayed double sum of
`P.objectiveCoeff i j * x i j`. -/
def objectiveValue
    {m n : ℕ}
    (P : GeneralizedAssignmentProblem m n)
    (x : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, P.objectiveCoeff i j * x i j

/-- Unfolding equation for `P.objectiveValue`. -/
theorem objectiveValue_def
    {m n : ℕ}
    (P : GeneralizedAssignmentProblem m n)
    (x : Matrix (Fin m) (Fin n) ℝ) :
    P.objectiveValue x =
      ∑ i : Fin m, ∑ j : Fin n, P.objectiveCoeff i j * x i j := by
  -- This theorem records the defining equation of `P.objectiveValue`.
  rfl

/-- The objective values attained by feasible solutions of the generalized assignment problem
`P`. -/
def objectiveValues
    {m n : ℕ}
    (P : GeneralizedAssignmentProblem m n) : Set ℝ :=
  P.objectiveValue '' P.feasibleSet

/-- Foundation-level witness form for membership in `P.objectiveValues`. -/
theorem mem_objectiveValues_iff_exists_feasible
    {m n : ℕ}
    {P : GeneralizedAssignmentProblem m n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : Matrix (Fin m) (Fin n) ℝ, x ∈ P.feasibleSet ∧ P.objectiveValue x = r := by
  -- Unfolding `objectiveValues` rewrites image membership into the witness form.
  rfl

end GeneralizedAssignmentProblem
