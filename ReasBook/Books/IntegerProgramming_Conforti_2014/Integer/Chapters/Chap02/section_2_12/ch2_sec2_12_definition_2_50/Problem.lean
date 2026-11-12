/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Image
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_6

public section

open scoped BigOperators

/-- A quadratic assignment problem with distance matrix `d` and flow matrix `f`. -/
structure QuadraticAssignmentProblem (n : ℕ) where
  distance : Matrix (Fin n) (Fin n) ℝ
  flow : Matrix (Fin n) (Fin n) ℝ

namespace QuadraticAssignmentProblem

/-- Construct a quadratic assignment problem from its distance and flow matrices. -/
def ofData
    {n : ℕ}
    (distance flow : Matrix (Fin n) (Fin n) ℝ) :
    QuadraticAssignmentProblem n :=
  { distance := distance
    flow := flow }

/-- The feasible assignment matrices for `P`; these are exactly the canonical assignment-problem
feasible matrices. -/
def feasibleSet
    {n : ℕ}
    (_ : QuadraticAssignmentProblem n) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  assignmentProblemFeasibleSet

/-- Membership in `P.feasibleSet` is exactly the displayed row-sum, column-sum, and `0/1`
constraint system. -/
theorem mem_feasibleSet_iff
    {n : ℕ}
    {P : QuadraticAssignmentProblem n}
    {x : Matrix (Fin n) (Fin n) ℝ} :
    x ∈ P.feasibleSet ↔
      (∀ j : Fin n, ∑ i : Fin n, x i j = 1) ∧
        (∀ i : Fin n, ∑ j : Fin n, x i j = 1) ∧
        ∀ i j : Fin n, x i j = 0 ∨ x i j = 1 := by
  change x ∈ assignmentProblemFeasibleSet ↔
    (∀ j : Fin n, ∑ i : Fin n, x i j = 1) ∧
      (∀ i : Fin n, ∑ j : Fin n, x i j = 1) ∧
      ∀ i j : Fin n, x i j = 0 ∨ x i j = 1
  exact mem_assignmentProblemFeasibleSet_iff

/-- The quadratic assignment objective of `x` for `P` is the displayed quadruple sum
`∑ i, ∑ j, ∑ k, ∑ ℓ, P.distance i j * P.flow k ℓ * x k i * x ℓ j`. -/
def objectiveValue
    {n : ℕ}
    (P : QuadraticAssignmentProblem n)
    (x : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ ℓ : Fin n,
    P.distance i j * P.flow k ℓ * x k i * x ℓ j

/-- Unfolding equation for `P.objectiveValue`. -/
theorem objectiveValue_eq_sum
    {n : ℕ}
    (P : QuadraticAssignmentProblem n)
    (x : Matrix (Fin n) (Fin n) ℝ) :
    P.objectiveValue x =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ ℓ : Fin n,
        P.distance i j * P.flow k ℓ * x k i * x ℓ j := by
  simp [objectiveValue]

/-- The objective values attained by feasible solutions of the quadratic assignment problem `P`. -/
def objectiveValues
    {n : ℕ}
    (P : QuadraticAssignmentProblem n) : Set ℝ :=
  P.objectiveValue '' P.feasibleSet

/-- Foundation-level witness form for membership in `P.objectiveValues`. -/
theorem mem_objectiveValues_iff_exists_feasible
    {n : ℕ}
    {P : QuadraticAssignmentProblem n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : Matrix (Fin n) (Fin n) ℝ, x ∈ P.feasibleSet ∧ P.objectiveValue x = r := by
  rfl

/-- Every feasible assignment matrix contributes its quadratic objective value to
`P.objectiveValues`. -/
theorem objectiveValue_mem_objectiveValues
    {n : ℕ}
    {P : QuadraticAssignmentProblem n}
    {x : Matrix (Fin n) (Fin n) ℝ}
    (hx : x ∈ P.feasibleSet) :
    P.objectiveValue x ∈ P.objectiveValues :=
  ⟨x, hx, rfl⟩

end QuadraticAssignmentProblem

end
