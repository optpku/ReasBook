/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Image
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_1.Problem

open scoped BigOperators

/-- A knapsack problem with positive weights, capacity, and objective coefficients. -/
structure KnapsackProblem (n : ℕ) where
  weight : Fin n → ℝ
  capacity : ℝ
  objectiveCoeff : Fin n → ℝ
  weight_pos : ∀ i : Fin n, 0 < weight i

namespace KnapsackProblem

/-- Construct a knapsack problem from its weight vector, capacity, objective coefficients, and
positivity hypothesis. -/
def ofData
    {n : ℕ}
    (weight : Fin n → ℝ)
    (capacity : ℝ)
    (objectiveCoeff : Fin n → ℝ)
    (weight_pos : ∀ i : Fin n, 0 < weight i) :
    KnapsackProblem n :=
  { weight := weight
    capacity := capacity
    objectiveCoeff := objectiveCoeff
    weight_pos := weight_pos }

/-- The feasible integer vectors of `P`, cut out by the nonnegativity and knapsack-capacity
constraints. -/
def feasibleSet
    {n : ℕ}
    (P : KnapsackProblem n) : Set (Fin n → ℤ) :=
  {x | (∀ i : Fin n, 0 ≤ x i) ∧ ∑ i : Fin n, P.weight i * (x i : ℝ) ≤ P.capacity}

/-- Membership in `P.feasibleSet` is exactly the displayed nonnegativity and knapsack-capacity
constraints. -/
theorem mem_feasibleSet_iff
    {n : ℕ}
    {P : KnapsackProblem n}
    {x : Fin n → ℤ} :
    x ∈ P.feasibleSet ↔
      (∀ i : Fin n, 0 ≤ x i) ∧ ∑ i : Fin n, P.weight i * (x i : ℝ) ≤ P.capacity := by
  -- Membership is definitionally the conjunction of the two knapsack constraints.
  rfl

/-- A feasible integer vector for `P` is coordinatewise nonnegative. -/
theorem feasible_nonneg
    {n : ℕ}
    {P : KnapsackProblem n}
    {x : Fin n → ℤ}
    (hx : x ∈ P.feasibleSet)
    (i : Fin n) :
    0 ≤ x i := by
  -- Project the coordinatewise nonnegativity constraint from feasibility.
  exact (mem_feasibleSet_iff.mp hx).1 i

/-- A feasible integer vector for `P` satisfies the weighted-sum capacity inequality. -/
theorem feasible_weightedSum_le
    {n : ℕ}
    {P : KnapsackProblem n}
    {x : Fin n → ℤ}
    (hx : x ∈ P.feasibleSet) :
    ∑ i : Fin n, P.weight i * (x i : ℝ) ≤ P.capacity := by
  -- Project the capacity constraint from feasibility.
  exact (mem_feasibleSet_iff.mp hx).2

/-- The objective value of the integer vector `x` for the knapsack problem `P`. -/
def objectiveValue
    {n : ℕ}
    (P : KnapsackProblem n)
    (x : Fin n → ℤ) : ℝ :=
  ∑ i : Fin n, P.objectiveCoeff i * (x i : ℝ)

/-- Unfolding equation for `P.objectiveValue`. -/
theorem objectiveValue_def
    {n : ℕ}
    (P : KnapsackProblem n)
    (x : Fin n → ℤ) :
    P.objectiveValue x =
      ∑ i : Fin n, P.objectiveCoeff i * (x i : ℝ) := by
  -- This is the defining equation for the objective value.
  rfl

/-- The objective values attained by feasible integer vectors of the knapsack problem `P`. -/
def objectiveValues
    {n : ℕ}
    (P : KnapsackProblem n) : Set ℝ :=
  P.objectiveValue '' P.feasibleSet

/-- Membership in `P.objectiveValues` is equivalent to the existence of a feasible integer vector
attaining that value. -/
theorem mem_objectiveValues_iff_exists_feasible
    {n : ℕ}
    {P : KnapsackProblem n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : Fin n → ℤ, x ∈ P.feasibleSet ∧ P.objectiveValue x = r := by
  -- Membership in the image is precisely an attained objective value.
  rfl

/-- Every feasible integer vector of `P` contributes its objective value to `P.objectiveValues`. -/
theorem objectiveValue_mem_objectiveValues
    {n : ℕ}
    {P : KnapsackProblem n}
    {x : Fin n → ℤ}
    (hx : x ∈ P.feasibleSet) :
    P.objectiveValue x ∈ P.objectiveValues := by
  -- Use the given feasible vector as the image witness.
  exact ⟨x, hx, rfl⟩

/-- View a knapsack problem as the corresponding one-row pure integer linear program. -/
def toPureIntegerLinearProgram
    {n : ℕ}
    (P : KnapsackProblem n) :
    PureIntegerLinearProgram 1 n :=
  PureIntegerLinearProgram.ofCoefficients
    P.objectiveCoeff
    (fun _ i ↦ P.weight i)
    (fun _ ↦ P.capacity)

/-- Casting an integer vector to `ℝ` identifies `P.feasibleSet` with the feasible set of
`P.toPureIntegerLinearProgram`. -/
theorem mem_toPureIntegerLinearProgram_feasibleSet_iff
    {n : ℕ}
    {P : KnapsackProblem n}
    {x : Fin n → ℤ} :
    (fun i ↦ (x i : ℝ)) ∈ P.toPureIntegerLinearProgram.feasibleSet ↔ x ∈ P.feasibleSet := by
  -- Expand the one-row program: its matrix inequality is the knapsack capacity constraint,
  -- while nonnegativity and integrality follow coordinatewise from the integer vector.
  rw [PureIntegerLinearProgram.mem_feasibleSet_iff, mem_feasibleSet_iff]
  constructor
  · rintro ⟨hcapacity, hnonneg, _⟩
    refine ⟨?_, ?_⟩
    · intro i
      simpa only [Pi.zero_apply, Int.cast_nonneg_iff] using hnonneg i
    · simpa [toPureIntegerLinearProgram, PureIntegerLinearProgram.ofCoefficients,
        Matrix.mulVec, dotProduct] using hcapacity (0 : Fin 1)
  · rintro ⟨hnonneg, hcapacity⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simpa [toPureIntegerLinearProgram, PureIntegerLinearProgram.ofCoefficients,
        Matrix.mulVec, dotProduct] using hcapacity
    · intro i
      simpa only [Pi.zero_apply, Int.cast_nonneg_iff] using hnonneg i
    · intro i
      exact ⟨x i, rfl⟩

end KnapsackProblem
