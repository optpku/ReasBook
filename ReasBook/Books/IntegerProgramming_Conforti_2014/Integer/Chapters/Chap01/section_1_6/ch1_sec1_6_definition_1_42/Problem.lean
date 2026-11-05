/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Image
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Order.Bounds.Defs

open scoped Matrix

public section

variable {m n : ℕ}

/-- A bounded integer program consists of an integral objective vector, an integral equality
constraint system, and integral lower and upper bounds on the decision vector.

This item is recorded under the label
`remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_definition_1_42/Problem.lean`. -/
structure BoundedIntegerProgram (m n : ℕ) where
  objective : Fin n → ℤ
  constraintMatrix : Matrix (Fin m) (Fin n) ℤ
  constraintRhs : Fin m → ℤ
  lowerBound : Fin n → ℤ
  upperBound : Fin n → ℤ

namespace BoundedIntegerProgram

/-- Construct a bounded integer program from its objective, equality-constraint, and bound data.
-/
def ofCoefficients
    (objective : Fin n → ℤ)
    (constraintMatrix : Matrix (Fin m) (Fin n) ℤ)
    (constraintRhs : Fin m → ℤ)
    (lowerBound upperBound : Fin n → ℤ) :
    BoundedIntegerProgram m n :=
  { objective := objective
    constraintMatrix := constraintMatrix
    constraintRhs := constraintRhs
    lowerBound := lowerBound
    upperBound := upperBound }

/-- The feasible set of `P` consists of the integer vectors satisfying the equality constraints
and coordinatewise box bounds. -/
def feasibleSet
    (P : BoundedIntegerProgram m n) : Set (Fin n → ℤ) :=
  {x | P.constraintMatrix *ᵥ x = P.constraintRhs ∧ P.lowerBound ≤ x ∧ x ≤ P.upperBound}

/-- Membership in `P.feasibleSet` is exactly the displayed system
`P.constraintMatrix *ᵥ x = P.constraintRhs`, `P.lowerBound ≤ x`, and `x ≤ P.upperBound`. -/
theorem mem_feasibleSet_iff
    (P : BoundedIntegerProgram m n)
    (x : Fin n → ℤ) :
    x ∈ P.feasibleSet ↔
      P.constraintMatrix *ᵥ x = P.constraintRhs ∧
        P.lowerBound ≤ x ∧ x ≤ P.upperBound := by
  -- Unfold `feasibleSet`; membership is definitionally the displayed conjunction.
  rfl

/-- The objective value of `x` for the bounded integer program `P` is the dot product
`P.objective ⬝ᵥ x`. -/
def objectiveValue
    (P : BoundedIntegerProgram m n)
    (x : Fin n → ℤ) : ℤ :=
  P.objective ⬝ᵥ x

/-- Unfolding equation for `P.objectiveValue`. -/
theorem objectiveValue_def
    (P : BoundedIntegerProgram m n)
    (x : Fin n → ℤ) :
    P.objectiveValue x = P.objective ⬝ᵥ x := by
  -- Unfold `objectiveValue` to expose the defining dot product.
  rfl

/-- The set of objective values attained by feasible integer vectors of `P`. -/
def objectiveValues
    (P : BoundedIntegerProgram m n) : Set ℤ :=
  P.objectiveValue '' P.feasibleSet

/-- Membership in `P.objectiveValues` means that some feasible integer vector of `P` attains the
value. -/
theorem mem_objectiveValues_iff
    (P : BoundedIntegerProgram m n)
    (z : ℤ) :
    z ∈ P.objectiveValues ↔ ∃ x : Fin n → ℤ, x ∈ P.feasibleSet ∧ P.objectiveValue x = z := by
  -- Unfold `objectiveValues`; image membership is exactly the existential witness form.
  rfl

/-- An integer vector is optimal for `P` when it is feasible and its objective value is least in
the attained-value set `P.objectiveValues`. -/
def isOptimalSolution
    (P : BoundedIntegerProgram m n)
    (x : Fin n → ℤ) : Prop :=
  x ∈ P.feasibleSet ∧ IsLeast P.objectiveValues (P.objectiveValue x)

/-- The bounded-integer-program optimality predicate unfolds to feasibility together with least
attained objective value. -/
theorem isOptimalSolution_iff
    (P : BoundedIntegerProgram m n)
    (x : Fin n → ℤ) :
    P.isOptimalSolution x ↔
      x ∈ P.feasibleSet ∧ IsLeast P.objectiveValues (P.objectiveValue x) := by
  -- Unfold `isOptimalSolution`; the predicate is defined by this conjunction.
  rfl

namespace isOptimalSolution

/-- An optimal solution of `P` belongs to `P.feasibleSet`. -/
theorem mem_feasibleSet
    {P : BoundedIntegerProgram m n}
    {x : Fin n → ℤ}
    (hx : P.isOptimalSolution x) :
    x ∈ P.feasibleSet := by
  -- Project the feasibility component from the optimality conjunction.
  exact hx.1

/-- An optimal solution of `P` attains a least element of `P.objectiveValues`. -/
theorem objectiveIsLeast
    {P : BoundedIntegerProgram m n}
    {x : Fin n → ℤ}
    (hx : P.isOptimalSolution x) :
    IsLeast P.objectiveValues (P.objectiveValue x) := by
  -- Project the least-value component from the optimality conjunction.
  exact hx.2

end isOptimalSolution

/-- `P` has an optimal solution when some feasible integer vector of `P` attains a least value in
`P.objectiveValues`. -/
def hasOptimalSolution
    (P : BoundedIntegerProgram m n) : Prop :=
  ∃ x, P.isOptimalSolution x

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_definition_1_42/Problem.lean

The bounded integer program `P` has an optimal solution exactly when some integer vector
satisfies `P.isOptimalSolution`. -/
theorem hasOptimalSolution_iff
    (P : BoundedIntegerProgram m n) :
    P.hasOptimalSolution ↔ ∃ x, P.isOptimalSolution x := by
  -- Unfold `hasOptimalSolution`; it is defined by the displayed existential.
  rfl

end BoundedIntegerProgram

end
