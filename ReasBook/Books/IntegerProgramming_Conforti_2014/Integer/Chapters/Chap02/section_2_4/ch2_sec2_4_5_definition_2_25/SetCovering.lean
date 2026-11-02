module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Data.Set.Image
public import Mathlib.LinearAlgebra.Matrix.RowCol

open scoped BigOperators Matrix

public section

namespace SetCovering

variable {flight schedule : Type} [Fintype schedule]

/-- The set covering feasible region attached to the flight-schedule incidence matrix `A` is
`{x | (∀ j, x j = 0 ∨ x j = 1) ∧ (1 : flight → ℤ) ≤ A *ᵥ x}`. -/
def feasibleSet (A : Matrix flight schedule ℤ) : Set (schedule → ℤ) :=
  {x | (∀ j, x j = 0 ∨ x j = 1) ∧ (1 : flight → ℤ) ≤ A *ᵥ x}

namespace SetCoveringNotation

/-- Source-facing notation for the set covering feasible region of `A`. -/
scoped notation:max "S^C(" A ")" => feasibleSet A

end SetCoveringNotation

open scoped SetCoveringNotation

/-- Membership in `S^C(A)` means that `x` is binary and covers every flight. -/
theorem mem_feasibleSet_iff
    {A : Matrix flight schedule ℤ}
    {x : schedule → ℤ} :
    x ∈ S^C(A) ↔
      (∀ j, x j = 0 ∨ x j = 1) ∧ (1 : flight → ℤ) ≤ A *ᵥ x := by
  -- `S^C(A)` is only notation for `feasibleSet A`, so membership is definitional.
  rfl

/-- The crew-count objective `x ↦ ∑ j, x j` for the set covering formulation. -/
def cardinalityObjective (x : schedule → ℤ) : ℤ :=
  ∑ j, x j

/-- Unfolding equation for `cardinalityObjective`. -/
theorem cardinalityObjective_def
    (x : schedule → ℤ) :
    cardinalityObjective x = ∑ j, x j := by
  -- The objective was defined to be the coordinate sum.
  rfl

/-- The set of objective values attained by feasible solutions in `S^C(A)`. -/
def objectiveValues (A : Matrix flight schedule ℤ) : Set ℤ :=
  cardinalityObjective '' feasibleSet A

/-- Membership in `objectiveValues A` means that some vector in `S^C(A)` attains that crew
count. -/
theorem mem_objectiveValues_iff
    {A : Matrix flight schedule ℤ}
    {z : ℤ} :
    z ∈ objectiveValues A ↔
      ∃ x : schedule → ℤ, x ∈ S^C(A) ∧ cardinalityObjective x = z := by
  -- Unfold the image set and rewrite membership as the existence of a feasible witness.
  simp [objectiveValues]

end SetCovering
