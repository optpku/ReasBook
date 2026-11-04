/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.Order.Pi
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs

open scoped Matrix

public section

namespace SetPacking

section FeasibleSet

variable {row col : Type} [Fintype col]

/-- The matrix-side set packing feasible region attached to `A` consists of the binary integer
vectors `x` satisfying `A *ᵥ x ≤ 1`. -/
def feasibleSet (A : Matrix row col ℤ) : Set (col → ℤ) :=
  {x | (∀ j, x j = 0 ∨ x j = 1) ∧ A *ᵥ x ≤ (1 : row → ℤ)}

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_definition_2_10/PackingPartitioning.lean

Membership in `SetPacking.feasibleSet A` is exactly the binary condition together with the
packing inequalities `A *ᵥ x ≤ 1`. -/
theorem mem_feasibleSet_iff
    {A : Matrix row col ℤ} {x : col → ℤ} :
    x ∈ feasibleSet A ↔
      (∀ j, x j = 0 ∨ x j = 1) ∧ A *ᵥ x ≤ (1 : row → ℤ) := by
  -- Membership unfolds to the predicate defining the packing feasible set.
  exact Iff.rfl

end FeasibleSet

end SetPacking

namespace SetPartitioning

section FeasibleSet

variable {row col : Type} [Fintype col]

/-- The matrix-side set partitioning feasible region attached to `A` consists of the binary
integer vectors `x` satisfying `A *ᵥ x = 1`. -/
def feasibleSet (A : Matrix row col ℤ) : Set (col → ℤ) :=
  {x | (∀ j, x j = 0 ∨ x j = 1) ∧ A *ᵥ x = (1 : row → ℤ)}

/-- Membership in `SetPartitioning.feasibleSet A` is exactly the binary condition together with
the partitioning equalities `A *ᵥ x = 1`. -/
theorem mem_feasibleSet_iff
    {A : Matrix row col ℤ} {x : col → ℤ} :
    x ∈ feasibleSet A ↔
      (∀ j, x j = 0 ∨ x j = 1) ∧ A *ᵥ x = (1 : row → ℤ) := by
  -- Membership unfolds to the predicate defining the partitioning feasible set.
  exact Iff.rfl

end FeasibleSet

end SetPartitioning
