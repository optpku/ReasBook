/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image

open scoped BigOperators

public section

namespace SetFamilyOptimization

variable {m n : ℕ}

/-- The feasible `0,1` vectors for the set packing problem attached to the family `family`. -/
def packingFeasibleSet (family : Fin m → Finset (Fin n)) : Set (Fin n → ℤ) :=
  {x | (∀ j, x j = 0 ∨ x j = 1) ∧ (∀ i, (family i).sum x ≤ 1)}

/-- Membership in `packingFeasibleSet family` is exactly the binary condition together with the
packing inequalities `∑ j in family i, x j ≤ 1`. -/
theorem mem_packingFeasibleSet_iff
    {family : Fin m → Finset (Fin n)} {x : Fin n → ℤ} :
    x ∈ packingFeasibleSet family ↔
      (∀ j, x j = 0 ∨ x j = 1) ∧ (∀ i, (family i).sum x ≤ 1) := Iff.rfl

/-- The feasible `0,1` vectors for the set partitioning problem attached to the family `family`.
-/
def partitioningFeasibleSet (family : Fin m → Finset (Fin n)) : Set (Fin n → ℤ) :=
  {x | (∀ j, x j = 0 ∨ x j = 1) ∧ (∀ i, (family i).sum x = 1)}

/-- Membership in `partitioningFeasibleSet family` is exactly the binary condition together with
the partitioning equalities `∑ j in family i, x j = 1`. -/
theorem mem_partitioningFeasibleSet_iff
    {family : Fin m → Finset (Fin n)} {x : Fin n → ℤ} :
    x ∈ partitioningFeasibleSet family ↔
      (∀ j, x j = 0 ∨ x j = 1) ∧ (∀ i, (family i).sum x = 1) := Iff.rfl

/-- The feasible `0,1` vectors for the set covering problem attached to the family `family`. -/
def coveringFeasibleSet (family : Fin m → Finset (Fin n)) : Set (Fin n → ℤ) :=
  {x | (∀ j, x j = 0 ∨ x j = 1) ∧ (∀ i, 1 ≤ (family i).sum x)}

/-- Membership in `coveringFeasibleSet family` is exactly the binary condition together with the
covering inequalities `1 ≤ ∑ j in family i, x j`. -/
theorem mem_coveringFeasibleSet_iff
    {family : Fin m → Finset (Fin n)} {x : Fin n → ℤ} :
    x ∈ coveringFeasibleSet family ↔
      (∀ j, x j = 0 ∨ x j = 1) ∧ (∀ i, 1 ≤ (family i).sum x) := Iff.rfl

/-- The weighted linear objective `x ↦ ∑ j, w j * x j` attached to a weight vector `w`. -/
def objective (w : Fin n → ℝ) (x : Fin n → ℤ) : ℝ :=
  Finset.univ.sum (fun j ↦ w j * (x j : ℝ))

/-- Unfolding equation for `objective w`. -/
theorem objective_def
    (w : Fin n → ℝ) (x : Fin n → ℤ) :
    objective w x = Finset.univ.sum (fun j ↦ w j * (x j : ℝ)) := by
  simp [objective]

/-- The objective values attained by feasible set packing solutions for `family` and `w`. -/
def packingObjectiveValues (family : Fin m → Finset (Fin n)) (w : Fin n → ℝ) : Set ℝ :=
  objective w '' packingFeasibleSet family

/-- Membership in `packingObjectiveValues family w` means that some feasible packing solution
attains that value. -/
theorem mem_packingObjectiveValues_iff
    {family : Fin m → Finset (Fin n)} {w : Fin n → ℝ} {z : ℝ} :
    z ∈ packingObjectiveValues family w ↔
      ∃ x : Fin n → ℤ, x ∈ packingFeasibleSet family ∧ objective w x = z := Iff.rfl

/-- The objective values attained by feasible set partitioning solutions for `family` and `w`. -/
def partitioningObjectiveValues (family : Fin m → Finset (Fin n)) (w : Fin n → ℝ) : Set ℝ :=
  objective w '' partitioningFeasibleSet family

/-- Membership in `partitioningObjectiveValues family w` means that some feasible partitioning
solution attains that value. -/
theorem mem_partitioningObjectiveValues_iff
    {family : Fin m → Finset (Fin n)} {w : Fin n → ℝ} {z : ℝ} :
    z ∈ partitioningObjectiveValues family w ↔
      ∃ x : Fin n → ℤ, x ∈ partitioningFeasibleSet family ∧ objective w x = z := Iff.rfl

/-- The objective values attained by feasible set covering solutions for `family` and `w`. -/
def coveringObjectiveValues (family : Fin m → Finset (Fin n)) (w : Fin n → ℝ) : Set ℝ :=
  objective w '' coveringFeasibleSet family

/-- Membership in `coveringObjectiveValues family w` means that some feasible covering solution
attains that value. -/
theorem mem_coveringObjectiveValues_iff
    {family : Fin m → Finset (Fin n)} {w : Fin n → ℝ} {z : ℝ} :
    z ∈ coveringObjectiveValues family w ↔
      ∃ x : Fin n → ℤ, x ∈ coveringFeasibleSet family ∧ objective w x = z := Iff.rfl

end SetFamilyOptimization
