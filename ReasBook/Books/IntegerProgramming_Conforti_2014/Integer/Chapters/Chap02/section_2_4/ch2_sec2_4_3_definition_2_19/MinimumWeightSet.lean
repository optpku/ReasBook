/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image

open scoped BigOperators

public section

namespace MinimumWeightSet

variable {n : ℕ}

/-- The objective value of a subset `S ⊆ {1, ..., n}` for the nonnegative weight vector `w`. -/
def objective (w : Fin n → NNReal) (S : Finset (Fin n)) : NNReal :=
  S.sum w

/-- Unfolding equation for `objective`. -/
theorem objective_def
    (w : Fin n → NNReal) (S : Finset (Fin n)) :
    objective w S = S.sum w :=
  by simp [objective]

/-- The objective is monotone with respect to inclusion of subsets. -/
theorem objective_mono (w : Fin n → NNReal) : Monotone (objective w) := by
  intro S T hST
  simpa [objective_def] using Finset.sum_le_sum_of_subset hST

/-- The objective values attained by members of the family `R`. -/
def objectiveValues (w : Fin n → NNReal) (R : Set (Finset (Fin n))) : Set NNReal :=
  objective w '' R

/-- Membership in `objectiveValues w R` means that some set in `R` attains that objective value. -/
theorem mem_objectiveValues_iff
    {w : Fin n → NNReal} {R : Set (Finset (Fin n))} {z : NNReal} :
    z ∈ objectiveValues w R ↔
      ∃ S : Finset (Fin n), S ∈ R ∧ objective w S = z :=
  Iff.rfl

/-- A set `S` solves the minimum-weight set problem over `R` when it belongs to `R` and has
least objective value in the attained-value set `objectiveValues w R`. -/
def IsOptimal
    (w : Fin n → NNReal) (R : Set (Finset (Fin n))) (S : Finset (Fin n)) : Prop :=
  S ∈ R ∧ IsLeast (objectiveValues w R) (objective w S)

/-- Unfolding characterization of optimality for the minimum-weight set problem over `R`. -/
theorem isOptimal_iff
    {w : Fin n → NNReal} {R : Set (Finset (Fin n))} {S : Finset (Fin n)} :
    IsOptimal w R S ↔
      S ∈ R ∧ ∀ T ∈ R, objective w S ≤ objective w T := by
  constructor
  · rintro ⟨hS, hleast⟩
    refine ⟨hS, ?_⟩
    intro T hT
    exact hleast.2 ⟨T, hT, rfl⟩
  · rintro ⟨hS, hmin⟩
    refine ⟨hS, ?_⟩
    refine ⟨⟨S, hS, rfl⟩, ?_⟩
    rintro _ ⟨T, hT, rfl⟩
    exact hmin T hT

/-- A nonempty feasible family has an optimal member. -/
theorem exists_isOptimal
    (w : Fin n → NNReal) {R : Set (Finset (Fin n))} (hR : R.Nonempty) :
    ∃ S : Finset (Fin n), IsOptimal w R S := by
  obtain ⟨S, hS⟩ := (Set.toFinite R).exists_minimalFor (objective w) R hR
  refine ⟨S, ?_⟩
  rw [isOptimal_iff]
  exact ⟨hS.1, fun T hT ↦ hS.le hT⟩

/-- An optimal set belongs to the feasible family `R`. -/
theorem IsOptimal.mem
    {w : Fin n → NNReal} {R : Set (Finset (Fin n))} {S : Finset (Fin n)}
    (hS : IsOptimal w R S) :
    S ∈ R :=
  hS.1

/-- The objective value of an optimal set is a least element of `objectiveValues w R`. -/
theorem IsOptimal.isLeast
    {w : Fin n → NNReal} {R : Set (Finset (Fin n))} {S : Finset (Fin n)}
    (hS : IsOptimal w R S) :
    IsLeast (objectiveValues w R) (objective w S) :=
  hS.2

/-- The objective value of an optimal set belongs to the attained-value set. -/
theorem IsOptimal.objective_mem_objectiveValues
    {w : Fin n → NNReal} {R : Set (Finset (Fin n))} {S : Finset (Fin n)}
    (hS : IsOptimal w R S) :
    objective w S ∈ objectiveValues w R :=
  hS.isLeast.1

/-- An optimal set has objective value at most that of every member of `R`. -/
theorem IsOptimal.objective_le
    {w : Fin n → NNReal} {R : Set (Finset (Fin n))} {S T : Finset (Fin n)}
    (hS : IsOptimal w R S) (hT : T ∈ R) :
    objective w S ≤ objective w T :=
  hS.isLeast.2 ⟨T, hT, rfl⟩

/-- Any feasible subset of an optimal set is again optimal. -/
theorem IsOptimal.of_subset
    {w : Fin n → NNReal} {R : Set (Finset (Fin n))} {S T : Finset (Fin n)}
    (hS : IsOptimal w R S) (hT : T ∈ R) (hTS : T ⊆ S) :
    IsOptimal w R T := by
  have hTS_le : objective w T ≤ objective w S := (objective_mono w) hTS
  have hST_le : objective w S ≤ objective w T := hS.objective_le hT
  have hObj : objective w T = objective w S := le_antisymm hTS_le hST_le
  refine ⟨hT, ?_⟩
  simpa [hObj] using hS.isLeast

end MinimumWeightSet
