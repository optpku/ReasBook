/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_1_extra_1
import Mathlib.Order.Filter.Extr

noncomputable section

section

local notation "Point" => EuclideanSpace ℝ (Fin 2)

-- Semantic recall: `lean_leansearch` surfaced `IsMinOn` as the canonical minimizer API, and
-- nearby Chapter 10 example files keep concrete `ℝ²` objectives, constrained-problem owners,
-- and optimizer points explicit on `Point = EuclideanSpace ℝ (Fin 2)`.

/-- The objective in Exercise 10.2 is `x ↦ -x 0^2 - x 1^2`. -/
def chapter10Exercise102Objective (x : Point) : ℝ :=
  -(x 0) ^ (2 : ℕ) - (x 1) ^ (2 : ℕ)

/-- The three inequality constraints in Exercise 10.2 are `8 - x 0`, `8 - x 1`, and
`x 0 + x 1 - 1`. -/
def chapter10Exercise102Constraint (i : Fin 3) (x : Point) : ℝ :=
  match i.1 with
  | 0 => 8 - x 0
  | 1 => 8 - x 1
  | _ => x 0 + x 1 - 1

/-- Exercise 10.2 as the chapter's canonical `StandardPenaltyProblem`: there are no equality
constraints, and the three inequality constraints are `8 - x 0`, `8 - x 1`, and
`x 0 + x 1 - 1`. -/
def chapter10Exercise102Problem : StandardPenaltyProblem 2 3 where
  eqCount := 0
  eqCount_le := Nat.zero_le 3
  objective := chapter10Exercise102Objective
  constraint := chapter10Exercise102Constraint

/-- The strict feasible set used by the inverse penalty method replaces the weak inequalities by
`x 0 < 8`, `x 1 < 8`, and `1 < x 0 + x 1`. -/
def chapter10Exercise102StrictFeasibleSet : Set Point :=
  {x | x 0 < 8 ∧ x 1 < 8 ∧ 1 < x 0 + x 1}

/-- Feasibility in `chapter10Exercise102Problem.feasibleSet` is exactly the source system
`x 0 ≤ 8`, `x 1 ≤ 8`, and `1 ≤ x 0 + x 1`. -/
theorem chapter10Exercise102_mem_feasibleSet_iff (x : Point) :
    x ∈ chapter10Exercise102Problem.feasibleSet ↔ x 0 ≤ 8 ∧ x 1 ≤ 8 ∧ 1 ≤ x 0 + x 1 := by
  rw [StandardPenaltyProblem.mem_feasibleSet_iff]
  simp [chapter10Exercise102Problem, chapter10Exercise102Constraint, Fin.forall_fin_succ,
    sub_nonneg]

/-- Strict feasibility in `chapter10Exercise102StrictFeasibleSet` is exactly the source system
`x 0 < 8`, `x 1 < 8`, and `1 < x 0 + x 1`. -/
theorem chapter10Exercise102_mem_strictFeasibleSet_iff (x : Point) :
    x ∈ chapter10Exercise102StrictFeasibleSet ↔ x 0 < 8 ∧ x 1 < 8 ∧ 1 < x 0 + x 1 :=
  Iff.rfl

/-- The initial point given in Exercise 10.2 is `(2, 2)ᵀ`. -/
def chapter10Exercise102InitialPoint : Point :=
  EuclideanSpace.single 0 (2 : ℝ) + EuclideanSpace.single 1 (2 : ℝ)

/-- The constrained optimizer for Exercise 10.2 is `(8, 8)ᵀ`. -/
def chapter10Exercise102Solution : Point :=
  EuclideanSpace.single 0 (8 : ℝ) + EuclideanSpace.single 1 (8 : ℝ)

#print axioms chapter10Exercise102Problem
#print axioms chapter10Exercise102InitialPoint
#print axioms chapter10Exercise102Solution

/-- The initial point `(2, 2)ᵀ` lies in the strict feasible set used by the inverse penalty
method for Exercise 10.2. -/
theorem chapter10Exercise102InitialPoint_mem_strictFeasibleSet :
    chapter10Exercise102InitialPoint ∈ chapter10Exercise102StrictFeasibleSet := by
  rw [chapter10Exercise102_mem_strictFeasibleSet_iff]
  norm_num [chapter10Exercise102InitialPoint]

/-- Every strict feasible point is feasible for Exercise 10.2. -/
theorem chapter10Exercise102StrictFeasibleSet_subset_feasibleSet :
    chapter10Exercise102StrictFeasibleSet ⊆ chapter10Exercise102Problem.feasibleSet := by
  intro x hx
  rcases (chapter10Exercise102_mem_strictFeasibleSet_iff x).1 hx with ⟨hx0, hx1, hsum⟩
  exact (chapter10Exercise102_mem_feasibleSet_iff x).2
    ⟨le_of_lt hx0, le_of_lt hx1, le_of_lt hsum⟩

/-- The source initial point `(2, 2)ᵀ` is feasible for the constrained problem. -/
theorem chapter10Exercise102InitialPoint_mem_feasibleSet :
    chapter10Exercise102InitialPoint ∈ chapter10Exercise102Problem.feasibleSet :=
  chapter10Exercise102StrictFeasibleSet_subset_feasibleSet
    chapter10Exercise102InitialPoint_mem_strictFeasibleSet

/-- Helper for Chapter10 Exercise 10.2: every feasible point satisfies the coordinate bounds
`-7 ≤ x 0 ≤ 8` and `-7 ≤ x 1 ≤ 8`. -/
theorem chapter10Exercise102_coord_bounds_of_mem_feasibleSet
    {x : Point} (hx : x ∈ chapter10Exercise102Problem.feasibleSet) :
    -7 ≤ x 0 ∧ x 0 ≤ 8 ∧ -7 ≤ x 1 ∧ x 1 ≤ 8 := by
  -- Unpack the source inequalities and recover the lower bounds from the sum constraint.
  rcases (chapter10Exercise102_mem_feasibleSet_iff x).1 hx with ⟨hx0_le, hx1_le, hsum⟩
  have hx0_ge : -7 ≤ x 0 := by
    linarith
  have hx1_ge : -7 ≤ x 1 := by
    linarith
  exact ⟨hx0_ge, hx0_le, hx1_ge, hx1_le⟩

/-- Helper for Chapter10 Exercise 10.2: the objective gap from a feasible point to `(8, 8)ᵀ`
factors into the two boundary-gap terms. -/
theorem chapter10Exercise102_objective_sub_solution (x : Point) :
    chapter10Exercise102Problem.objective x -
        chapter10Exercise102Problem.objective chapter10Exercise102Solution =
      (8 - x 0) * (8 + x 0) + (8 - x 1) * (8 + x 1) := by
  -- Expand the objective at the candidate point `(8, 8)` and collect the quadratic gaps.
  norm_num
    [chapter10Exercise102Problem, chapter10Exercise102Objective, chapter10Exercise102Solution]
  ring

/-- Helper for Chapter10 Exercise 10.2: among feasible points, `(8, 8)ᵀ` has objective value no
larger than any competitor. -/
theorem chapter10Exercise102_solution_objective_le_of_mem_feasibleSet
    {x : Point} (hx : x ∈ chapter10Exercise102Problem.feasibleSet) :
    chapter10Exercise102Problem.objective chapter10Exercise102Solution ≤
      chapter10Exercise102Problem.objective x := by
  -- The factored gap is a sum of two nonnegative boundary terms on the feasible set.
  rcases chapter10Exercise102_coord_bounds_of_mem_feasibleSet hx with
    ⟨hx0_ge, hx0_le, hx1_ge, hx1_le⟩
  have hterm0_nonneg : 0 ≤ (8 - x 0) * (8 + x 0) := by
    have hleft : 0 ≤ 8 - x 0 := sub_nonneg.mpr hx0_le
    have hright : 0 ≤ 8 + x 0 := by
      linarith
    exact mul_nonneg hleft hright
  have hterm1_nonneg : 0 ≤ (8 - x 1) * (8 + x 1) := by
    have hleft : 0 ≤ 8 - x 1 := sub_nonneg.mpr hx1_le
    have hright : 0 ≤ 8 + x 1 := by
      linarith
    exact mul_nonneg hleft hright
  have hdiff_nonneg :
      0 ≤ chapter10Exercise102Problem.objective x -
        chapter10Exercise102Problem.objective chapter10Exercise102Solution := by
    rw [chapter10Exercise102_objective_sub_solution]
    exact add_nonneg hterm0_nonneg hterm1_nonneg
  linarith

/-- Helper for Chapter10 Exercise 10.2: if a feasible point has the same objective value as
`(8, 8)ᵀ`, then the point itself must be `(8, 8)ᵀ`. -/
theorem chapter10Exercise102_eq_solution_of_mem_feasibleSet_of_objective_eq
    {x : Point} (hx : x ∈ chapter10Exercise102Problem.feasibleSet)
    (hobj :
      chapter10Exercise102Problem.objective x =
        chapter10Exercise102Problem.objective chapter10Exercise102Solution) :
    x = chapter10Exercise102Solution := by
  -- Equality in the factored objective gap forces both nonnegative summands to vanish.
  rcases chapter10Exercise102_coord_bounds_of_mem_feasibleSet hx with
    ⟨hx0_ge, hx0_le, hx1_ge, hx1_le⟩
  have hterm0_nonneg : 0 ≤ (8 - x 0) * (8 + x 0) := by
    have hleft : 0 ≤ 8 - x 0 := sub_nonneg.mpr hx0_le
    have hright : 0 ≤ 8 + x 0 := by
      linarith
    exact mul_nonneg hleft hright
  have hterm1_nonneg : 0 ≤ (8 - x 1) * (8 + x 1) := by
    have hleft : 0 ≤ 8 - x 1 := sub_nonneg.mpr hx1_le
    have hright : 0 ≤ 8 + x 1 := by
      linarith
    exact mul_nonneg hleft hright
  have hsum_eq_zero :
      (8 - x 0) * (8 + x 0) + (8 - x 1) * (8 + x 1) = 0 := by
    calc
      (8 - x 0) * (8 + x 0) + (8 - x 1) * (8 + x 1) =
          chapter10Exercise102Problem.objective x -
            chapter10Exercise102Problem.objective chapter10Exercise102Solution := by
        symm
        exact chapter10Exercise102_objective_sub_solution x
      _ = 0 := by
        linarith
  have hterm0_le_zero : (8 - x 0) * (8 + x 0) ≤ 0 := by
    calc
      (8 - x 0) * (8 + x 0) ≤
          (8 - x 0) * (8 + x 0) + (8 - x 1) * (8 + x 1) :=
        le_add_of_nonneg_right hterm1_nonneg
      _ = 0 := hsum_eq_zero
  have hterm1_le_zero : (8 - x 1) * (8 + x 1) ≤ 0 := by
    calc
      (8 - x 1) * (8 + x 1) ≤
          (8 - x 0) * (8 + x 0) + (8 - x 1) * (8 + x 1) :=
        le_add_of_nonneg_left hterm0_nonneg
      _ = 0 := hsum_eq_zero
  have hterm0_eq_zero : (8 - x 0) * (8 + x 0) = 0 :=
    le_antisymm hterm0_le_zero hterm0_nonneg
  have hterm1_eq_zero : (8 - x 1) * (8 + x 1) = 0 :=
    le_antisymm hterm1_le_zero hterm1_nonneg
  have hx0_plus_pos : 0 < 8 + x 0 := by
    linarith
  have hx1_plus_pos : 0 < 8 + x 1 := by
    linarith
  have hx0_gap_eq_zero : 8 - x 0 = 0 := by
    rcases mul_eq_zero.mp hterm0_eq_zero with hx0_gap_eq_zero | hx0_plus_eq_zero
    · exact hx0_gap_eq_zero
    · exfalso
      linarith
  have hx1_gap_eq_zero : 8 - x 1 = 0 := by
    rcases mul_eq_zero.mp hterm1_eq_zero with hx1_gap_eq_zero | hx1_plus_eq_zero
    · exact hx1_gap_eq_zero
    · exfalso
      linarith
  have hx0_eq : x 0 = 8 := by
    exact (sub_eq_zero.mp hx0_gap_eq_zero).symm
  have hx1_eq : x 1 = 8 := by
    exact (sub_eq_zero.mp hx1_gap_eq_zero).symm
  -- Matching both coordinates identifies the feasible minimizer with `(8, 8)ᵀ`.
  ext i
  fin_cases i
  · simpa [chapter10Exercise102Solution] using hx0_eq
  · simpa [chapter10Exercise102Solution] using hx1_eq

/-- Chapter10 Exercise 10.2: the point `chapter10Exercise102Solution = (8, 8)ᵀ` minimizes
`chapter10Exercise102Problem.objective` on `chapter10Exercise102Problem.feasibleSet`. -/
theorem chapter10Exercise102Solution_isMinOnFeasibleSet :
    IsMinOn
      chapter10Exercise102Problem.objective
      chapter10Exercise102Problem.feasibleSet
      chapter10Exercise102Solution := by
  rw [isMinOn_iff]
  intro x hx
  -- The feasible-set geometry already packages the comparison with every competitor.
  exact chapter10Exercise102_solution_objective_le_of_mem_feasibleSet hx

/-- The constrained optimizer `(8, 8)ᵀ` is feasible for Exercise 10.2. -/
theorem chapter10Exercise102Solution_mem_feasibleSet :
    chapter10Exercise102Solution ∈ chapter10Exercise102Problem.feasibleSet := by
  rw [chapter10Exercise102_mem_feasibleSet_iff]
  norm_num [chapter10Exercise102Solution]

/-- Any minimizer of `chapter10Exercise102Problem.objective` on
`chapter10Exercise102Problem.feasibleSet` agrees with `chapter10Exercise102Solution`. -/
theorem chapter10Exercise102_eq_solution_of_isMinOnFeasibleSet
    {x : Point} (hx : x ∈ chapter10Exercise102Problem.feasibleSet)
    (hmin : IsMinOn
      chapter10Exercise102Problem.objective
      chapter10Exercise102Problem.feasibleSet
      x) :
    x = chapter10Exercise102Solution := by
  -- Compare the two minimizers against each other to force objective equality.
  have hx_le :
      chapter10Exercise102Problem.objective x ≤
        chapter10Exercise102Problem.objective chapter10Exercise102Solution :=
    (isMinOn_iff.mp hmin) _ chapter10Exercise102Solution_mem_feasibleSet
  have hsolution_le :
      chapter10Exercise102Problem.objective chapter10Exercise102Solution ≤
        chapter10Exercise102Problem.objective x :=
    (isMinOn_iff.mp chapter10Exercise102Solution_isMinOnFeasibleSet) _ hx
  have hobj :
      chapter10Exercise102Problem.objective x =
        chapter10Exercise102Problem.objective chapter10Exercise102Solution :=
    le_antisymm hx_le hsolution_le
  -- The equality case of the factored objective gap pins both coordinates at their bounds.
  exact chapter10Exercise102_eq_solution_of_mem_feasibleSet_of_objective_eq hx hobj

end
