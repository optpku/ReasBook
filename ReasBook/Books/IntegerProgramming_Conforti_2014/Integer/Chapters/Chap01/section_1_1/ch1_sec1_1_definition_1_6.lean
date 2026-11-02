module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace

public section

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

/-- Definition 1.6 (1): the assignment-problem objective with cost matrix `c` evaluated at the
decision matrix `x`. -/
def assignmentProblemObjective {n : ℕ} (c x : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, c i j * x i j

/-- The objective function is the displayed double sum `∑ i, ∑ j, c i j * x i j`. -/
theorem assignmentProblemObjective_eq_sum {n : ℕ} (c x : Matrix (Fin n) (Fin n) ℝ) :
    assignmentProblemObjective c x = ∑ i : Fin n, ∑ j : Fin n, c i j * x i j := by
  simp [assignmentProblemObjective]

/-- The assignment-problem objective is the canonical matrix trace pairing
`Matrix.trace (cᵀ * x)`. -/
theorem assignmentProblemObjective_eq_trace_transpose_mul {n : ℕ}
    (c x : Matrix (Fin n) (Fin n) ℝ) :
    assignmentProblemObjective c x = Matrix.trace (c.transpose * x) := by
  calc
    assignmentProblemObjective c x = ∑ i : Fin n, ∑ j : Fin n, c i j * x i j :=
      assignmentProblemObjective_eq_sum c x
    _ = ∑ j : Fin n, ∑ i : Fin n, c i j * x i j := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin n, ∑ i : Fin n, c.transpose j i * x i j := by
      simp [Matrix.transpose_apply]
    _ = ∑ j : Fin n, (c.transpose * x) j j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [Matrix.mul_apply]
    _ = Matrix.trace (c.transpose * x) := by
      rw [Matrix.trace]
      simp

/-- Definition 1.6 (2): the feasible set of assignment matrices with column sums `1`, row sums
`1`, and entrywise `0/1` values. -/
def assignmentProblemFeasibleSet {n : ℕ} : Set (Matrix (Fin n) (Fin n) ℝ) :=
  (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ)) ∩
    {x | ∀ i j : Fin n, x i j = 0 ∨ x i j = 1}

/-- Membership in `assignmentProblemFeasibleSet` means being doubly stochastic together with the
entrywise `0/1` condition. -/
theorem mem_assignmentProblemFeasibleSet_iff_mem_doublyStochastic_and_zeroOne
    {n : ℕ} {x : Matrix (Fin n) (Fin n) ℝ} :
    x ∈ assignmentProblemFeasibleSet ↔
      x ∈ doublyStochastic ℝ (Fin n) ∧
        ∀ i j : Fin n, x i j = 0 ∨ x i j = 1 := by
  rfl

/-- Membership in `assignmentProblemFeasibleSet` is exactly the displayed row, column, and `0/1`
constraint system. -/
theorem mem_assignmentProblemFeasibleSet_iff {n : ℕ} {x : Matrix (Fin n) (Fin n) ℝ} :
    x ∈ assignmentProblemFeasibleSet ↔
      (∀ j : Fin n, ∑ i : Fin n, x i j = 1) ∧
        (∀ i : Fin n, ∑ j : Fin n, x i j = 1) ∧
        ∀ i j : Fin n, x i j = 0 ∨ x i j = 1 := by
  rw [mem_assignmentProblemFeasibleSet_iff_mem_doublyStochastic_and_zeroOne,
    mem_doublyStochastic_iff_sum]
  constructor
  · rintro ⟨⟨_, hrow, hcol⟩, h01⟩
    exact ⟨hcol, hrow, h01⟩
  · rintro ⟨hcol, hrow, h01⟩
    refine ⟨?_, h01⟩
    refine ⟨fun i j ↦ ?_, hrow, hcol⟩
    rcases h01 i j with hij | hij
    · simp [hij]
    · simp [hij]

/-- Every feasible assignment matrix has row sum `1`. -/
theorem assignmentProblemFeasible_rowSum_eq_one {n : ℕ} {x : Matrix (Fin n) (Fin n) ℝ}
    (hx : x ∈ assignmentProblemFeasibleSet) (i : Fin n) :
    ∑ j : Fin n, x i j = 1 :=
  sum_row_of_mem_doublyStochastic
    ((mem_assignmentProblemFeasibleSet_iff_mem_doublyStochastic_and_zeroOne.1 hx).1) i

/-- Every feasible assignment matrix has column sum `1`. -/
theorem assignmentProblemFeasible_colSum_eq_one {n : ℕ} {x : Matrix (Fin n) (Fin n) ℝ}
    (hx : x ∈ assignmentProblemFeasibleSet) (j : Fin n) :
    ∑ i : Fin n, x i j = 1 :=
  sum_col_of_mem_doublyStochastic
    ((mem_assignmentProblemFeasibleSet_iff_mem_doublyStochastic_and_zeroOne.1 hx).1) j

/-- Every feasible assignment matrix has entrywise `0/1` values. -/
theorem assignmentProblemFeasible_zeroOne {n : ℕ} {x : Matrix (Fin n) (Fin n) ℝ}
    (hx : x ∈ assignmentProblemFeasibleSet) :
    ∀ i j : Fin n, x i j = 0 ∨ x i j = 1 :=
  (mem_assignmentProblemFeasibleSet_iff_mem_doublyStochastic_and_zeroOne.1 hx).2

/-- Every feasible assignment matrix is doubly stochastic, giving the canonical relaxation
bridge. -/
theorem assignmentProblemFeasible_mem_doublyStochastic {n : ℕ} {x : Matrix (Fin n) (Fin n) ℝ}
    (hx : x ∈ assignmentProblemFeasibleSet) :
    x ∈ doublyStochastic ℝ (Fin n) :=
  (mem_assignmentProblemFeasibleSet_iff_mem_doublyStochastic_and_zeroOne.1 hx).1
