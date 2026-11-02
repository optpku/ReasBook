module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

open scoped Matrix

/-- The `3 × 5` integer coefficient matrix of the displayed system `(1.24)`. -/
def diophantineFeasibilityMatrix : Matrix (Fin 3) (Fin 5) ℤ :=
  !![(4 : ℤ), 4, 3, 3, 3;
    2, 4, 4, 8, 0;
    5, 7, 0, 0, 5]

/-- The integer right-hand side vector of the displayed system `(1.24)`. -/
def diophantineFeasibilityRhs : Fin 3 → ℤ :=
  ![(3 : ℤ), 2, 2]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_definition_1_49.lean.
Definition 1.49. The Diophantine feasibility problem is the set of integer vectors
`x : Fin 5 → ℤ` satisfying `diophantineFeasibilityMatrix *ᵥ x = diophantineFeasibilityRhs`. -/
def diophantineFeasibilitySolutionSet : Set (Fin 5 → ℤ) :=
  {x | diophantineFeasibilityMatrix *ᵥ x = diophantineFeasibilityRhs}

/-- Evaluating `diophantineFeasibilityMatrix *ᵥ x` gives the three displayed left-hand sides from
`(1.24)`. -/
theorem diophantineFeasibilityMatrix_mulVec
    (x : Fin 5 → ℤ) :
    diophantineFeasibilityMatrix *ᵥ x =
      ![4 * x 0 + 4 * x 1 + 3 * x 2 + 3 * x 3 + 3 * x 4,
        2 * x 0 + 4 * x 1 + 4 * x 2 + 8 * x 3,
        5 * x 0 + 7 * x 1 + 5 * x 4] := by
  -- Reduce the vector identity to the three rows of the fixed matrix.
  funext i
  fin_cases i
  all_goals
    simp [diophantineFeasibilityMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, add_assoc]

/-- Membership in `diophantineFeasibilitySolutionSet` is equivalent to satisfying the three
displayed equations of `(1.24)`. -/
theorem mem_diophantineFeasibilitySolutionSet_iff
    (x : Fin 5 → ℤ) :
    x ∈ diophantineFeasibilitySolutionSet ↔
      4 * x 0 + 4 * x 1 + 3 * x 2 + 3 * x 3 + 3 * x 4 = 3 ∧
        2 * x 0 + 4 * x 1 + 4 * x 2 + 8 * x 3 = 2 ∧
          5 * x 0 + 7 * x 1 + 5 * x 4 = 2 := by
  -- Rewrite membership through the computed rows, then compare coordinates.
  simp [diophantineFeasibilitySolutionSet, diophantineFeasibilityRhs,
    diophantineFeasibilityMatrix_mulVec, Matrix.vecCons_inj]
