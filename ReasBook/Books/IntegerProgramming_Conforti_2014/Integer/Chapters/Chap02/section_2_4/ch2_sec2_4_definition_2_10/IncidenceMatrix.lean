/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Mul

open scoped BigOperators Matrix

public section

namespace Matrix

section IncidenceMatrix

variable {row col : Type} [DecidableEq col]

/-- The `0/1` incidence matrix attached to a finite family of subsets
`family : row → Finset col`. -/
def incidenceMatrix (family : row → Finset col) : Matrix row col ℤ :=
  fun i j ↦ if j ∈ family i then 1 else 0

/-- Expanding `Matrix.incidenceMatrix family` at entry `(i, j)` gives the indicator of the
membership condition `j ∈ family i`. -/
theorem incidenceMatrix_apply
    {family : row → Finset col} {i : row} {j : col} :
    incidenceMatrix family i j = if j ∈ family i then 1 else 0 := by
  -- The matrix entry is definitionally the corresponding membership indicator.
  rfl

/--
remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_definition_2_10/IncidenceMatrix.lean

Evaluating `(Matrix.incidenceMatrix family) *ᵥ x` at row `i` gives the sum of the coordinates of
`x` indexed by `family i`.
-/
theorem incidenceMatrix_mulVec_apply
    [Fintype col]
    (family : row → Finset col) (x : col → ℤ) (i : row) :
    (incidenceMatrix family *ᵥ x) i = (family i).sum x := by
  -- Expand the selected row product, then restrict its indicator sum to `family i`.
  simp [mulVec, dotProduct, incidenceMatrix_apply, Finset.sum_ite_mem]

end IncidenceMatrix

end Matrix
