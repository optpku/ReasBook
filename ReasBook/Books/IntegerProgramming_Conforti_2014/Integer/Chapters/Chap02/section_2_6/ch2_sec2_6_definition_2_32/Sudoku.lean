import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_zero_one
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Defs

open scoped BigOperators

namespace Sudoku

/-- The coordinate of an entry inside a `3 × 3` block, with `Fin 3` block indices corresponding
to the textbook block starts `1, 4, 7` after shifting from one-based to zero-based indexing. -/
def blockCoord (b q : Fin 3) : Fin 9 :=
  Fin.ofNat 9 (3 * (b : ℕ) + (q : ℕ))

/-- Expanding `blockCoord` gives the zero-based block-start-plus-offset formula. -/
theorem blockCoord_def
    (b q : Fin 3) :
    blockCoord b q = Fin.ofNat 9 (3 * (b : ℕ) + (q : ℕ)) :=
  rfl

/-- A candidate Sudoku completion respects the given clues when every specified digit is forced to
appear in its prescribed cell. -/
def respectsClues
    (clues : Fin 9 → Fin 9 → Option (Fin 9))
    (x : Fin 9 → Fin 9 → Fin 9 → ℤ) : Prop :=
  ∀ i j, match clues i j with
    | none => True
    | some k => x i j k = 1

/-- Membership in `respectsClues clues x` is exactly the clue-fixing condition from the source
formulation. -/
theorem respectsClues_iff
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9 → ℤ} :
    respectsClues clues x ↔
      ∀ i j, match clues i j with
        | none => True
        | some k => x i j k = 1 :=
  Iff.rfl

/-- The Sudoku feasible region attached to a partial clue assignment consists of the integer
families satisfying the binary, row, column, block, cell, and clue-fixing constraints. -/
def feasibleSet
    (clues : Fin 9 → Fin 9 → Option (Fin 9)) :
    Set (Fin 9 → Fin 9 → Fin 9 → ℤ) :=
  {x |
    is_zero_one_family (fun ijk : Fin 9 × Fin 9 × Fin 9 ↦ x ijk.1 ijk.2.1 ijk.2.2) ∧
      (∀ j k, (∑ i : Fin 9, x i j k) = 1) ∧
      (∀ i k, (∑ j : Fin 9, x i j k) = 1) ∧
      (∀ bi bj k, (∑ q : Fin 3, ∑ r : Fin 3, x (blockCoord bi q) (blockCoord bj r) k) = 1) ∧
      (∀ i j, (∑ k : Fin 9, x i j k) = 1) ∧
      respectsClues clues x}

/-- Membership in `feasibleSet clues` means that `x` satisfies the six displayed constraint
families in Definition 2.32. -/
theorem mem_feasibleSet_iff
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9 → ℤ} :
    x ∈ feasibleSet clues ↔
      (∀ i j k, x i j k = 0 ∨ x i j k = 1) ∧
      (∀ j k, (∑ i : Fin 9, x i j k) = 1) ∧
      (∀ i k, (∑ j : Fin 9, x i j k) = 1) ∧
      (∀ bi bj k, (∑ q : Fin 3, ∑ r : Fin 3, x (blockCoord bi q) (blockCoord bj r) k) = 1) ∧
      (∀ i j, (∑ k : Fin 9, x i j k) = 1) ∧
      (∀ i j, match clues i j with
        | none => True
        | some k => x i j k = 1) := by
  simp [feasibleSet, respectsClues, is_zero_one_family_iff]

/-- Every variable in a feasible Sudoku completion model is binary. -/
theorem feasible_binary
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9 → ℤ}
    (hx : x ∈ feasibleSet clues)
    (i j k : Fin 9) :
    x i j k = 0 ∨ x i j k = 1 :=
  (mem_feasibleSet_iff.mp hx).1 i j k

/-- In a feasible Sudoku completion model, each digit `k` appears exactly once in every column
`j`. -/
theorem feasible_columnDigitSum_eq_one
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9 → ℤ}
    (hx : x ∈ feasibleSet clues)
    (j k : Fin 9) :
    (∑ i : Fin 9, x i j k) = 1 :=
  (mem_feasibleSet_iff.mp hx).2.1 j k

/-- In a feasible Sudoku completion model, each digit `k` appears exactly once in every row
`i`. -/
theorem feasible_rowDigitSum_eq_one
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9 → ℤ}
    (hx : x ∈ feasibleSet clues)
    (i k : Fin 9) :
    (∑ j : Fin 9, x i j k) = 1 :=
  (mem_feasibleSet_iff.mp hx).2.2.1 i k

/-- In a feasible Sudoku completion model, each digit `k` appears exactly once in every
`3 × 3` block indexed by `(bi, bj)`. -/
theorem feasible_blockDigitSum_eq_one
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9 → ℤ}
    (hx : x ∈ feasibleSet clues)
    (bi bj : Fin 3)
    (k : Fin 9) :
    (∑ q : Fin 3, ∑ r : Fin 3, x (blockCoord bi q) (blockCoord bj r) k) = 1 :=
  (mem_feasibleSet_iff.mp hx).2.2.2.1 bi bj k

/-- In a feasible Sudoku completion model, each cell `(i, j)` receives exactly one digit. -/
theorem feasible_cellSum_eq_one
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9 → ℤ}
    (hx : x ∈ feasibleSet clues)
    (i j : Fin 9) :
    (∑ k : Fin 9, x i j k) = 1 :=
  (mem_feasibleSet_iff.mp hx).2.2.2.2.1 i j

/-- A feasible Sudoku completion model satisfies the clue-fixing constraints. -/
theorem feasible_respectsClues
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9 → ℤ}
    (hx : x ∈ feasibleSet clues) :
    respectsClues clues x := by
  simpa [respectsClues] using (mem_feasibleSet_iff.mp hx).2.2.2.2.2

/-- A fixed clue in a feasible Sudoku completion model forces the corresponding binary variable to
be `1`. -/
theorem feasible_clue
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9 → ℤ}
    (hx : x ∈ feasibleSet clues)
    {i j : Fin 9}
    {k : Fin 9}
    (h_clue : clues i j = some k) :
    x i j k = 1 := by
  simpa [h_clue] using feasible_respectsClues hx i j

end Sudoku
