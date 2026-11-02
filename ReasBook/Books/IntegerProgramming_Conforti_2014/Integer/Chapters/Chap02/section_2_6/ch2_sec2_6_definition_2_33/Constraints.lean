import Mathlib.Data.Set.Defs
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_6.ch2_sec2_6_definition_2_32.Sudoku

namespace Sudoku

/-- The entries of the `3 × 3` block with zero-based anchor indices `(bi, bj)` in the candidate
grid `x`. -/
def block
    (x : Fin 9 → Fin 9 → Fin 9)
    (bi bj : Fin 3) : Fin 3 × Fin 3 → Fin 9 :=
  fun qr ↦ x (blockCoord bi qr.1) (blockCoord bj qr.2)

/-- Unfolding equation for the block view `block x bi bj`. -/
@[simp] theorem block_apply
    (x : Fin 9 → Fin 9 → Fin 9)
    (bi bj q r : Fin 3) :
    block x bi bj (q, r) = x (blockCoord bi q) (blockCoord bj r) :=
  rfl

/-- A candidate Sudoku completion respects the given clues when every specified entry matches its
prescribed digit. -/
def respectsGivens
    (clues : Fin 9 → Fin 9 → Option (Fin 9))
    (x : Fin 9 → Fin 9 → Fin 9) : Prop :=
  ∀ i j, match clues i j with
    | none => True
    | some k => x i j = k

/-- Unfolding characterization of `respectsGivens clues x`. -/
@[simp] theorem respectsGivens_iff
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9} :
    respectsGivens clues x ↔
      ∀ i j, match clues i j with
        | none => True
        | some k => x i j = k :=
  Iff.rfl

/-- Definition 2.33 (Constraint-programming formulation of Sudoku): the Sudoku constraints on a
candidate grid `x` are the row, column, and block `alldifferent` conditions together with
agreement with the given clues, formalized by injectivity on `Fin 9` and `Fin 3 × Fin 3`. -/
def constraints
    (clues : Fin 9 → Fin 9 → Option (Fin 9))
    (x : Fin 9 → Fin 9 → Fin 9) : Prop :=
  (∀ i, Function.Injective (x i)) ∧
    (∀ j, Function.Injective (fun i ↦ x i j)) ∧
    (∀ bi bj, Function.Injective (block x bi bj)) ∧
    respectsGivens clues x

/-- Membership in `constraints clues x` is exactly the conjunction of the row, column, block, and
clue conditions from Definition 2.33. -/
@[simp] theorem constraints_iff
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9} :
    constraints clues x ↔
      (∀ i, Function.Injective (x i)) ∧
        (∀ j, Function.Injective (fun i ↦ x i j)) ∧
        (∀ bi bj, Function.Injective (block x bi bj)) ∧
        respectsGivens clues x :=
  Iff.rfl

/-- The set of Sudoku grids satisfying the constraint-programming formulation for the clue table
`clues`. -/
def constraintSet
    (clues : Fin 9 → Fin 9 → Option (Fin 9)) :
    Set (Fin 9 → Fin 9 → Fin 9) :=
  {x | constraints clues x}

/-- Membership in `constraintSet clues` is exactly the conjunction of the row, column, block, and
clue conditions from Definition 2.33. -/
@[simp] theorem mem_constraintSet_iff
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9} :
    x ∈ constraintSet clues ↔
      (∀ i, Function.Injective (x i)) ∧
        (∀ j, Function.Injective (fun i ↦ x i j)) ∧
        (∀ bi bj, Function.Injective (block x bi bj)) ∧
        respectsGivens clues x :=
  Iff.rfl

/-- The row `alldifferent` condition extracted from `constraints clues x`. -/
theorem constraints_rowInjective
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9}
    (h_constraints : constraints clues x) (i : Fin 9) :
    Function.Injective (x i) :=
  h_constraints.1 i

/-- The column `alldifferent` condition extracted from `constraints clues x`. -/
theorem constraints_colInjective
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9}
    (h_constraints : constraints clues x) (j : Fin 9) :
    Function.Injective (fun i ↦ x i j) :=
  h_constraints.2.1 j

/-- The block `alldifferent` condition extracted from `constraints clues x`. -/
theorem constraints_blockInjective
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9}
    (h_constraints : constraints clues x) (bi bj : Fin 3) :
    Function.Injective (block x bi bj) :=
  h_constraints.2.2.1 bi bj

/-- The clue-agreement condition extracted from `constraints clues x`. -/
theorem constraints_respectsGivens
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9}
    (h_constraints : constraints clues x) :
    respectsGivens clues x :=
  h_constraints.2.2.2

/-- A fixed clue extracted from `constraints clues x` forces the corresponding cell value. -/
theorem constraints_clue
    {clues : Fin 9 → Fin 9 → Option (Fin 9)}
    {x : Fin 9 → Fin 9 → Fin 9}
    (h_constraints : constraints clues x)
    {i j : Fin 9} {k : Fin 9}
    (h_clue : clues i j = some k) :
    x i j = k := by
  simpa [h_clue] using constraints_respectsGivens h_constraints i j

end Sudoku
