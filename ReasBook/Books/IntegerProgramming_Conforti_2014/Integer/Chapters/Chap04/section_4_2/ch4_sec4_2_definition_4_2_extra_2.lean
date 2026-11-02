import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic search tools such as
-- `lean_leansearch`, so the declarations below use direct local matrix and finite-set
-- formulations for the red/blue column partition in the source definition.

section Definition42Extra2

variable {m n : Type*}

/-- The rowwise difference between the sum of the red columns and the sum of the blue columns of
`A`. -/
def column_bicoloring_difference
    (A : Matrix m n ℤ) (red blue : Finset n) : m → ℤ :=
  fun i ↦ red.sum (fun j ↦ A i j) - blue.sum (fun j ↦ A i j)

/-- Evaluating `column_bicoloring_difference` at a row expands to the defining red-sum minus
blue-sum formula. -/
@[simp] theorem column_bicoloring_difference_apply
    (A : Matrix m n ℤ) (red blue : Finset n) (i : m) :
    column_bicoloring_difference A red blue i =
      red.sum (fun j ↦ A i j) - blue.sum (fun j ↦ A i j) :=
  rfl

variable [Fintype n] [DecidableEq n]

/-- Definition 4.2-extra-2. An equitable bicoloring of an integer matrix `A` is a partition of
its columns into red and blue column sets such that, in every row, the sum of the red columns
minus the sum of the blue columns is `0`, `1`, or `-1`. -/
@[mk_iff is_equitable_bicoloring_iff]
class is_equitable_bicoloring
    (A : Matrix m n ℤ) (red blue : Finset n) : Prop where
  /-- The red and blue column sets are disjoint. -/
  disjoint : Disjoint red blue
  /-- Every column of `A` is colored either red or blue. -/
  cover : red ∪ blue = Finset.univ
  /-- In each row, the red-column sum minus the blue-column sum is `0`, `1`, or `-1`. -/
  row_balance (i : m) :
    column_bicoloring_difference A red blue i = 0 ∨
      column_bicoloring_difference A red blue i = 1 ∨
      column_bicoloring_difference A red blue i = -1

/-- In an equitable bicoloring, every column is colored either red or blue. -/
theorem is_equitable_bicoloring.mem_red_or_mem_blue
    {A : Matrix m n ℤ} {red blue : Finset n}
    (h : is_equitable_bicoloring A red blue) (j : n) :
    j ∈ red ∨ j ∈ blue := by
  simpa [Finset.mem_union] using congrArg (fun s : Finset n ↦ j ∈ s) h.cover

end Definition42Extra2
