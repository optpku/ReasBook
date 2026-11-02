import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_definition_4_2_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

-- This file is a bridge/view layer: the source-facing row-bicoloring language is expressed via
-- the Chapter 4.2 owner `is_equitable_bicoloring` applied to the transpose matrix.

section Definition42Extra3

variable {m n : Type*}

/-- The columnwise difference between the sum of the red rows and the sum of the blue rows of
`A`. -/
abbrev row_bicoloring_difference
    (A : Matrix m n ℤ) (red blue : Finset m) : n → ℤ :=
  column_bicoloring_difference A.transpose red blue

/-- Evaluating `row_bicoloring_difference` at a column expands to the defining red-sum minus
blue-sum formula. -/
@[simp] theorem row_bicoloring_difference_apply
    (A : Matrix m n ℤ) (red blue : Finset m) (j : n) :
    row_bicoloring_difference A red blue j =
      red.sum (fun i ↦ A i j) - blue.sum (fun i ↦ A i j) :=
  column_bicoloring_difference_apply A.transpose red blue j

variable [Fintype m] [DecidableEq m]

/-- Definition 4.2-extra-3. An equitable row-bicoloring of an integral matrix `A` is a partition
of its rows into red and blue row sets such that, in every column, the sum of the red entries
minus the sum of the blue entries is `0`, `1`, or `-1`. -/
abbrev is_equitable_row_bicoloring
    (A : Matrix m n ℤ) (red blue : Finset m) : Prop :=
  is_equitable_bicoloring A.transpose red blue

/-- In an equitable row-bicoloring, the red and blue row sets are disjoint. -/
theorem is_equitable_row_bicoloring.disjoint
    {A : Matrix m n ℤ} {red blue : Finset m} :
    is_equitable_row_bicoloring A red blue → Disjoint red blue
  | h => (show is_equitable_bicoloring A.transpose red blue from h).disjoint

/-- In an equitable row-bicoloring, every row is colored either red or blue. -/
theorem is_equitable_row_bicoloring.cover
    {A : Matrix m n ℤ} {red blue : Finset m} :
    is_equitable_row_bicoloring A red blue → red ∪ blue = Finset.univ
  | h => (show is_equitable_bicoloring A.transpose red blue from h).cover

/-- In an equitable row-bicoloring, each column difference is `0`, `1`, or `-1`. -/
theorem is_equitable_row_bicoloring.column_balance
    {A : Matrix m n ℤ} {red blue : Finset m}
    (h : is_equitable_row_bicoloring A red blue) (j : n) :
    row_bicoloring_difference A red blue j = 0 ∨
      row_bicoloring_difference A red blue j = 1 ∨
      row_bicoloring_difference A red blue j = -1 := by
  simpa [row_bicoloring_difference] using
    (show
        column_bicoloring_difference A.transpose red blue j = 0 ∨
          column_bicoloring_difference A.transpose red blue j = 1 ∨
            column_bicoloring_difference A.transpose red blue j = -1
      from (show is_equitable_bicoloring A.transpose red blue from h).row_balance j)

/-- Unfolding lemma for `is_equitable_row_bicoloring`. -/
theorem is_equitable_row_bicoloring_iff
    {A : Matrix m n ℤ} {red blue : Finset m} :
    is_equitable_row_bicoloring A red blue ↔
      Disjoint red blue ∧
        red ∪ blue = Finset.univ ∧
          ∀ j : n,
            row_bicoloring_difference A red blue j = 0 ∨
              row_bicoloring_difference A red blue j = 1 ∨
                row_bicoloring_difference A red blue j = -1 := by
  simpa [is_equitable_row_bicoloring, row_bicoloring_difference] using
    (is_equitable_bicoloring_iff A.transpose red blue)

/-- In an equitable row-bicoloring, every row is colored either red or blue. -/
theorem is_equitable_row_bicoloring.mem_red_or_mem_blue
    {A : Matrix m n ℤ} {red blue : Finset m}
    (h : is_equitable_row_bicoloring A red blue) (i : m) :
    i ∈ red ∨ i ∈ blue :=
  is_equitable_bicoloring.mem_red_or_mem_blue
    (show is_equitable_bicoloring A.transpose red blue from h) i

end Definition42Extra3
