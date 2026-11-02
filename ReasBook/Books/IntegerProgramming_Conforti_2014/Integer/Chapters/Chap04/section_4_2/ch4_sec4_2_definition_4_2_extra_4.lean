import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- This file records the source-facing `(0, ±1)` entry owner used repeatedly in Chapter 4.2 and
-- later TU criteria.

section Definition42Extra4

variable {m n : Type*}

/-- An integer matrix is a `(0, ±1)`-matrix when every entry lies in the canonical image of
`SignType.cast`. -/
def HasZeroOneNegOneEntries (A : Matrix m n ℤ) : Prop :=
  ∀ i j, A i j ∈ Set.range (SignType.cast : SignType → ℤ)

/-- Unfolding `HasZeroOneNegOneEntries` recovers the source-facing `0`, `1`, `-1` entrywise
characterization. -/
theorem hasZeroOneNegOneEntries_iff (A : Matrix m n ℤ) :
    HasZeroOneNegOneEntries A ↔
      ∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1 := by
  constructor
  · intro hA i j
    rcases hA i j with ⟨s, hs⟩
    cases s with
    | zero =>
        exact Or.inl <| by simpa using hs.symm
    | neg =>
        exact Or.inr <| Or.inr <| by simpa using hs.symm
    | pos =>
        exact Or.inr <| Or.inl <| by simpa using hs.symm
  · intro hA i j
    rcases hA i j with h | h | h
    · exact ⟨0, by simpa using h.symm⟩
    · exact ⟨1, by simpa using h.symm⟩
    · exact ⟨-1, by simpa using h.symm⟩

namespace HasZeroOneNegOneEntries

/-- Entrywise expansion of `HasZeroOneNegOneEntries`. -/
theorem apply {A : Matrix m n ℤ} (hA : HasZeroOneNegOneEntries A) (i : m) (j : n) :
    A i j = 0 ∨ A i j = 1 ∨ A i j = -1 :=
  (hasZeroOneNegOneEntries_iff A).1 hA i j

/-- The `(0, ±1)` entry condition is preserved by taking submatrices. -/
theorem submatrix {m' n' : Type*} {A : Matrix m n ℤ}
    (hA : HasZeroOneNegOneEntries A) (row : m' → m) (col : n' → n) :
    HasZeroOneNegOneEntries (A.submatrix row col) := by
  intro i j
  simpa using hA (row i) (col j)

end HasZeroOneNegOneEntries

namespace Matrix.IsTotallyUnimodular

/-- Total unimodularity forces every entry to be `0`, `1`, or `-1`. -/
theorem hasZeroOneNegOneEntries {A : Matrix m n ℤ} (hA : A.IsTotallyUnimodular) :
    HasZeroOneNegOneEntries A := by
  intro i j
  simpa using hA.apply i j

end Matrix.IsTotallyUnimodular

end Definition42Extra4
