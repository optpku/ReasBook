import Mathlib

/-!
Definition 4.10.1-extra-2 lies in the combinatorial-matrix domain.

Domain-style sampling for this refine pass:
* source-facing owner in this section: `unique_disjointness_matrix`
* derived matrix-entry API in the same domain: `unique_disjointness_matrix_apply`
* mathlib matrix constructor/apply pattern: `Matrix.of`, `Matrix.of_apply`

The primitive data here is the matrix itself. Entrywise facts are derived API and should be reused
downstream instead of duplicated.
-/

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition 4.10.1-extra-2: the unique disjointness matrix `U^n`, indexed by subsets of
`Fin n` (the Lean encoding of the `2^n` subsets of `{1, ..., n}`), with entry `1` unless the
intersection has cardinality exactly `1`. -/
def unique_disjointness_matrix (n : ℕ) : Matrix (Finset (Fin n)) (Finset (Fin n)) ℕ :=
  fun a b ↦ if (a ∩ b).card = 1 then 0 else 1

namespace UniqueDisjointnessMatrixNotation

scoped notation "U^" n:max => unique_disjointness_matrix n

end UniqueDisjointnessMatrixNotation

open scoped UniqueDisjointnessMatrixNotation

/-- The entries of the unique disjointness matrix are given by the defining `if`-formula. -/
theorem unique_disjointness_matrix_apply {n : ℕ} (a b : Finset (Fin n)) :
    (U^n) a b = if (a ∩ b).card = 1 then 0 else 1 := rfl

/-- An entry of the unique disjointness matrix is `0` exactly when the two indexing subsets meet in
exactly one element. -/
theorem unique_disjointness_matrix_eq_zero_iff {n : ℕ} {a b : Finset (Fin n)} :
    (U^n) a b = 0 ↔ (a ∩ b).card = 1 := by
  by_cases h : (a ∩ b).card = 1 <;> simp [unique_disjointness_matrix, h]
