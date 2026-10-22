/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace Matrix

section

variable {n : ℕ}

/-- A real square matrix is a generalized permutation matrix if every entry is `0`, `1`, or `-1`,
and each row and each column contains exactly one nonzero entry. -/
class IsGeneralizedPermutation (A : Matrix (Fin n) (Fin n) ℝ) : Prop where
  entry_eq_zero_or_one_or_neg_one (i j : Fin n) :
    A i j = 0 ∨ A i j = 1 ∨ A i j = -1
  row_existsUnique_ne_zero (i : Fin n) :
    ∃! j : Fin n, A i j ≠ 0
  col_existsUnique_ne_zero (j : Fin n) :
    ∃! i : Fin n, A i j ≠ 0

-- Proof sketch: for the identity matrix, diagonal entries are `1`, off-diagonal entries are `0`,
-- and each row and column has its unique nonzero entry on the diagonal.
/-- The identity matrix is a generalized permutation matrix. -/
instance : IsGeneralizedPermutation (1 : Matrix (Fin n) (Fin n) ℝ) := by
  refine
    { entry_eq_zero_or_one_or_neg_one := ?_
      row_existsUnique_ne_zero := ?_
      col_existsUnique_ne_zero := ?_ }
  · intro i j
    -- Identity-matrix entries are `1` on the diagonal and `0` off the diagonal.
    by_cases hij : i = j
    · right
      left
      subst j
      simp
    · left
      simp [hij]
  · intro i
    -- In row `i`, the diagonal position `i` is the unique nonzero entry.
    refine ⟨i, ?_, ?_⟩
    · simp
    · intro j hj
      by_contra hji
      have hij : ¬i = j := by
        simpa [eq_comm] using hji
      exact hj (by simp [hij])
  · intro j
    -- In column `j`, the diagonal position `j` is the unique nonzero entry.
    refine ⟨j, ?_, ?_⟩
    · simp
    · intro i hi
      by_contra hij
      exact hi (by simp [hij])

end

end Matrix

section

variable {n : ℕ}

/-- Definition 7.7: `generalizedPermutationMatrices n` is the set of all real `n × n`
generalized permutation matrices, denoted in the text by `Λ^G_n`. -/
def generalizedPermutationMatrices (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | Matrix.IsGeneralizedPermutation A}

-- Proof sketch: unfold `generalizedPermutationMatrices`; the right-hand side is exactly the
-- defining set of matrices satisfying `Matrix.IsGeneralizedPermutation`.
/-- The defining formula for `generalizedPermutationMatrices n` is the set of matrices satisfying
`Matrix.IsGeneralizedPermutation`. -/
@[simp] theorem generalizedPermutationMatrices_def (n : ℕ) :
    generalizedPermutationMatrices n = {A | Matrix.IsGeneralizedPermutation A} := by
  -- This theorem is just the unfolded definition of `generalizedPermutationMatrices`.
  rfl

notation "Λᴳ[" n "]" => generalizedPermutationMatrices n

-- Proof sketch: the identity matrix carries the instance
-- `Matrix.IsGeneralizedPermutation (1 : Matrix (Fin n) (Fin n) ℝ)`, so it belongs to the
-- defining set of generalized permutation matrices.
/-- The identity matrix belongs to `generalizedPermutationMatrices n`. -/
@[simp] theorem one_mem_generalizedPermutationMatrices :
    (1 : Matrix (Fin n) (Fin n) ℝ) ∈ generalizedPermutationMatrices n := by
  -- Unfold membership and use the identity-matrix instance proved above.
  rw [generalizedPermutationMatrices_def]
  change Matrix.IsGeneralizedPermutation (1 : Matrix (Fin n) (Fin n) ℝ)
  infer_instance

-- Proof sketch: `generalizedPermutationMatrices n` is nonempty because it contains the identity
-- matrix.
/-- The set `generalizedPermutationMatrices n` is nonempty because it contains the identity
matrix. -/
theorem generalizedPermutationMatrices_nonempty (n : ℕ) :
    Set.Nonempty (generalizedPermutationMatrices n) := by
  -- The identity matrix is a concrete witness in the set.
  exact ⟨1, one_mem_generalizedPermutationMatrices (n := n)⟩

-- Proof sketch: unfold `generalizedPermutationMatrices`; membership in the defining set is exactly
-- the predicate `Matrix.IsGeneralizedPermutation`.
/-- A real square matrix belongs to `Λᴳ[n]` exactly when it is a generalized permutation matrix. -/
@[simp] theorem mem_generalizedPermutationMatrices_iff (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ Λᴳ[n] ↔ Matrix.IsGeneralizedPermutation A := by
  -- Membership in `Λᴳ[n]` is exactly the defining predicate.
  rw [generalizedPermutationMatrices_def]
  change Matrix.IsGeneralizedPermutation A ↔ Matrix.IsGeneralizedPermutation A
  rfl

end
