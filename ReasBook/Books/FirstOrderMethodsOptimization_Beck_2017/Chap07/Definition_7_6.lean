/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

/-- Definition 7.6: `permutationMatrices n` is the set of all `n × n` real permutation matrices,
denoted in the text by `Λ_n`; equivalently, it is the range of the canonical map sending a
permutation of `Fin n` to its permutation matrix. -/
def permutationMatrices (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  Set.range fun σ : Equiv.Perm (Fin n) ↦ σ.permMatrix ℝ

-- Proof sketch: unfold `permutationMatrices`; the right-hand side is exactly the defining
-- range used in the declaration.
/-- The defining formula for `permutationMatrices n` is the range of the permutation-matrix map
from permutations of `Fin n`. -/
@[simp] theorem permutationMatrices_def (n : ℕ) :
    permutationMatrices n = Set.range (fun σ : Equiv.Perm (Fin n) ↦ σ.permMatrix ℝ) := by
  -- This theorem is just the unfolded definition of `permutationMatrices`.
  rfl

-- Proof sketch: `σ.permMatrix ℝ` belongs to the defining range of `permutationMatrices n` with
-- witness `σ`.
/-- Every permutation matrix of order `n` belongs to `permutationMatrices n`. -/
@[simp] theorem permMatrix_mem_permutationMatrices (σ : Equiv.Perm (Fin n)) :
    σ.permMatrix ℝ ∈ permutationMatrices n := by
  -- We prove membership by exhibiting `σ` as the witness in the defining range.
  rw [permutationMatrices_def]
  exact Set.mem_range_self σ

-- Proof sketch: the identity permutation contributes its permutation matrix to the defining
-- range, so `permutationMatrices n` is nonempty.
/-- The set `permutationMatrices n` is nonempty because it contains the identity permutation
matrix. -/
theorem permutationMatrices_nonempty (n : ℕ) : Set.Nonempty (permutationMatrices n) := by
  -- The identity permutation contributes a concrete matrix in the set.
  refine ⟨(1 : Equiv.Perm (Fin n)).permMatrix ℝ, ?_⟩
  exact permMatrix_mem_permutationMatrices (n := n) (1 : Equiv.Perm (Fin n))

-- Proof sketch: unfold `permutationMatrices`; membership in a set-valued range means exactly that
-- the matrix is `σ.permMatrix ℝ` for some permutation `σ`.
/-- A real square matrix belongs to `permutationMatrices n` exactly when it is the permutation
matrix associated with some permutation of `Fin n`. -/
@[simp] theorem mem_permutationMatrices_iff (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ permutationMatrices n ↔ ∃ σ : Equiv.Perm (Fin n), A = σ.permMatrix ℝ := by
  -- Unfold membership in the defining range and read off the witness permutation.
  constructor
  · intro hA
    rw [permutationMatrices_def] at hA
    rcases hA with ⟨σ, rfl⟩
    exact ⟨σ, rfl⟩
  · rintro ⟨σ, rfl⟩
    exact permMatrix_mem_permutationMatrices σ

end
