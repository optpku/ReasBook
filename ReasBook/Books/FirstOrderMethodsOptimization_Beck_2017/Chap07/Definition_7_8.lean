/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_1

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

-- Proof sketch: permutation matrices are orthogonal because their transpose is the permutation
-- matrix of the inverse permutation, so the product with the transpose is the identity matrix.
/-- Permutation matrices over `ℝ` lie in the orthogonal group. -/
theorem permMatrix_mem_orthogonalGroup (σ : Equiv.Perm (Fin n)) :
    σ.permMatrix ℝ ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  -- Orthogonality reduces to the permutation matrix times its transpose being the identity.
  refine
    (Matrix.mem_orthogonalGroup_iff
      (A := (σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ)) (R := ℝ)).2 ?_
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
  simp

/-- The orthogonal transformation of `ℝ^n` induced by a permutation of the coordinates. -/
noncomputable def permutationOrthogonalMatrix (σ : Equiv.Perm (Fin n)) :
    Matrix.orthogonalGroup (Fin n) ℝ :=
  ⟨σ.permMatrix ℝ, permMatrix_mem_orthogonalGroup σ⟩

/-- The family `Λ_n` of coordinate-permutation orthogonal matrices of `ℝ^n`. -/
noncomputable def permutationOrthogonalFamily (n : ℕ) :
    Set (Matrix.orthogonalGroup (Fin n) ℝ) :=
  Set.range permutationOrthogonalMatrix

notation "Λ[" n "]" => permutationOrthogonalFamily n

/-- The decreasing rearrangement `x↓` of a vector `x` is obtained by sorting its coordinates in
weakly decreasing order. -/
noncomputable def descendingRearrangement (x : Fin n → ℝ) : Fin n → ℝ :=
  x ∘ Tuple.sort x ∘ Fin.revPerm

postfix:max "↓" => descendingRearrangement

/-- Definition 7.8: a proper extended-real-valued function on `ℝ^n` is permutation symmetric when
it is invariant under every permutation matrix. -/
abbrev IsPermutationSymmetricFunction (f : (Fin n → ℝ) → EReal) : Prop :=
  IsSymmetricFunction Λ[n] f

/-- Helper for Definition 7.8: the orthogonal action of a permutation matrix just reindexes the
coordinates of the vector. -/
lemma permutationOrthogonalMatrix_smul
    (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    permutationOrthogonalMatrix σ • x = x ∘ σ := by
  -- The orthogonal-group action is matrix multiplication, and `permMatrix_mulVec` computes it.
  simpa [permutationOrthogonalMatrix] using
    (Matrix.permMatrix_mulVec (R := ℝ) (σ := σ) (v := x))

/-- Helper for Definition 7.8: the decreasing rearrangement is unchanged by permuting coordinates
before sorting. -/
lemma descendingRearrangement_comp_perm
    (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    (x ∘ σ)↓ = x↓ := by
  -- Sorting after a permutation gives the same sorted tuple, so the canonical representative is
  -- unchanged on the whole permutation orbit.
  funext i
  simpa [descendingRearrangement, Function.comp_assoc] using
    congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort (f := x) (σ := σ)) (Fin.revPerm i)

/-- Helper for Definition 7.8: the decreasing rearrangement is obtained from `x` by the concrete
sorting permutation. -/
lemma descendingRearrangement_eq_sort_perm_smul
    (x : Fin n → ℝ) :
    permutationOrthogonalMatrix (Tuple.sort x * Fin.revPerm) • x = x↓ := by
  -- The source proof picks the sorted orbit representative by applying the sorting permutation.
  rw [permutationOrthogonalMatrix_smul]
  simp [descendingRearrangement, Equiv.Perm.coe_mul]

-- Proof sketch: for the forward implication, permutation symmetry supplies properness and every
-- vector has the same value as its decreasing rearrangement. For the reverse implication, keep the
-- source's properness assumption explicitly, and use that every permutation of `x` has the same
-- decreasing rearrangement `x↓` to force invariance under coordinate permutations.
/-- A permutation symmetric function is exactly a proper function whose value depends only on the
decreasing rearrangement `x↓`. -/
theorem isPermutationSymmetricFunction_iff_forall_eq_descendingRearrangement
    (f : (Fin n → ℝ) → EReal) :
    IsPermutationSymmetricFunction f ↔
      IsProperExtendedRealFunction f ∧ ∀ x, f x = f x↓ := by
  constructor
  · intro hf
    refine ⟨hf.toIsProperExtendedRealFunction, ?_⟩
    intro x
    -- The forward direction evaluates `f` on the canonical representative `x↓` of the orbit of
    -- `x`, obtained by the concrete sorting permutation.
    have hsort :=
      hf.map_smul
        (permutationOrthogonalMatrix (Tuple.sort x * Fin.revPerm))
        (by exact Set.mem_range_self (Tuple.sort x * Fin.revPerm))
        x
    simpa [descendingRearrangement_eq_sort_perm_smul x] using hsort.symm
  · rintro ⟨hproper, hdesc⟩
    refine
      { toIsProperExtendedRealFunction := hproper
        map_smul := ?_ }
    intro A hA x
    -- The reverse direction reduces an arbitrary orbit point `A • x` to the same decreasing
    -- rearrangement `x↓`, so `f` is constant on the whole permutation orbit.
    rcases hA with ⟨σ, rfl⟩
    calc
      f (permutationOrthogonalMatrix σ • x)
          = f ((permutationOrthogonalMatrix σ • x)↓) := hdesc _
      _ = f (x↓) := by
        rw [permutationOrthogonalMatrix_smul, descendingRearrangement_comp_perm]
      _ = f x := (hdesc x).symm

end
