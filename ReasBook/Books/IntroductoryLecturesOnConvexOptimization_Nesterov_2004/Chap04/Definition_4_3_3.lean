/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 4.3.3 lies in the finite-dimensional linear-algebra / symmetric-matrix subspace
domain.

Sampled owner-style declarations in this domain:
* `coordinateSubspace` and `mem_coordinateSubspace_iff` in `Text_2_13`, the Chapter 2 owner/view
  for coordinatewise vanishing subspaces in `ℝⁿ`;
* mathlib `selfAdjointMatricesSubmodule`, the canonical submodule owner for symmetric real
  matrices via the identity bilinear form;
* mathlib `Submodule.pi` and `Submodule.comap`, the canonical owners for coordinatewise support
  conditions on function spaces;
* mathlib `Matrix.ofLinearEquiv`, the canonical bridge between matrices and curried entrywise
  functions.

Best owner abstractions:
* source-facing: `coordinateSymmetricMatrixSubspace k n`, the textbook subspace `𝕊^{k,n}`;
* core/canonical: the intersection of the symmetric-matrix owner
  `selfAdjointMatricesSubmodule (1 : Matrix (Fin n) (Fin n) ℝ)` with the coordinate-support
  submodule defined via `Submodule.comap`/`Submodule.pi`;
* bridge/view: `mem_coordinateSymmetricMatrixSubspace_iff`.

Primitive data:
* symmetry of the matrix;
* the allowed support pattern: diagonal entries are free, and off-diagonal entries are free only
  inside the leading `k × k` block.

Derived API:
* the source-facing owner `coordinateSymmetricMatrixSubspace`;
* its notation `𝕊^{k,n}`;
* the textbook membership criterion `mem_coordinateSymmetricMatrixSubspace_iff`.

This file therefore keeps the textbook owner `𝕊^{k,n}` but deletes the hand-written additive
closure proofs in favor of the canonical symmetric-matrix owner and a private support submodule.
-/

#check coordinateSubspace
#check mem_coordinateSubspace_iff

private theorem mem_symmetricMatrixSubmodule_iff {H : Mat} :
    H ∈ selfAdjointMatricesSubmodule (1 : Mat) ↔ H.IsSymm := by
  rw [mem_selfAdjointMatricesSubmodule]
  simp [Matrix.IsSelfAdjoint, Matrix.IsAdjointPair, Matrix.IsSymm]

private def coordinateMatrixSupportSubmodule (k n : ℕ) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  Submodule.comap
    ((Matrix.ofLinearEquiv ℝ : (Fin n → Fin n → ℝ) ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ).symm.toLinearMap)
    (Submodule.pi Set.univ (fun i : Fin n ↦
      Submodule.pi Set.univ (fun j : Fin n ↦
        if i = j ∨ (i.1 < k ∧ j.1 < k) then (⊤ : Submodule ℝ ℝ) else ⊥)))

private theorem mem_coordinateMatrixSupportSubmodule_iff {H : Mat} {k : ℕ} :
    H ∈ coordinateMatrixSupportSubmodule k n ↔
      ∀ i j : Fin n, i ≠ j → (k ≤ i.1 ∨ k ≤ j.1) → H i j = 0 := by
  have hsupp :
      H ∈ coordinateMatrixSupportSubmodule k n ↔
        ∀ i j : Fin n,
          H i j ∈
            (if i = j ∨ (i.1 < k ∧ j.1 < k) then (⊤ : Submodule ℝ ℝ) else ⊥) := by
    simp [coordinateMatrixSupportSubmodule, Submodule.mem_comap, Submodule.mem_pi]
  rw [hsupp]
  constructor
  · intro h i j hij hk
    have hmem := h i j
    have hk' : ¬ (i.1 < k ∧ j.1 < k) := by
      omega
    simpa [hij, hk'] using hmem
  · intro h i j
    by_cases hij : i = j
    · simp [hij]
    · by_cases hk : i.1 < k ∧ j.1 < k
      · simp [hij, hk]
      · have hk' : k ≤ i.1 ∨ k ≤ j.1 := by
          omega
        simp [hij, hk, h i j hij hk']

/-- Definition 4.3.3: `coordinateSymmetricMatrixSubspace k n` is the coordinate subspace
`𝕊^{k,n}` of symmetric matrices whose off-diagonal entries vanish whenever one index lies beyond
the first `k` coordinates. -/
def coordinateSymmetricMatrixSubspace (k n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  selfAdjointMatricesSubmodule (1 : Matrix (Fin n) (Fin n) ℝ) ⊓ coordinateMatrixSupportSubmodule k n

scoped[CoordinateSymmetricMatrixSubspace] notation "𝕊^{" k "," n "}" =>
  coordinateSymmetricMatrixSubspace k n
open scoped CoordinateSymmetricMatrixSubspace

-- Proof sketch: `coordinateSymmetricMatrixSubspace` is the intersection of the canonical
-- symmetric-matrix submodule and the private coordinate-support submodule, so membership is the
-- conjunction of symmetry and the displayed off-diagonal vanishing criterion.
/-- Membership in `𝕊^{k,n}` means that the matrix is symmetric and
all off-diagonal entries vanish whenever one of the indices lies past the first `k` positions. -/
theorem mem_coordinateSymmetricMatrixSubspace_iff {H : Mat} {k : ℕ} :
    H ∈ 𝕊^{k,n} ↔
      H.IsSymm ∧
        ∀ i j : Fin n, i ≠ j → (k ≤ i.1 ∨ k ≤ j.1) → H i j = 0 := by
  rw [coordinateSymmetricMatrixSubspace, Submodule.mem_inf, mem_symmetricMatrixSubmodule_iff,
    mem_coordinateMatrixSupportSubmodule_iff]
