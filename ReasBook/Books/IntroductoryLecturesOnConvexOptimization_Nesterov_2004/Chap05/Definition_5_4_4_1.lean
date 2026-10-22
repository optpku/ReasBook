/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

/- Definition 5.4.4.1 is a recall-only item in the real symmetric-matrix domain.

Layer targeted by this refinement:
- source-facing recall of the core/canonical symmetric-matrix submodule.

Primary domain:
- the real vector space `𝕊^n` of symmetric `n × n` matrices.

Sampled owner-style declarations:
- mathlib `selfAdjointMatricesSubmodule`
- mathlib `mem_selfAdjointMatricesSubmodule`
- mathlib `Matrix.IsSymm`
- mathlib `Matrix.IsSymm.eq`

Best owner abstraction:
- source-facing: the vector space `𝕊^n` of real symmetric matrices;
- core/canonical: `selfAdjointMatricesSubmodule (1 : Matrix (Fin n) (Fin n) ℝ)`;
- bridge/view: membership rewritten as `Matrix.IsSymm`, equivalently `Xᵀ = X`.

Primitive data:
- `n : ℕ`

Derived API:
- the canonical symmetric-matrix owner `selfAdjointMatricesSubmodule`
- the source-facing notation `𝕊^n`
- the owner-branded symmetry bridge `RealSymmetricMatrixSpace.mem_iff_isSymm`
- the owner-branded transpose bridge `RealSymmetricMatrixSpace.mem_iff_transpose_eq`

This file therefore removes the duplicate local definition `realSymmetricMatrixSubspace` and
reuses the matrix-specific canonical owner directly. The textbook surface is then recovered by
thin owner-branded companion lemmas on `𝕊^n`, written directly in `Matrix.IsSymm` / `Xᵀ = X`
form. -/

recall selfAdjointMatricesSubmodule
recall mem_selfAdjointMatricesSubmodule

scoped[RealSymmetricMatrixSpace] notation:arg "𝕊^" n:arg =>
  selfAdjointMatricesSubmodule (1 : Matrix (Fin n) (Fin n) ℝ)
open scoped RealSymmetricMatrixSpace

section

variable (n : ℕ)

/- Definition 5.4.4.1: the vector space `𝕊^n` of real symmetric matrices is the canonical
self-adjoint submodule specialized to real square matrices. -/
#check (𝕊^n : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))

end

section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

namespace RealSymmetricMatrixSpace

/-- Membership in `𝕊^n` is exactly symmetry. -/
theorem mem_iff_isSymm
    {X : Mat} :
    X ∈ 𝕊^n ↔ X.IsSymm := by
  rw [mem_selfAdjointMatricesSubmodule]
  simp [Matrix.IsSelfAdjoint, Matrix.IsAdjointPair, Matrix.IsSymm]

/-- Membership in `𝕊^n` is exactly the equation `Xᵀ = X`. -/
theorem mem_iff_transpose_eq
    {X : Mat} :
    X ∈ 𝕊^n ↔ Xᵀ = X := by
  simpa [Matrix.IsSymm] using
    (mem_iff_isSymm :
      X ∈ 𝕊^n ↔ X.IsSymm)

/-- A point of `𝕊^n` is symmetric as an ambient real matrix. -/
theorem isSymm (X : 𝕊^n) :
    ((X : 𝕊^n) : Mat).IsSymm :=
  mem_iff_isSymm.mp X.2

end RealSymmetricMatrixSpace

end

/-- The identity matrix is a canonical element of `𝕊^n`. -/
instance {n : ℕ} : One (𝕊^n) where
  one := ⟨1, by
    rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
    exact Matrix.isSymm_one⟩

/-- The numeral `1` on `𝕊^n` is the identity matrix. -/
instance {n : ℕ} : OfNat (𝕊^n) 1 where
  ofNat := (1 : 𝕊^n)

noncomputable section

namespace RealSymmetricMatrixSpace

@[simp] theorem coe_one
    {n : ℕ} :
    ((1 : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ) = 1 :=
  rfl

/-- A real symmetric matrix in `𝕊^n` is Hermitian. -/
theorem isHermitian
    {n : ℕ} (X : 𝕊^n) :
    ((X : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using
    isSymm X

/-- The intrinsic eigenvalue list of a real symmetric matrix in `𝕊^n`. -/
abbrev eigenvalues
    {n : ℕ} (X : 𝕊^n) :
    Fin n → ℝ :=
  (isHermitian X).eigenvalues

/-- The determinant of a real symmetric matrix is the product of its intrinsic eigenvalues. -/
theorem det_eq_prod_eigenvalues
    {n : ℕ} (X : 𝕊^n) :
    ((X : Matrix (Fin n) (Fin n) ℝ)).det =
      ∏ i : Fin n, eigenvalues X i := by
  simpa using (isHermitian X).det_eq_prod_eigenvalues

end RealSymmetricMatrixSpace

end
