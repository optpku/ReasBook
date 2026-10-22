/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_1
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped MatrixOrder NNReal RealInnerProductSpace RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n

/- Definition 5.4.4.3 lies in the real symmetric-matrix positivity domain.

Layer targeted by this refinement:
- source-facing: the textbook cone notation `𝕊^n₊` inside the symmetric carrier `𝕊^n`;
- core/canonical: `Matrix.PosSemidef` and `Matrix.PosDef`;
- bridge/view: coercion from `𝕊^n` to matrices and quadratic-form characterizations through
  `Matrix.toEuclideanLin`.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` from `Definition_5_4_4_1`, the symmetric-matrix owner;
- mathlib `Matrix.PosSemidef`, the canonical positive-semidefinite matrix predicate;
- mathlib `selfAdjoint.submodule`, the canonical carrier behind `𝕊^n`;
- mathlib `Matrix.isPositive_toEuclideanLin_iff`, the Euclidean-operator positivity bridge;
- mathlib `Matrix.PosDef.of_dotProduct_mulVec_pos` and `Matrix.PosDef.dotProduct_mulVec_pos`,
  the positive-definite owner API.

Primitive data:
- `n : ℕ`

Derived API:
- the source-facing notation `𝕊^n₊ : Set (𝕊^n)`;
- the owner bridge `X ∈ 𝕊^n₊ ↔ (X : Mat).PosSemidef`;
- the intrinsic cone bridge `PositiveSemidefiniteCone.nnrpow X p` for nonnegative powers of PSD
  matrices;
- the quadratic-form and positive-definite companion characterizations.

This file therefore deletes the duplicate local owner `positiveSemidefiniteCone`, keeps the
textbook cone notation on the intrinsic symmetric carrier `𝕊^n`, avoids any public
Euclidean-array realization wrapper, and derives the rest of the API from the canonical
matrix-positivity owners.
-/

recall Matrix.PosSemidef
recall Matrix.isPositive_toEuclideanLin_iff

set_option quotPrecheck false in
scoped[RealSymmetricMatrixSpace] notation:arg "𝕊^" n:arg "₊" =>
  ({X : 𝕊^n | ((X : Matrix (Fin n) (Fin n) ℝ)).PosSemidef} : Set (𝕊^n))

section

variable (n : ℕ)

/- Definition 5.4.4.3: the cone `𝕊ⁿ₊` of positive semidefinite real symmetric `n × n` matrices
is the canonical subset of the symmetric carrier `𝕊^n` cut out by `Matrix.PosSemidef`. -/
#check (𝕊^n₊ : Set (𝕊^n))

end

/-- Membership in `𝕊ⁿ₊` is exactly the canonical predicate `Matrix.PosSemidef`. -/
@[simp] theorem mem_positiveSemidefiniteCone_iff
    (X : SymmMat) :
    X ∈ 𝕊^n₊ ↔ (X : Mat).PosSemidef :=
  Iff.rfl

namespace PositiveSemidefiniteCone

private theorem nnrpow_posSemidef
    (X : 𝕊^n₊) (p : ℝ≥0) :
    ((((X : SymmMat) : Mat) ^ p) : Mat).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (show 0 ≤ ((((X : SymmMat) : Mat) ^ p) : Mat) by
      exact CFC.nnrpow_nonneg)

private theorem nnrpow_mem_symm
    (X : 𝕊^n₊) (p : ℝ≥0) :
    ((((X : SymmMat) : Mat) ^ p) : Mat) ∈ 𝕊^n := by
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using
    (nnrpow_posSemidef X p).isHermitian

/-- The ambient nonnegative real power of a positive-semidefinite symmetric matrix, viewed back
in `𝕊^n₊`. -/
def nnrpow
    (X : 𝕊^n₊) (p : ℝ≥0) : 𝕊^n₊ :=
  ⟨⟨(((X : SymmMat) : Mat) ^ p), nnrpow_mem_symm X p⟩, nnrpow_posSemidef X p⟩

/-- The textbook nonnegative real power notation on `𝕊^n₊` is induced by `nnrpow`. -/
instance : Pow (𝕊^n₊) ℝ≥0 where
  pow X p := nnrpow X p

@[simp] theorem pow_eq_nnrpow
    (X : 𝕊^n₊) (p : ℝ≥0) :
    X ^ p = nnrpow X p :=
  rfl

@[simp] theorem coe_nnrpow
    (X : 𝕊^n₊) (p : ℝ≥0) :
    (((nnrpow X p : SymmMat) : Mat)) = (((X : SymmMat) : Mat) ^ p) :=
  rfl

@[simp] theorem coe_pow
    (X : 𝕊^n₊) (p : ℝ≥0) :
    (((X ^ p : 𝕊^n₊) : SymmMat) : Mat) = (((X : SymmMat) : Mat) ^ p) :=
  rfl

end PositiveSemidefiniteCone

-- Proof sketch: unfold membership in `𝕊^n₊`; then use the real-matrix characterization of
-- `Matrix.PosSemidef` by nonnegativity of the quadratic form `u ↦ ⟪Xu, u⟫`; the symmetry part is
-- already built into the carrier `𝕊^n`.
/-- For a symmetric matrix, membership in the positive-semidefinite cone is equivalent to
nonnegativity of the quadratic form `u ↦ ⟪Xu, u⟫` on `ℝⁿ`. -/
theorem mem_positiveSemidefiniteCone_iff_inner_nonneg
    (X : SymmMat) :
    X ∈ 𝕊^n₊ ↔ ∀ u : E, 0 ≤ ⟪(X : Mat).toEuclideanLin u, u⟫ := by
  rw [mem_positiveSemidefiniteCone_iff, ← Matrix.isPositive_toEuclideanLin_iff,
    LinearMap.isPositive_iff]
  constructor
  · rintro ⟨_, hpos⟩
    exact hpos
  · intro hpos
    refine ⟨?_, hpos⟩
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr <|
      by simpa [Matrix.IsHermitian, Matrix.IsSymm] using
        RealSymmetricMatrixSpace.isHermitian X

-- Proof sketch: apply the standard characterization of `Matrix.PosDef`; under the symmetry
-- built into `𝕊^n`, positivity of the quadratic form on all nonzero vectors is exactly the
-- textbook condition.
/-- A real symmetric matrix is positive definite exactly when its quadratic form is positive on
every nonzero vector. -/
theorem matrix_posDef_iff_forall_inner_pos
    (X : SymmMat) :
    (X : Mat).PosDef ↔ ∀ u : E, u ≠ 0 → 0 < ⟪(X : Mat).toEuclideanLin u, u⟫ := by
  constructor
  · intro hPos u hu
    have hu' : u.ofLp ≠ 0 := by
      simpa using hu
    have hquad := hPos.dotProduct_mulVec_pos hu'
    simpa using hquad
  · intro hquad
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun {u} hu ↦ ?_
    · simpa using RealSymmetricMatrixSpace.isHermitian X
    · let uE : E := (EuclideanSpace.equiv (Fin n) ℝ).symm u
      have huE : uE ≠ 0 := by
        intro huE0
        apply hu
        simpa [uE] using congrArg (EuclideanSpace.equiv (Fin n) ℝ) huE0
      have h := hquad uE huE
      simpa [uE] using h

end
