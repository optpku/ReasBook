/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open RealSymmetricMatrixSpace
open scoped RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.17 lies in Chapter 7's symmetric-matrix spectral-radius domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n`, the chapter owner for real symmetric matrices;
- Chapter 5 `RealSymmetricMatrixSpace.eigenvalues`, the derived ordered-eigenvalue API on `𝕊^n`;
- mathlib `spectralRadius`, the canonical spectral-radius owner;
- mathlib `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`, the Hermitian-to-eigenvalue
  bridge behind the source-facing formula.

Best owner abstraction:
- source-facing: the real-valued spectral radius of a symmetric matrix;
- core/canonical: `spectralRadius`;
- bridge/view: the eigenvalue-supremum theorem below, expressed through the chapter owner
  `eigenvalues`.

Primitive data:
- `X : 𝕊^n`

Derived API:
- the source-facing notation `ρ(X)` for the real-valued spectral radius
- the ordered eigenvalue family `eigenvalues X`

Source/core/bridge triage:
- source-facing: Definition 7.17's real-valued spectral-radius surface on `𝕊^n`;
- core/canonical: `spectralRadius`;
- bridge/view: `realSymmetricMatrix_toReal_spectralRadius_eq_iSup_abs_eigenvalues`.

This file therefore removes the duplicate public alias `symmetricMatrixSpectralRadius`, keeps the
canonical owner `spectralRadius`, and adds the textbook source-facing notation `ρ(X)` on the
chapter carrier `𝕊^n`. The eigenvalue formula remains expressed via the existing Chapter 5 owner
`eigenvalues`.
-/

scoped[RealSymmetricMatrixSpace] notation "ρ(" X ")" =>
  ENNReal.toReal (spectralRadius ℝ (Subtype.val X))

section

variable (n : ℕ)

/- Definition 7.17: for `X ∈ 𝕊^n`, the spectral radius is the real number `ρ(X)`. -/
#check (fun X : 𝕊^n ↦ ρ(X))

end

-- Proof sketch: the Hermitian spectral theorem identifies the real spectrum of a symmetric
-- matrix with its ordered eigenvalues, and the spectral radius is the supremum of the absolute
-- values of spectral points.
/-- Helper for Definition 7.17: the real spectrum of a symmetric matrix is the range of its
ordered eigenvalue family `eigenvalues X`. -/
theorem realSymmetricMatrixSpectrumEqRangeEigenvalues
    (X : 𝕊^n) :
    spectrum ℝ (X : Mat) = Set.range (RealSymmetricMatrixSpace.eigenvalues X) := by
  -- The Hermitian spectral theorem gives the exact bridge from spectral points to eigenvalues.
  simpa [RealSymmetricMatrixSpace.eigenvalues] using
    (RealSymmetricMatrixSpace.isHermitian X).spectrum_real_eq_range_eigenvalues

/-- The spectral radius of a real symmetric matrix is the maximum absolute value of its
eigenvalues, written as a supremum over the finite index type `Fin n`. -/
theorem realSymmetricMatrix_toReal_spectralRadius_eq_iSup_abs_eigenvalues
    (X : 𝕊^n) :
    ρ(X) = ⨆ i : Fin n, |eigenvalues X i| := by
  -- Rewrite the ambient spectral radius through the Hermitian spectrum/eigenvalue bridge.
  rw [spectralRadius, realSymmetricMatrixSpectrumEqRangeEigenvalues X, iSup_range]
  -- The remaining supremum is indexed directly by the ordered eigenvalues.
  rw [ENNReal.toReal_iSup]
  · simp [Real.norm_eq_abs]
  · intro i
    simp
