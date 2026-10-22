/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped MatrixOrder RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.44 lies in Chapter 7's real symmetric-matrix spectral-radius / semidefinite-order
domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n`, the project owner for real symmetric matrices;
- Chapter 5 `𝕊^n₊` and `mem_positiveSemidefiniteCone_iff`, the intrinsic positive-semidefinite cone
  and its bridge to `Matrix.PosSemidef`;
- Chapter 7 `ρ(X)` and
  `realSymmetricMatrix_toReal_spectralRadius_eq_iSup_abs_eigenvalues` in `Definition_7_17`, the
  canonical spectral-radius surface and its eigenvalue bridge;
- mathlib `Matrix.nonneg_iff_posSemidef`, the canonical proof-layer bridge from matrix order to
  positive semidefiniteness.

Best owner abstraction:
- source-facing: Definition 7.44's least semidefinite bound for the spectral radius;
- core/canonical: the chapter owners `𝕊^n`, `𝕊^n₊`, and the spectral-radius surface `ρ(X)`;
- bridge/view: the cone-membership inequalities `τ I_n ± X ∈ 𝕊^n₊`, equivalently the ambient
  matrix semidefinite conditions and the two-sided matrix-order bound `-τ I_n ≤ X ≤ τ I_n`.

Primitive data:
- `X : 𝕊^n`.

Derived API:
- the spectral-radius owner `ρ(X)`;
- the eigenvalue formula already provided by `Definition_7_17`;
- the semidefinite-bound theorem below, stated directly on `𝕊^n` via membership in `𝕊^n₊`.

This refinement removes the duplicate raw subtype `{M // M.IsSymm}` and the duplicate
Hermitian/eigenvalue bridge from this file. The public surface now grows from the existing chapter
owners `𝕊^n` and `𝕊^n₊`, and the new theorem keeps only the source-facing semidefinite
characterization that is not already owned upstream.
-/

/-- The nonnegative semidefinite cone bounds that dominate a symmetric matrix on both sides. -/
def realSymmetricMatrix_spectralRadiusSemidefiniteBounds
    (X : 𝕊^n) : Set ℝ :=
  {τ : ℝ |
    0 ≤ τ ∧
      τ • (1 : 𝕊^n) - X ∈ 𝕊^n₊ ∧
      τ • (1 : 𝕊^n) + X ∈ 𝕊^n₊}

/-- Helper for Definition 7.44: membership in the semidefinite-bound set is exactly the two-sided
ambient matrix order bound `-τ I ≤ X ≤ τ I`. -/
theorem mem_realSymmetricMatrix_spectralRadiusSemidefiniteBounds_iff
    {X : 𝕊^n} {τ : ℝ} :
    τ ∈ realSymmetricMatrix_spectralRadiusSemidefiniteBounds X ↔
      0 ≤ τ ∧ (-(τ • (1 : Mat)) ≤ (X : Mat)) ∧ ((X : Mat) ≤ τ • (1 : Mat)) := by
  rw [realSymmetricMatrix_spectralRadiusSemidefiniteBounds, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hτ, hUpperCone, hLowerCone⟩
    rw [mem_positiveSemidefiniteCone_iff] at hUpperCone hLowerCone
    refine ⟨hτ, ?_, ?_⟩
    · -- Convert `τ I + X ∈ 𝕊^n₊` into the lower matrix-order bound `-τ I ≤ X`.
      exact sub_nonneg.mp <| by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (Matrix.nonneg_iff_posSemidef).mpr hLowerCone
    · -- Convert `τ I - X ∈ 𝕊^n₊` into the upper matrix-order bound `X ≤ τ I`.
      exact sub_nonneg.mp <| by
        simpa using (Matrix.nonneg_iff_posSemidef).mpr hUpperCone
  · rintro ⟨hτ, hLower, hUpper⟩
    refine ⟨hτ, ?_, ?_⟩
    · -- Repackage the upper matrix-order bound as positivity of `τ I - X`.
      rw [mem_positiveSemidefiniteCone_iff]
      exact (Matrix.nonneg_iff_posSemidef).mp <| sub_nonneg.mpr hUpper
    · -- Repackage the lower matrix-order bound as positivity of `τ I + X`.
      rw [mem_positiveSemidefiniteCone_iff]
      exact (Matrix.nonneg_iff_posSemidef).mp <| by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          sub_nonneg.mpr hLower

/-- Helper for Definition 7.44: the spectral radius itself satisfies the two semidefinite
inequalities `ρ(X) I - X ∈ 𝕊^n₊` and `ρ(X) I + X ∈ 𝕊^n₊`. -/
theorem realSymmetricMatrix_spectralRadius_mem_semidefiniteBounds
    (X : 𝕊^n) :
    ρ(X) ∈ realSymmetricMatrix_spectralRadiusSemidefiniteBounds X := by
  let A : Mat := (X : Mat)
  have hSelfAdjoint : IsSelfAdjoint A := by
    simpa [A, Matrix.IsSelfAdjoint, Matrix.IsHermitian, Matrix.IsSymm] using
      RealSymmetricMatrixSpace.isHermitian X
  have hSpectrumEq :
      spectrum ℝ A = Set.range (RealSymmetricMatrixSpace.eigenvalues X) := by
    -- Real spectral points of a symmetric matrix are exactly its ordered eigenvalues.
    simpa [A, RealSymmetricMatrixSpace.eigenvalues] using
      (RealSymmetricMatrixSpace.isHermitian X).spectrum_real_eq_range_eigenvalues
  have hSpectrumAbsLe : ∀ x ∈ spectrum ℝ A, |x| ≤ ρ(X) := by
    intro x hx
    rw [hSpectrumEq] at hx
    rcases hx with ⟨i, rfl⟩
    -- Each eigenvalue is bounded by the supremum formula for `ρ(X)`.
    rw [realSymmetricMatrix_toReal_spectralRadius_eq_iSup_abs_eigenvalues]
    exact Finite.le_ciSup (fun j : Fin n ↦ |RealSymmetricMatrixSpace.eigenvalues X j|) i
  have hLower : -(ρ(X) • (1 : Mat)) ≤ A := by
    -- Spectral points bounded below by `-ρ(X)` give the lower matrix-order bound.
    have hLower' : algebraMap ℝ Mat (-ρ(X)) ≤ A :=
      algebraMap_le_of_le_spectrum
        (a := A) (r := -ρ(X))
        (ha := hSelfAdjoint)
        (fun x hx ↦ (abs_le.mp (hSpectrumAbsLe x hx)).1)
    simpa [A, Algebra.algebraMap_eq_smul_one] using hLower'
  have hUpper : A ≤ ρ(X) • (1 : Mat) := by
    -- Spectral points bounded above by `ρ(X)` give the upper matrix-order bound.
    have hUpper' : A ≤ algebraMap ℝ Mat (ρ(X)) :=
      le_algebraMap_of_spectrum_le
        (a := A) (r := ρ(X))
        (ha := hSelfAdjoint)
        (fun x hx ↦ (abs_le.mp (hSpectrumAbsLe x hx)).2)
    simpa [A, Algebra.algebraMap_eq_smul_one] using hUpper'
  rw [mem_realSymmetricMatrix_spectralRadiusSemidefiniteBounds_iff]
  refine ⟨?_, hLower, hUpper⟩
  -- The chapter spectral radius is an `ENNReal.toReal`, so it is automatically nonnegative.
  exact ENNReal.toReal_nonneg

/-- Helper for Definition 7.44: any admissible semidefinite bound `τ` dominates the absolute value
of every eigenvalue of `X`. -/
theorem eigenvalue_abs_le_of_semidefinite_bound
    {X : 𝕊^n} {τ : ℝ}
    (hτ : τ ∈ realSymmetricMatrix_spectralRadiusSemidefiniteBounds X)
    (i : Fin n) :
    |RealSymmetricMatrixSpace.eigenvalues X i| ≤ τ := by
  let A : Mat := (X : Mat)
  have hSelfAdjoint : IsSelfAdjoint A := by
    simpa [A, Matrix.IsSelfAdjoint, Matrix.IsHermitian, Matrix.IsSymm] using
      RealSymmetricMatrixSpace.isHermitian X
  rw [mem_realSymmetricMatrix_spectralRadiusSemidefiniteBounds_iff] at hτ
  rcases hτ with ⟨_, hLower, hUpper⟩
  have hSpectrumUpper : ∀ x ∈ spectrum ℝ A, x ≤ τ := by
    -- The upper matrix-order bound forces every spectral value to lie below `τ`.
    have hUpper' : A ≤ algebraMap ℝ Mat τ := by
      simpa [A, Algebra.algebraMap_eq_smul_one] using hUpper
    exact (le_algebraMap_iff_spectrum_le (a := A) (r := τ) (ha := hSelfAdjoint)).mp hUpper'
  have hSpectrumLower : ∀ x ∈ spectrum ℝ A, -τ ≤ x := by
    -- The lower matrix-order bound forces every spectral value to lie above `-τ`.
    have hLower' : algebraMap ℝ Mat (-τ) ≤ A := by
      simpa [A, Algebra.algebraMap_eq_smul_one] using hLower
    exact
      (algebraMap_le_iff_le_spectrum (a := A) (r := -τ) (ha := hSelfAdjoint)).mp hLower'
  have hEigenvalue :
      RealSymmetricMatrixSpace.eigenvalues X i ∈ spectrum ℝ A := by
    -- Hermitian eigenvalues are real spectral points of the ambient matrix.
    simpa [A, RealSymmetricMatrixSpace.eigenvalues] using
      (RealSymmetricMatrixSpace.isHermitian X).eigenvalues_mem_spectrum_real i
  exact abs_le.mpr ⟨hSpectrumLower _ hEigenvalue, hSpectrumUpper _ hEigenvalue⟩

/-- Helper for Definition 7.44: every admissible semidefinite bound `τ` is at least the spectral
radius. -/
theorem realSymmetricMatrix_spectralRadius_le_of_semidefiniteBound
    {X : 𝕊^n} {τ : ℝ}
    (hτ : τ ∈ realSymmetricMatrix_spectralRadiusSemidefiniteBounds X) :
    ρ(X) ≤ τ := by
  -- Rewrite `ρ(X)` as the supremum of the absolute eigenvalues and bound each term by `τ`.
  rw [realSymmetricMatrix_toReal_spectralRadius_eq_iSup_abs_eigenvalues]
  by_cases hNonempty : Nonempty (Fin n)
  · letI := hNonempty
    exact ciSup_le fun i : Fin n ↦ eigenvalue_abs_le_of_semidefinite_bound hτ i
  · have hτ_nonneg :
        0 ≤ τ := (mem_realSymmetricMatrix_spectralRadiusSemidefiniteBounds_iff.mp hτ).1
    letI : IsEmpty (Fin n) := not_nonempty_iff.mp hNonempty
    rw [iSup_of_empty']
    simpa using hτ_nonneg

/-- Definition 7.44: for a real symmetric matrix, the spectral radius is the least nonnegative
real scalar `τ` such that both symmetric matrices `τ I_n - X` and `τ I_n + X` lie in the
positive-semidefinite cone `𝕊^n₊`. -/
-- Proof sketch: use the Chapter 7 owner `ρ(X)` from `Definition_7_17`, rewrite the spectral
-- radius as the operator norm of the associated self-adjoint matrix, apply the standard
-- two-sided order characterization `-τ I ≤ X ≤ τ I`, and translate those order inequalities to
-- intrinsic cone membership in `𝕊^n₊` via `Matrix.nonneg_iff_posSemidef` together with
-- `mem_positiveSemidefiniteCone_iff`. Stating the admissible set over nonnegative scalars keeps
-- the canonical least-bound surface and removes the artificial `n > 0` side condition: when
-- `n = 0`, the cone constraints are vacuous but the extra bound `0 ≤ τ` makes `0` the least
-- admissible scalar.
theorem realSymmetricMatrix_toReal_spectralRadius_isLeast_semidefiniteBound
    (X : 𝕊^n) :
    IsLeast (realSymmetricMatrix_spectralRadiusSemidefiniteBounds X) ρ(X) := by
  refine ⟨realSymmetricMatrix_spectralRadius_mem_semidefiniteBounds (X := X), ?_⟩
  -- Once `ρ(X)` is known to be admissible, minimality is exactly the universal bound lemma.
  intro τ hτ
  exact realSymmetricMatrix_spectralRadius_le_of_semidefiniteBound (X := X) hτ

end
