/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open RealSymmetricMatrixSpace
open scoped MatrixOrder RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 6.41 lies in the chapter's real symmetric-matrix spectral-calculus domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` and `RealSymmetricMatrixSpace.eigenvalues`, the canonical carrier and ordered
  eigenvalue owner for real symmetric matrices;
- Chapter 5 `⟪·, ·⟫_F`, the existing Frobenius inner-product owner on `𝕊^n`;
- mathlib `Matrix.diagonal`, the canonical diagonal-matrix owner already matching the textbook
  notation `D(λ)`;
- mathlib `CFC.abs`, the canonical functional-calculus absolute value on self-adjoint matrices;
- mathlib `WithLp.toLp`, the canonical finite-dimensional `ℓ_p` owner for vectors indexed by
  `Fin n`.

Best owner abstraction:
- source-facing: the symmetric-matrix absolute value `|X|` and the spectral `p`-norm
  `‖X‖_(p)` on `𝕊^n`;
- core/canonical: `𝕊^n`, `eigenvalues`, `CFC.abs`, and `WithLp.toLp`;
- bridge/view: the ambient matrix order statement `0 ≤ |X|` and the eigenvalue-norm formulas.

Primitive data:
- the chapter carrier `𝕊^n` from Chapter 5;
- a spectral exponent `p ∈ [1, ∞]`.

Derived API:
- the source-facing absolute-value owner `RealSymmetricMatrixSpace.abs`, written `|X|`;
- the source-facing spectral `p`-norm owner `symmetricMatrixSpectralPNorm`;
- the bridge theorem rewriting `‖X‖_(p)` through the eigenvalues of `|X|`.

This refinement reuses the canonical Chapter 5 symmetric-matrix carrier and eigenvalue owner,
keeps the textbook absolute value as a source-facing operation on `𝕊^n`, and defines the matrix
spectral `p`-norm directly from the `WithLp` norm of the ordered eigenvalue vector. It does not
introduce a public owner for the auxiliary diagonalization matrix `U(X)`, since that choice is
noncanonical and serves only to describe the same intrinsic functional-calculus construction.
-/

namespace RealSymmetricMatrixSpace

-- Proof sketch: `CFC.abs` preserves self-adjointness. Specializing the ambient matrix order to
-- real matrices, the ambient absolute value of a symmetric matrix is Hermitian and therefore
-- symmetric, so it lies back in `𝕊^n`.
/-- The ambient functional-calculus absolute value of a real symmetric matrix is again a point of
`𝕊^n`. -/
private theorem abs_mem (X : SymmMat) :
    CFC.abs (X : Mat) ∈ 𝕊^n := by
  -- Rewrite membership in `𝕊^n` as symmetry and read it off from positivity of `CFC.abs X`.
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using
    (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).isHermitian

/-- The source-facing absolute value on `𝕊^n`, induced by the ambient functional-calculus absolute
value. -/
def abs (X : SymmMat) : SymmMat :=
  ⟨CFC.abs (X : Mat), abs_mem X⟩

/- Lean surface notation for the textbook matrix absolute value on `𝕊^n`. -/
scoped macro:max "|" x:term:max "|" : term => `(RealSymmetricMatrixSpace.abs $x)

-- Proof sketch: unfold `RealSymmetricMatrixSpace.abs`; the subtype carrier is definitionally the
-- ambient matrix absolute value `CFC.abs (X : Mat)`.
/-- Expanding `|X|` on `𝕊^n` recovers the ambient functional-calculus absolute value. -/
@[simp] theorem coe_abs (X : SymmMat) :
    ((|X| : SymmMat) : Mat) = CFC.abs (X : Mat) :=
  rfl

-- Proof sketch: `CFC.abs_nonneg` gives the ambient matrix-order nonnegativity of `CFC.abs (X)`,
-- and `coe_abs` identifies this ambient matrix with the source-facing matrix `|X|`.
/-- The source-facing absolute value `|X|` is positive semidefinite in the ambient matrix order. -/
theorem abs_nonneg (X : SymmMat) :
    0 ≤ ((|X| : SymmMat) : Mat) := by
  -- The subtype wrapper for `|X|` is definitionally the ambient `CFC.abs X`.
  rw [RealSymmetricMatrixSpace.coe_abs]
  exact CFC.abs_nonneg (X : Mat)

end RealSymmetricMatrixSpace

/-- For `p ∈ [1, ∞]`, Definition 6.41 [Chapter6_2.json:96] defines the spectral `p`-norm of a
real symmetric matrix `X ∈ 𝕊^n` as the `ℓ_p` norm of its ordered eigenvalue vector `λ(X)`. The
Frobenius pairing and the auxiliary diagonal matrix notation `D(λ)` are reused from the canonical
Chapter 5 Frobenius owner and mathlib's diagonal-matrix API. -/
def symmetricMatrixSpectralPNorm
    (p : Set.Ici (1 : ENNReal)) (X : SymmMat) : ℝ :=
  ‖WithLp.toLp (p : ENNReal) (eigenvalues X)‖

-- Proof sketch: unfold `symmetricMatrixSpectralPNorm`; the right-hand side is exactly the
-- defining `WithLp` norm of the ordered eigenvalue vector.
/-- Expanding `symmetricMatrixSpectralPNorm p X` gives the `ℓ_p` norm of the ordered eigenvalue
vector `λ(X)`. -/
theorem symmetricMatrixSpectralPNorm_eq_eigenvalueNorm
    (p : Set.Ici (1 : ENNReal)) (X : SymmMat) :
    symmetricMatrixSpectralPNorm p X =
      ‖WithLp.toLp (p : ENNReal) (eigenvalues X)‖ :=
  rfl

/-- Helper for Definition 6.41: tracing the Hermitian functional calculus of a symmetric matrix
applies the scalar function to the ordered eigenvalues and sums the result. -/
private theorem traceCfcEqSumMapEigenvalues
    (Q : SymmMat) (f : ℝ → ℝ) :
    Matrix.trace ((isHermitian Q).cfc f) = ∑ i : Fin n, f (eigenvalues Q i) := by
  -- Rewrite the functional calculus into diagonal form in the orthonormal eigenbasis.
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [Function.comp]

/-- Helper for Definition 6.41: the `ℓ_p` norm of the ordered eigenvalues is unchanged when `X`
is replaced by its intrinsic absolute value `|X|`. -/
private theorem absEigenvalueLpNormEqOriginal
    (p : Set.Ici (1 : ENNReal)) (X : SymmMat) :
    ‖WithLp.toLp (p : ENNReal) (eigenvalues (|X| : SymmMat))‖ =
      ‖WithLp.toLp (p : ENNReal) (eigenvalues X)‖ := by
  -- Route correction: the ordered eigenvalue vectors are not componentwise equal after `abs`, so
  -- we compare finite `p` norms by trace/cfc and the `∞` norm by spectrum/range equality.
  by_cases hpTop : (p : ENNReal) = ⊤
  · -- In the `∞` branch, the PiLp norm is the supremum norm, so set-level spectral mapping
    -- suffices once both sides are rewritten as ranges of eigenvalues.
    have hpTop' : p = ⟨(⊤ : ENNReal), by simp⟩ := by
      apply Subtype.ext
      simpa using hpTop
    subst hpTop'
    have hnormAbs :
        ‖WithLp.toLp (⊤ : ENNReal) (eigenvalues (|X| : SymmMat))‖ =
          ⨆ i : Fin n, ‖eigenvalues (|X| : SymmMat) i‖ := by
      simpa using
        (PiLp.norm_eq_ciSup (WithLp.toLp (⊤ : ENNReal) (eigenvalues (|X| : SymmMat))))
    have hnormX :
        ‖WithLp.toLp (⊤ : ENNReal) (eigenvalues X)‖ =
          ⨆ i : Fin n, ‖eigenvalues X i‖ := by
      simpa using
        (PiLp.norm_eq_ciSup (WithLp.toLp (⊤ : ENNReal) (eigenvalues X)))
    have habs_nonneg : ∀ i : Fin n, 0 ≤ eigenvalues (|X| : SymmMat) i := by
      intro i
      exact
        (Matrix.nonneg_iff_posSemidef.mp
          (RealSymmetricMatrixSpace.abs_nonneg X)).eigenvalues_nonneg i
    have hself : IsSelfAdjoint (X : Mat) := by
      simpa using (isHermitian X)
    have hrange :
        Set.range (fun i : Fin n ↦ ‖eigenvalues (|X| : SymmMat) i‖) =
          Set.range (fun i : Fin n ↦ ‖eigenvalues X i‖) := by
      calc
        Set.range (fun i : Fin n ↦ ‖eigenvalues (|X| : SymmMat) i‖)
            = Set.range (eigenvalues (|X| : SymmMat)) := by
                ext x
                constructor
                · rintro ⟨i, rfl⟩
                  refine ⟨i, ?_⟩
                  simp [Real.norm_eq_abs, abs_of_nonneg (habs_nonneg i)]
                · rintro ⟨i, rfl⟩
                  refine ⟨i, ?_⟩
                  simp [Real.norm_eq_abs, abs_of_nonneg (habs_nonneg i)]
        _ = spectrum ℝ (((|X| : SymmMat) : Mat)) := by
              symm
              rw [(isHermitian (|X| : SymmMat)).spectrum_real_eq_range_eigenvalues]
        _ = spectrum ℝ (CFC.abs (X : Mat)) := by
              simp [RealSymmetricMatrixSpace.coe_abs]
        _ = (fun z : ℝ ↦ ‖z‖) '' spectrum ℝ (X : Mat) := by
              simpa using (CFC.spectrum_abs (X : Mat) hself)
        _ = (fun z : ℝ ↦ ‖z‖) '' Set.range (eigenvalues X) := by
              rw [(isHermitian X).spectrum_real_eq_range_eigenvalues]
        _ = Set.range (fun i : Fin n ↦ ‖eigenvalues X i‖) := by
              ext x
              constructor
              · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
                exact ⟨i, rfl⟩
              · rintro ⟨i, rfl⟩
                exact ⟨eigenvalues X i, ⟨i, rfl⟩, rfl⟩
    calc
      ‖WithLp.toLp (⊤ : ENNReal) (eigenvalues (|X| : SymmMat))‖
          = ⨆ i : Fin n, ‖eigenvalues (|X| : SymmMat) i‖ := hnormAbs
      _ = ⨆ i : Fin n, ‖eigenvalues X i‖ := by
            by_cases hne : Nonempty (Fin n)
            · letI := hne
              apply le_antisymm
              · refine ciSup_le ?_
                intro i
                have hi :
                    ‖eigenvalues (|X| : SymmMat) i‖ ∈
                      Set.range (fun j : Fin n ↦ ‖eigenvalues X j‖) := by
                  rw [← hrange]
                  exact ⟨i, rfl⟩
                rcases hi with ⟨j, hj⟩
                simpa [hj] using
                  (le_ciSup (Set.finite_range (fun j : Fin n ↦ ‖eigenvalues X j‖)).bddAbove j)
              · refine ciSup_le ?_
                intro i
                have hi :
                    ‖eigenvalues X i‖ ∈
                      Set.range (fun j : Fin n ↦ ‖eigenvalues (|X| : SymmMat) j‖) := by
                  rw [hrange]
                  exact ⟨i, rfl⟩
                rcases hi with ⟨j, hj⟩
                exact
                  by
                    simpa [hj] using
                      (le_ciSup
                        (Set.finite_range
                          (fun j : Fin n ↦ ‖eigenvalues (|X| : SymmMat) j‖)).bddAbove j)
            · letI : IsEmpty (Fin n) := not_nonempty_iff.mp hne
              simp
      _ = ‖WithLp.toLp (⊤ : ENNReal) (eigenvalues X)‖ := hnormX.symm
  · -- In the finite-`p` branch, compare the `p`th power sums through the trace of the continuous
    -- functional calculus, using `cfc_comp_norm` to pass from `X` to `|X|`.
    have hp_ne_zero : (p : ENNReal) ≠ 0 := by
      exact pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one p.property)
    have hp_toReal_pos : 0 < (p : ENNReal).toReal :=
      ENNReal.toReal_pos hp_ne_zero hpTop
    have habs_nonneg : ∀ i : Fin n, 0 ≤ eigenvalues (|X| : SymmMat) i := by
      intro i
      exact
        (Matrix.nonneg_iff_posSemidef.mp
          (RealSymmetricMatrixSpace.abs_nonneg X)).eigenvalues_nonneg i
    have hself : IsSelfAdjoint (X : Mat) := by
      simpa using (isHermitian X)
    have hsum :
        ∑ i : Fin n, ‖eigenvalues (|X| : SymmMat) i‖ ^ (p : ENNReal).toReal =
          ∑ i : Fin n, ‖eigenvalues X i‖ ^ (p : ENNReal).toReal := by
      calc
        ∑ i : Fin n, ‖eigenvalues (|X| : SymmMat) i‖ ^ (p : ENNReal).toReal
            = ∑ i : Fin n, (eigenvalues (|X| : SymmMat) i) ^ (p : ENNReal).toReal := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [Real.norm_eq_abs, abs_of_nonneg (habs_nonneg i)]
        _ = Matrix.trace
              ((isHermitian (|X| : SymmMat)).cfc
                (fun x : ℝ ↦ x ^ (p : ENNReal).toReal)) := by
              symm
              exact
                traceCfcEqSumMapEigenvalues
                  (|X| : SymmMat) (fun x : ℝ ↦ x ^ (p : ENNReal).toReal)
        _ = Matrix.trace (cfc (fun x : ℝ ↦ ‖x‖ ^ (p : ENNReal).toReal) (X : Mat)) := by
              calc
                Matrix.trace
                    ((isHermitian (|X| : SymmMat)).cfc
                      (fun x : ℝ ↦ x ^ (p : ENNReal).toReal))
                    =
                    Matrix.trace
                      (cfc (fun x : ℝ ↦ x ^ (p : ENNReal).toReal)
                        (((|X| : SymmMat) : Mat))) := by
                        rw [(isHermitian (|X| : SymmMat)).cfc_eq]
                _ = Matrix.trace
                      (cfc (fun x : ℝ ↦ x ^ (p : ENNReal).toReal)
                        (CFC.abs (X : Mat))) := by
                      simp [RealSymmetricMatrixSpace.coe_abs]
                _ = Matrix.trace (cfc (fun x : ℝ ↦ ‖x‖ ^ (p : ENNReal).toReal) (X : Mat)) := by
                      simpa using
                        congrArg Matrix.trace
                          ((cfc_comp_norm
                            (fun x : ℝ ↦ x ^ (p : ENNReal).toReal)
                            (X : Mat) hself).symm)
        _ = Matrix.trace ((isHermitian X).cfc fun x : ℝ ↦ ‖x‖ ^ (p : ENNReal).toReal) := by
              rw [(isHermitian X).cfc_eq]
        _ = ∑ i : Fin n, ‖eigenvalues X i‖ ^ (p : ENNReal).toReal :=
              traceCfcEqSumMapEigenvalues X (fun x : ℝ ↦ ‖x‖ ^ (p : ENNReal).toReal)
    have hnormAbs :
        ‖WithLp.toLp (p : ENNReal) (eigenvalues (|X| : SymmMat))‖ =
          (∑ i : Fin n, ‖eigenvalues (|X| : SymmMat) i‖ ^ (p : ENNReal).toReal) ^
            (1 / (p : ENNReal).toReal) := by
      simpa using
        (PiLp.norm_eq_sum hp_toReal_pos
          (WithLp.toLp (p : ENNReal) (eigenvalues (|X| : SymmMat))))
    have hnormX :
        ‖WithLp.toLp (p : ENNReal) (eigenvalues X)‖ =
          (∑ i : Fin n, ‖eigenvalues X i‖ ^ (p : ENNReal).toReal) ^
            (1 / (p : ENNReal).toReal) := by
      simpa using
        (PiLp.norm_eq_sum hp_toReal_pos
          (WithLp.toLp (p : ENNReal) (eigenvalues X)))
    calc
      ‖WithLp.toLp (p : ENNReal) (eigenvalues (|X| : SymmMat))‖
          = (∑ i : Fin n, ‖eigenvalues (|X| : SymmMat) i‖ ^ (p : ENNReal).toReal) ^
              (1 / (p : ENNReal).toReal) := hnormAbs
      _ = (∑ i : Fin n, ‖eigenvalues X i‖ ^ (p : ENNReal).toReal) ^
            (1 / (p : ENNReal).toReal) := by
              rw [hsum]
      _ = ‖WithLp.toLp (p : ENNReal) (eigenvalues X)‖ := hnormX.symm

-- Proof sketch: the matrix absolute value `|X|` has eigenvalues `|λ_i(X)|`, so the same
-- `WithLp` norm computes the spectral `p`-norm from the ordered eigenvalues of `|X|`.
/-- Definition 6.41: the spectral `p`-norm can equally be computed from the ordered eigenvalues of
`|X|`. -/
theorem symmetricMatrixSpectralPNorm_eq_abs_eigenvalueNorm
    (p : Set.Ici (1 : ENNReal)) (X : SymmMat) :
    symmetricMatrixSpectralPNorm p X =
      ‖WithLp.toLp (p : ENNReal) (eigenvalues (|X|))‖ := by
  -- Reduce the public theorem to the private norm comparison between `X` and `|X|`.
  rw [symmetricMatrixSpectralPNorm_eq_eigenvalueNorm]
  exact (absEigenvalueLpNormEqOriginal p X).symm
