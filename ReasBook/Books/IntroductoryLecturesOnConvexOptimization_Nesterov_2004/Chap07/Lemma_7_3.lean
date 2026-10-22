/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.Subspace
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_41
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_3.Core

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open RealSymmetricMatrixSpace
open scoped BigOperators MatrixOrder SupportFunction RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Lemma 7.3 lies in Chapter 7's symmetric-matrix support-function / spectral-radius domain.

Sampled owner-style declarations:
- Chapter 3 `supportFunction` and `supportFunction_apply`, the chapter owner for support functions;
- Chapter 5 `𝕊^n`, `RealSymmetricMatrixSpace.eigenvalues`, and `⟪·, ·⟫_F`, the established
  symmetric-matrix carrier and Frobenius geometry;
- Chapter 7 `spectral_eigenvalue_l1_unit_ball`, the source-facing owner of the set `Q₂`;
- Chapter 7 `ρ(X)`, the canonical spectral-radius surface on `𝕊^n`.

Best owner abstraction:
- source-facing: Lemma 7.3's support-function formula for the spectral radius on `𝕊^n`;
- core/canonical: `spectral_eigenvalue_l1_unit_ball n`, `ξ[·]`, `⟪·, ·⟫_F`, and `ρ(X)`;
- bridge/view: the explicit trace-supremum formula obtained by expanding the owner support function
  on the Frobenius symmetric-matrix space.

Primitive data:
- `X : 𝕊^n`.

Derived API:
- the closedness / convexity / Frobenius-ball bounds for `spectral_eigenvalue_l1_unit_ball n`;
- the explicit trace formula for `(ξ[spectral_eigenvalue_l1_unit_ball n] X).toReal`;
- Lemma 7.3's main identity `ρ(X) = (ξ[spectral_eigenvalue_l1_unit_ball n] X).toReal`.

This refinement deletes the duplicate local trace-pairing, Hermitian-set, and semidefinite-gauge
owners, together with the duplicate local Frobenius inner-product instances. The file now reuses
the Chapter 5 owners directly and keeps only the source-facing bridge theorems specific to this
lemma.
-/

-- The helper/API prefix through the signed-projector attainer theorem is imported from
-- `Nesterov.Chap07.Lemma_7_3.Core` so the final source-facing statements here reuse that stable
-- proof world instead of reopening the whole projector chain locally.

/-- Helper for Lemma 7.3: the Frobenius pairing with `X` is the ambient trace pairing
`U ↦ trace (XU)` on `𝕊^n`. -/
theorem frobeniusInner_eq_trace_mul
    (X U : SymmMat) :
    inner ℝ U X = Matrix.trace ((X : Mat) * (U : Mat)) := by
  have htranspose : ((U : Mat)ᵀ) = (U : Mat) := by
    simpa [Matrix.IsSymm] using (isSymm U).eq
  -- Rewrite the inherited inner product by the Frobenius trace formula and commute the trace.
  calc
    inner ℝ U X = ⟪U, X⟫_F := rfl
    _ = Matrix.trace (((U : Mat)ᵀ) * (X : Mat)) := by
          rw [RealSymmetricMatrixSpace.frobeniusInner_def]
    _ = Matrix.trace ((U : Mat) * (X : Mat)) := by
          rw [htranspose]
    _ = Matrix.trace ((X : Mat) * (U : Mat)) := by
          simpa using Matrix.trace_mul_comm (U : Mat) (X : Mat)

/-- Helper for Lemma 7.3: the trace image of `Q₂` attains its greatest value at `ρ(X)`. -/
theorem isGreatest_traceImage_Q2_spectralRadius
    (X : SymmMat) :
    IsGreatest
      ((fun U : SymmMat ↦ Matrix.trace ((X : Mat) * (U : Mat))) ''
        spectral_eigenvalue_l1_unit_ball n)
      (ρ(X)) := by
  let traceSet : Set ℝ :=
    (fun U : SymmMat ↦ Matrix.trace ((X : Mat) * (U : Mat))) ''
      spectral_eigenvalue_l1_unit_ball n
  have hupper : ∀ y ∈ traceSet, y ≤ ρ(X) := by
    intro y hy
    rcases hy with ⟨U, hU, rfl⟩
    exact trace_pairing_le_spectralRadius_of_mem_Q2 (n := n) X hU
  have hwitness : ρ(X) ∈ traceSet := by
    -- The signed eigenspace projector witness attains the support value inside the trace image.
    rcases exists_signedEigenprojector_mem_Q2_trace_eq_spectralRadius (n := n) X with
      ⟨U, hU, htrace⟩
    exact ⟨U, hU, htrace⟩
  exact ⟨hwitness, hupper⟩

-- Proof sketch: expand the Chapter 3 support function directly as an `EReal` supremum, rewrite
-- each pairing into the ambient trace form, and then use the signed-projector attainer theorem to
-- identify the resulting greatest value with `ρ(X)`.
/-- Expanding the support function of `Q₂` at `X` gives the textbook trace supremum formula. -/
theorem supportFunction_toReal_Q2_eq_sSup_trace
    (X : SymmMat) :
    (ξ[spectral_eigenvalue_l1_unit_ball n] X).toReal =
      sSup ((fun U : SymmMat ↦ Matrix.trace ((X : Mat) * (U : Mat))) ''
        spectral_eigenvalue_l1_unit_ball n) := by
  let traceSet : Set ℝ :=
    (fun U : SymmMat ↦ Matrix.trace ((X : Mat) * (U : Mat))) ''
      spectral_eigenvalue_l1_unit_ball n
  have hgreatest :
      IsGreatest traceSet (ρ(X)) :=
    isGreatest_traceImage_Q2_spectralRadius (n := n) X
  have himage :
      (fun U : SymmMat ↦ ((inner ℝ U X : ℝ) : EReal)) ''
          spectral_eigenvalue_l1_unit_ball n =
        (fun y : ℝ ↦ (y : EReal)) '' traceSet := by
    ext z
    constructor
    · rintro ⟨U, hU, rfl⟩
      exact ⟨Matrix.trace ((X : Mat) * (U : Mat)), ⟨U, hU, rfl⟩, by
        simp [frobeniusInner_eq_trace_mul (n := n) X U]⟩
    · rintro ⟨y, ⟨U, hU, rfl⟩, rfl⟩
      exact ⟨U, hU, by
        simp [frobeniusInner_eq_trace_mul (n := n) X U]⟩
  have hgreatestEReal :
      IsGreatest
        ((fun y : ℝ ↦ (y : EReal)) '' traceSet)
        ((ρ(X) : ℝ) : EReal) := by
    simpa only [Set.image_image] using
      (EReal.coe_strictMono.map_isGreatest).2 hgreatest
  calc
    (ξ[spectral_eigenvalue_l1_unit_ball n] X).toReal
        = (sSup
            ((fun U : SymmMat ↦ ((inner ℝ U X : ℝ) : EReal)) ''
              spectral_eigenvalue_l1_unit_ball n)).toReal := by
            rw [supportFunction_apply]
    _ = ((ρ(X) : ℝ) : EReal).toReal := by
          rw [himage, hgreatestEReal.csSup_eq]
    _ = ρ(X) := by
          simp
    _ = sSup traceSet := by
          symm
          exact hgreatest.csSup_eq

-- Proof sketch: Definition 7.17 identifies `ρ(X)` as the canonical spectral-radius owner on
-- `𝕊^n`, and Lemma 7.3 expresses this owner as the support function of `Q₂` with respect to the
-- Frobenius geometry.
/-- Lemma 7.3: for a real symmetric matrix `X`, the spectral radius `ρ(X)` is the support
function of `Q₂`. -/
theorem realSymmetricMatrix_toReal_spectralRadius_eq_supportFunction_Q2
    (X : SymmMat) :
    ρ(X) = (ξ[spectral_eigenvalue_l1_unit_ball n] X).toReal := by
  let traceSet : Set ℝ :=
    (fun U : SymmMat ↦ Matrix.trace ((X : Mat) * (U : Mat))) ''
      spectral_eigenvalue_l1_unit_ball n
  -- Rewrite the support function into the real trace image used by the source statement.
  rw [supportFunction_toReal_Q2_eq_sSup_trace]
  change ρ(X) = sSup traceSet
  -- The trace image has greatest element `ρ(X)` by the signed-projector attainer theorem.
  exact (isGreatest_traceImage_Q2_spectralRadius (n := n) X).csSup_eq.symm
