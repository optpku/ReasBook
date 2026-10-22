/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped RealSymmetricMatrixSpace

/- Proposition 5.4.4.1 belongs to the chapter's real symmetric-matrix Frobenius domain.

Sampled owner-style declarations:
* `𝕊^n` from Definition 5.4.4.1
* `RealSymmetricMatrixSpace.frobeniusInner`
* `RealSymmetricMatrixSpace.frobeniusInner_def`
* `RealSymmetricMatrixSpace.sandwich`
* `Matrix.trace_mul_cycle'`
* `RealSymmetricMatrixSpace.isSymm`

Best owner abstraction:
* source-facing: the real symmetric-matrix space `𝕊^n` with Frobenius pairing `⟪·, ·⟫_F`;
* core/canonical: the ambient trace formula for the restricted Frobenius pairing;
* bridge/view: the coercion `𝕊^n → Matrix (Fin n) (Fin n) ℝ`.

Primitive data:
* `X Y : 𝕊^n`.

Derived API:
* the intrinsic square `RealSymmetricMatrixSpace.sandwich Y 1 : 𝕊^n`, whose ambient matrix is
  `(Y : Mat)^2`;
* the ambient sandwich product `(Y : Mat) * (X : Mat) * (Y : Mat)`;
* the trace identities obtained from `RealSymmetricMatrixSpace.frobeniusInner_def`,
  cyclicity of trace, and simplification against `(1 : 𝕊^n)`.

This refinement removes the parallel local owner wrappers `square`, `sandwich`, and `identity`,
and returns the proposition to the chapter owners `𝕊^n` and `⟪·, ·⟫_F`, using the canonical
ambient matrix expressions only where multiplication actually lives. -/

section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

open RealSymmetricMatrixSpace

-- `sandwich Y 1` is the intrinsic symmetric-matrix representative of the ambient square `Y²`.
/-- Pairing `X` with the intrinsic square `sandwich Y 1` gives the trace of `YXY`. -/
theorem frobeniusInner_square_eq_trace_sandwich
    (X Y : SymmMat) :
    ⟪X, sandwich Y (1 : SymmMat)⟫_F =
      Matrix.trace ((Y : Mat) * (X : Mat) * (Y : Mat)) := by
  calc
    ⟪X, sandwich Y (1 : SymmMat)⟫_F =
        Matrix.trace ((X : Mat)ᵀ * (sandwich Y (1 : SymmMat) : Mat)) := by
          rw [frobeniusInner_def]
    _ = Matrix.trace ((X : Mat) * (Y : Mat) ^ 2) := by
          simp [pow_two, (isSymm X).eq]
    _ = Matrix.trace ((Y : Mat) * (X : Mat) * (Y : Mat)) := by
          simpa [pow_two, Matrix.mul_assoc] using
            Matrix.trace_mul_cycle' (X : Mat) (Y : Mat) (Y : Mat)

/-- Pairing the sandwich `YXY` with the identity matrix recovers its trace. -/
theorem frobeniusInner_one_sandwich_eq_trace
    (X Y : SymmMat) :
    ⟪(1 : SymmMat), sandwich Y X⟫_F =
      Matrix.trace ((Y : Mat) * (X : Mat) * (Y : Mat)) := by
  rw [frobeniusInner_def]
  simp

/-- Proposition 5.4.4.1: for real symmetric matrices `X` and `Y`, the Frobenius pairing of `X`
with the intrinsic symmetric-carrier square `sandwich Y 1` of `Y²` equals `Trace (YXY)`, and
that trace is the Frobenius pairing of `YXY` with the identity matrix. -/
theorem frobenius_trace_identity_for_real_symmetric_matrices
    (X Y : SymmMat) :
    ⟪X, sandwich Y (1 : SymmMat)⟫_F =
        Matrix.trace ((Y : Mat) * (X : Mat) * (Y : Mat)) ∧
      Matrix.trace ((Y : Mat) * (X : Mat) * (Y : Mat)) =
        ⟪(1 : SymmMat), sandwich Y X⟫_F := by
  exact
    ⟨frobeniusInner_square_eq_trace_sandwich X Y,
      (frobeniusInner_one_sandwich_eq_trace X Y).symm⟩

end
