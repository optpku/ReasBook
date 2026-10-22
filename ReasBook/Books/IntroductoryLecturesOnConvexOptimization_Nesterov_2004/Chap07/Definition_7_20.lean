/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators RealSymmetricMatrixSpace

/- Definition 7.20 is a recall/bridge item in the symmetric-matrix Frobenius domain.

Layer targeted by this refinement:
- source-facing recall of the Chapter 5 Frobenius geometry on `𝕊^n`.

Primary domain:
- the Frobenius inner product and Frobenius norm on real symmetric matrices.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the project owner for real symmetric matrices;
- Chapter 5 `RealSymmetricMatrixSpace.frobeniusInner` in `Definition_5_4_4_2`, the project owner
  for the Frobenius pairing on `𝕊^n`;
- Chapter 5 `RealSymmetricMatrixSpace.norm_eq_sqrt_frobeniusInner`, the owner-level norm bridge;
- mathlib `Matrix.frobenius_norm_def`, the ambient matrix Frobenius norm formula.

Best owner abstraction:
- source-facing: the Frobenius inner product and associated norm on `𝕊^n`;
- core/canonical: the Chapter 5 owner `RealSymmetricMatrixSpace.frobeniusInner` together with the
  inherited norm `‖·‖` on `𝕊^n`;
- bridge/view: the entrywise double-sum realization of the Frobenius pairing.

Primitive data:
- `n : ℕ`
- `X Y : 𝕊^n`

Derived API:
- the owner pairing `⟪X, Y⟫_F`
- the inherited Frobenius norm `‖X‖`
- the owner theorem `RealSymmetricMatrixSpace.norm_eq_sqrt_frobeniusInner`

Source/core/bridge triage:
- source-facing: Definition 7.20's Frobenius geometry on symmetric matrices;
- core/canonical: `𝕊^n`, `⟪·, ·⟫_F`, and `‖·‖`;
- bridge/view: the entrywise-sum formula below.

This file removes the duplicate Chapter 7 wrapper names and reuses the existing Chapter 5 owner
directly. The only local theorem kept here is the source-facing entrywise realization of the
owner pairing. -/

section

variable (n : ℕ)

/- Definition 7.20: on `𝕊^n`, the Frobenius inner product is the Chapter 5 owner
`RealSymmetricMatrixSpace.frobeniusInner`. -/
#check (RealSymmetricMatrixSpace.frobeniusInner : 𝕊^n → 𝕊^n → ℝ)

/- The associated Frobenius norm on `𝕊^n` is the inherited norm, with source formula
`‖X‖ = sqrt ⟪X, X⟫_F` given by the Chapter 5 owner theorem. -/
#check (RealSymmetricMatrixSpace.norm_eq_sqrt_frobeniusInner :
  ∀ X : 𝕊^n, ‖X‖ = Real.sqrt ⟪X, X⟫_F)

end

/-- Expanding the Chapter 5 Frobenius pairing on `𝕊^n` gives the textbook entrywise double sum. -/
theorem frobeniusInner_eq_entrywise_sum
    {n : ℕ} (X Y : 𝕊^n) :
    ⟪X, Y⟫_F =
      ∑ i : Fin n, ∑ j : Fin n,
        ((X : Matrix (Fin n) (Fin n) ℝ) i j) * ((Y : Matrix (Fin n) (Fin n) ℝ) i j) := by
  rw [RealSymmetricMatrixSpace.frobeniusInner_def]
  calc
    Matrix.trace ((X : Matrix (Fin n) (Fin n) ℝ)ᵀ * (Y : Matrix (Fin n) (Fin n) ℝ)) =
        ∑ i : Fin n, (((X : Matrix (Fin n) (Fin n) ℝ)ᵀ * (Y : Matrix (Fin n) (Fin n) ℝ)) i i) := by
      rfl
    _ =
        ∑ i : Fin n, ∑ j : Fin n,
          ((X : Matrix (Fin n) (Fin n) ℝ) j i) * ((Y : Matrix (Fin n) (Fin n) ℝ) j i) := by
      simp [Matrix.mul_apply]
    _ = ∑ j : Fin n, ∑ i : Fin n,
          ((X : Matrix (Fin n) (Fin n) ℝ) j i) * ((Y : Matrix (Fin n) (Fin n) ℝ) j i) := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n,
          ((X : Matrix (Fin n) (Fin n) ℝ) i j) * ((Y : Matrix (Fin n) (Fin n) ℝ) i j) := by
      rfl
