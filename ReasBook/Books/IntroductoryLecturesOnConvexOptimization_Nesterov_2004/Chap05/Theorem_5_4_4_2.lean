/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open RealSymmetricMatrixSpace
open scoped RealSymmetricMatrixSpace

/-
Theorem 5.4.4.2 lies in the positive-definite real symmetric matrix / spectral barrier domain.

Sampled owner-style declarations:
* Chapter 5 `logDetBarrier`, the source-facing owner for `-log det` on `𝕊^n₊₊`;
* Chapter 5 `RealSymmetricMatrixSpace.eigenvalues`, the intrinsic eigenvalue API on `𝕊^n`;
* `Matrix.IsHermitian.det_eq_prod_eigenvalues`, the canonical determinant/eigenvalue bridge;
* `Matrix.PosDef.eigenvalues_pos`, the positivity owner for eigenvalues of positive-definite
  matrices;
* `Real.log_prod`, the canonical logarithm-of-product identity.

Best owner abstraction:
* source-facing: `logDetBarrier n` on the strict cone `𝕊^n₊₊`;
* core/canonical: Hermitian eigenvalues and positive-definite positivity;
* bridge/view: `logDetBarrier_apply`.

This refinement removes the duplicated ambient `-log det` surface from the theorem statement and
restates the identity directly for the Chapter 5 barrier owner.
-/

/-- Theorem 5.4.4.2: for a positive-definite real symmetric matrix `X`, the Chapter 5 owner
`logDetBarrier` equals the negative sum of the logarithms of the eigenvalues of `X`. -/
theorem logDetBarrier_eq_neg_sum_log_eigenvalues
    {n : ℕ} (X : 𝕊^n₊₊) :
    logDetBarrier n X =
      -∑ i : Fin n, Real.log (eigenvalues X i) := by
  have hlog :
      Real.log (∏ i : Fin n, eigenvalues X i) =
        ∑ i : Fin n, Real.log (eigenvalues X i) := by
    simpa using
      (Real.log_prod fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
        (eigenvalues_pos X i).ne')
  calc
    logDetBarrier n X = -Real.log (((X : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ).det) := by
      simp [logDetBarrier_apply]
    _ = -Real.log (∏ i : Fin n, eigenvalues X i) := by
      rw [det_eq_prod_eigenvalues (X : 𝕊^n)]
    _ = -∑ i : Fin n, Real.log (eigenvalues X i) := by
      rw [hlog]

end
