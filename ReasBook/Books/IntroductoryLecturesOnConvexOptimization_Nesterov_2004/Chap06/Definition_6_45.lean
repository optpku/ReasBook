/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_35

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open RealSymmetricMatrixSpace
open scoped BigOperators RealSymmetricMatrixSpace

variable {n : ℕ}

/- Definition 6.45 lies in Chapter 6's real symmetric / Hermitian spectral log-sum-exp domain.

Primary domain:
- entropy smoothing of the maximal eigenvalue on real symmetric matrices.

Sampled owner-style declarations:
- `entropySmoothing` in `Chap06/Proposition_6_35`, the existing Chapter 6 owner for
  `X ↦ log (∑ i, exp (λᵢ(X)))` on the canonical carrier `𝕊^n`;
- `entropySmoothing_apply` in `Chap06/Proposition_6_35`, the source-facing expansion theorem for
  that owner;
- `RealSymmetricMatrixSpace.eigenvalues` in `Chap05/Definition_5_4_4_1`, the chapter owner for
  the ordered eigenvalues of a real symmetric matrix;
- mathlib `Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff`, the canonical proof-irrelevance
  bridge showing that the ordered eigenvalue list depends only on the underlying Hermitian matrix.

Best owner abstraction:
- source-facing: Definition 6.45's entropy smoothing formula;
- core/canonical: `entropySmoothing : 𝕊^n → ℝ`;
- bridge/view: restriction of that owner along the real-Hermitian-to-symmetric identification.

Primitive data:
- a real Hermitian matrix `X`.

Derived API:
- the symmetric-matrix view of `X`;
- the bridge theorem below identifying the recalled owner with the textbook Hermitian formula.

Source/core/bridge triage:
- source-facing: the Hermitian-form formula in
  `entropySmoothing_eq_log_sum_exp_eigenvalues`;
- core/canonical: `entropySmoothing`;
- bridge/view: the canonical subtype inclusion of a real Hermitian matrix into `𝕊^n`.

The previous file rebuilt two parallel owners, `eigenvalueExponentialSum` and
`entropySmoothedMaxEigenvalue`, for a notion already owned upstream by `entropySmoothing`.
This refinement removes those duplicate definitions and keeps only the minimal bridge from the
source-facing Hermitian presentation to the existing symmetric-matrix owner.
-/

namespace RealSymmetricMatrixSpace

/-- The canonical view of a real Hermitian matrix as an element of `𝕊^n`. -/
abbrev ofHermitian
    (X : {X : Matrix (Fin n) (Fin n) ℝ // X.IsHermitian}) : 𝕊^n :=
  ⟨X.1, by
    rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using X.2⟩

/-- Passing from a real Hermitian matrix to its canonical element of `𝕊^n` does not change the
ordered eigenvalue list. -/
theorem eigenvalues_ofHermitian
    (X : {X : Matrix (Fin n) (Fin n) ℝ // X.IsHermitian}) :
    eigenvalues (ofHermitian X) = X.2.eigenvalues := by
  exact
    (X.2.eigenvalues_eq_eigenvalues_iff (isHermitian (ofHermitian X))).2 rfl

end RealSymmetricMatrixSpace

/- Definition 6.45 is recalled directly from the Chapter 6 owner `entropySmoothing`. -/
#check (entropySmoothing : 𝕊^n → ℝ)

/-- Definition 6.45, source-facing bridge: on a real Hermitian matrix, the recalled owner
`entropySmoothing` is the logarithm of the sum of the exponentials of the ordered eigenvalues. -/
theorem entropySmoothing_eq_log_sum_exp_eigenvalues
    (X : {X : Matrix (Fin n) (Fin n) ℝ // X.IsHermitian}) :
    entropySmoothing (ofHermitian X) =
      Real.log (∑ i : Fin n, Real.exp (X.2.eigenvalues i)) := by
  simpa [eigenvalues_ofHermitian X] using entropySmoothing_apply (ofHermitian X)

end
