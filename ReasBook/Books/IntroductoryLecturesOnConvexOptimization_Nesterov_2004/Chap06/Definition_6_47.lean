/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open RealSymmetricMatrixSpace
open scoped BigOperators RealSymmetricMatrixSpace

variable {n : ℕ}

/- Definition 6.47 lies in Chapter 6's symmetric-matrix spectral log-sum-exp smoothing domain.

Primary domain:
- positive-parameter smoothing of the maximal eigenvalue on real symmetric matrices.

Sampled owner-style declarations:
- `𝕊^n` in `Chap05/Definition_5_4_4_1`, the chapter owner for real symmetric `n × n` matrices;
- `RealSymmetricMatrixSpace.eigenvalues` in `Chap05/Definition_5_4_4_1`, the chapter owner for
  the ordered eigenvalues of an element of `𝕊^n`;
- `η` and `eta_apply` in `Chap06/Proposition_6_23` / `Definition_6_27`, the Chapter 6
  positive-parameter log-sum-exp owner on finite-dimensional real vectors;
- `entropySmoothing` in `Chap06/Proposition_6_35`, the `μ = 1` spectral smoothing owner on `𝕊^n`.

Best owner abstraction:
- source-facing: `logSumExpMaxEigenvalueSmoothing`, the positive-parameter spectral smoothing from
  Definition 6.47;
- core/canonical: `𝕊^n`, `RealSymmetricMatrixSpace.eigenvalues`, and the Chapter 6 vector owner
  `η`;
- bridge/view: the theorem `logSumExpMaxEigenvalueSmoothing_eq_eta`, identifying Definition 6.47
  with `η` applied to the ordered eigenvalue vector.

Primitive data:
- `n : ℕ`;
- a positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
- a symmetric matrix `X : 𝕊^n`.

Derived API:
- the source-facing smoothing owner below;
- its direct textbook expansion theorem;
- under `[NeZero n]`, the bridge to the Chapter 6 vector owner `η`.

The previous file rebuilt a second symmetric-matrix subtype, a second Hermitian bridge, and a
second eigenvalue accessor. Those are already owned upstream by `𝕊^n` and
`RealSymmetricMatrixSpace.eigenvalues`, so this refinement keeps only the actual new
positive-parameter smoothing owner.
-/

/-- Definition 6.47: for a positive smoothing parameter `μ` and a real symmetric matrix `X`, the
log-sum-exp smoothing of `λ_max` is
`f_μ(X) = μ log (∑ i, exp (λ_i(X) / μ))`. -/
def logSumExpMaxEigenvalueSmoothing
    (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n) : ℝ :=
  (μ : ℝ) * Real.log (∑ i : Fin n, Real.exp (eigenvalues X i / (μ : ℝ)))

/-- Expanding `logSumExpMaxEigenvalueSmoothing μ X` gives the textbook
`μ`-scaled log-sum-exp formula on the ordered eigenvalues of `X`. -/
theorem logSumExpMaxEigenvalueSmoothing_eq
    (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n) :
    logSumExpMaxEigenvalueSmoothing μ X =
      (μ : ℝ) * Real.log (∑ i : Fin n, Real.exp (eigenvalues X i / (μ : ℝ))) :=
  rfl

section

variable [NeZero n]

/-- Definition 6.47 is the Chapter 6 positive-parameter log-sum-exp owner `η` applied to the
ordered eigenvalue vector of `X`. -/
theorem logSumExpMaxEigenvalueSmoothing_eq_eta
    (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n) :
    logSumExpMaxEigenvalueSmoothing μ X = η μ (WithLp.toLp 2 (eigenvalues X)) := by
  symm
  simpa [logSumExpMaxEigenvalueSmoothing] using
    (eta_apply μ (WithLp.toLp 2 (eigenvalues X)))

end

end
