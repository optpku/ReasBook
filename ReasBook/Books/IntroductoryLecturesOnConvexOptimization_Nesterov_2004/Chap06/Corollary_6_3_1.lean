/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_9

-- Declarations for this item will be appended below by the statement pipeline.

/- Corollary 6.3.1 lies in the chapter's symmetric-matrix trace-power / Hessian spectral domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the established owner for real symmetric matrices;
- Chapter 6 `RealSymmetricMatrixSpace.powerTrace`, written `π[k]`, the source-facing trace-power
  owner on `𝕊^n`;
- Chapter 6 `powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing` in `Theorem_6_9`, the
  canonical Hessian quadratic-form bound for that owner;
- mathlib `iteratedFDeriv`, `CFC.abs`, and Hermitian eigenvalues as the ambient calculus and
  spectral owners.

Best owner abstraction:
- source-facing: the Hessian quadratic-form estimate for `π_k(X) = Trace (X^k)` on the symmetric
  matrix space `𝕊^n`;
- core/canonical: `π[k]`, `iteratedFDeriv`, `CFC.abs`, and
  `powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing`;
- bridge/view: any ambient-matrix reformulation with extra symmetry hypotheses.

Primitive data:
- `k : ℕ`;
- `X H : 𝕊^n`.

Derived API:
- the source-facing owner `π[k]`;
- the canonical Hessian estimate
  `powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing`.

Source/core/bridge triage:
- source-facing: Corollary 6.3.1's Hessian inequality for the trace-power quantity;
- core/canonical: the owner theorem in `Theorem_6_9`;
- bridge/view: the discarded ambient `Matrix` restatement with `IsSymm` assumptions.

This file previously rebuilt ambient matrix normed-space instances and restated the same result
under a parallel local theorem name. Corollary 6.3.1 adds no new mathematics beyond the canonical
symmetric-matrix owner theorem, so this file is now a pure recall item.
-/

/- Corollary 6.3.1 is the canonical symmetric-matrix Hessian estimate from `Theorem_6_9`. -/
recall powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing
