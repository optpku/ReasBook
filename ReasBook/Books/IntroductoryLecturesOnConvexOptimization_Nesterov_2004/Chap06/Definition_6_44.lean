/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_41
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_42

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open RealSymmetricMatrixSpace
open scoped RealSymmetricMatrixSpace

variable {n : ℕ}

/- Definition 6.44 lies in the chapter's symmetric-matrix smoothing / trace-power domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` and `RealSymmetricMatrixSpace.eigenvalues`, the canonical symmetric-matrix
  carrier and ordered eigenvalue owner;
- Chapter 6 `RealSymmetricMatrixSpace.powerTrace`, written `π[k]`, the chapter owner for the
  trace-power coordinates;
- Chapter 6 `half_powerTrace_iteratedFDeriv_two_le` in `Proposition_6_34`, which already uses
  the half-scaled even trace-power surface needed downstream.

Best owner abstraction:
- source-facing: the smoothing functional `F_p(X) = (1 / 2) ‖λ(X)‖_(2p)^2` on `𝕊^n`;
- core/canonical: the existing trace-power owner `π[k]`;
- bridge/view: the power-trace identity
  `‖λ(X)‖_(2p)^2 = (π_{2p}(X))^(1 / p)`.

Primitive data:
- `p : ℕ+`
- `X : 𝕊^n`

Derived API:
- the source-facing smoothing functional obtained from the even trace-power owner `π[2p]` and
  scaling by `1 / 2`;
- the companion theorem rewriting that quantity through `π[2 * (p : ℕ)]`.

Source/core/bridge triage:
- source-facing: `squaredLpMatrixNormSmoothing`;
- core/canonical: `π[k]`;
- bridge/view: `squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace`.

The previous definition attempted to route through a non-existent chapter owner
`symmetricMatrixSpectralPNorm`. The chapter already exposes the even spectral data through the
trace-power owner `π[k]`, so this file now uses that canonical source-facing owner directly and
keeps only the genuinely new smoothing layer.
-/

/-- Definition 6.44: for a positive integer `p`, `squaredLpMatrixNormSmoothing p X` is the
matrix smoothing functional
`F_p(X) = (1 / 2) ‖λ(X)‖_(2p)^2 = (1 / 2) (π_{2p}(X))^(1 / p)` on the symmetric-matrix
space `𝕊^n`. -/
def squaredLpMatrixNormSmoothing (p : ℕ+) (X : 𝕊^n) : ℝ :=
  (1 / 2 : ℝ) * Real.rpow (π[2 * (p : ℕ)] X) (1 / (p : ℝ))

-- Proof sketch: diagonalize the symmetric matrix `X`, rewrite the `ℓ_{2p}`-norm of `λ(X)` as the
-- `2p`-power sum of its eigenvalues, and identify that power sum with the trace formula
-- `π_{2p}(X) = Trace(X^(2p))`.
/-- The smoothing functional agrees with the power-trace formula
`F_p(X) = (1 / 2) (π_{2p}(X))^(1 / p)`. -/
theorem squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace
    (p : ℕ+) (X : 𝕊^n) :
    squaredLpMatrixNormSmoothing p X =
      (1 / 2 : ℝ) *
        Real.rpow
          (π[2 * (p : ℕ)] X)
          (1 / (p : ℝ)) :=
  rfl
