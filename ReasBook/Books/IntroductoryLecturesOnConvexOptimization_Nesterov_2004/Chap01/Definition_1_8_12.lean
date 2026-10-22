/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix InnerProductSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Definition 1.8.12 is source-facing through the correction matrix `ΔHₖ`.
Its owner abstraction is the canonical rank-one continuous linear endomorphism of Euclidean space,
and the matrix formula is the standard-basis realization of that operator.

Primary domain:
- rank-one endomorphisms of Euclidean space and their matrix realizations.

Owner declarations sampled before refinement:
- `InnerProductSpace.rankOne`
- `InnerProductSpace.rankOne_apply`
- `Matrix.toEuclideanLin`
- `InnerProductSpace.symm_toEuclideanLin_rankOne`

Primitive data:
- the current inverse-Hessian approximation `Hk`
- the gradient difference `γk`
- the step `δk`

Derived API:
- the source-facing correction matrix `ΔHₖ`
- the action of `ΔHₖ` on `γₖ`
- the secant-equation consequences under the standard SR1 denominator condition

Layer triage:
- `source-facing`: `rankOneCorrectionMatrixDifference`
- `core/canonical`: `Matrix.toEuclideanLin`, `InnerProductSpace.rankOne`
- `bridge/view`: `rankOneCorrectionMatrixDifference_apply`
-/

private abbrev sr1Residual (Hk : Mat) (γk δk : E) : E :=
  δk - Hk.toEuclideanLin γk

/-- Definition 1.8.12: `ΔHₖ` is the standard-basis matrix of the canonical rank-one correction
operator built from the secant residual `δₖ - Hₖ γₖ`, equivalently the textbook SR1
outer-product update. The nonzero denominator hypothesis belongs on the secant consequences rather
than on this source-facing matrix formula itself. -/
def rankOneCorrectionMatrixDifference (Hk : Mat) (γk δk : E) : Mat :=
  let r := sr1Residual Hk γk δk
  toEuclideanLin.symm ((inner ℝ r γk)⁻¹ • rankOne ℝ r r)

/-- Applying the rank-one correction matrix to `γₖ` returns the secant residual. -/
theorem rankOneCorrectionMatrixDifference_apply
    {Hk : Mat} {γk δk : E}
    (hdenom : inner ℝ (δk - Hk.toEuclideanLin γk) γk ≠ 0) :
    (rankOneCorrectionMatrixDifference Hk γk δk).toEuclideanLin γk =
      δk - Hk.toEuclideanLin γk := by
  let r := sr1Residual Hk γk δk
  have hr : inner ℝ r γk ≠ 0 := by
    simpa [r, sr1Residual] using hdenom
  rw [rankOneCorrectionMatrixDifference]
  simp only [LinearEquiv.apply_symm_apply]
  change ((inner ℝ r γk)⁻¹ • rankOne ℝ r r) γk = r
  rw [ContinuousLinearMap.smul_apply, rankOne_apply, smul_smul, inv_mul_cancel₀ hr, one_smul]

/-- Adding the rank-one correction matrix to `Hₖ` enforces the secant equation. -/
-- Proof sketch: evaluate `ΔHₖ` on `γₖ` via its canonical rank-one operator view; the denominator
-- cancellation leaves the secant residual `δₖ - Hₖ γₖ`, so the correction term exactly repairs
-- the original image `Hₖ γₖ`.
theorem rankOneCorrectionMatrixDifference_secantEquation
    (Hk : Mat) (γk δk : E)
    (hdenom : inner ℝ (δk - Hk.toEuclideanLin γk) γk ≠ 0) :
    (Hk + rankOneCorrectionMatrixDifference Hk γk δk).toEuclideanLin γk = δk := by
  rw [show (Hk + rankOneCorrectionMatrixDifference Hk γk δk).toEuclideanLin γk =
      Hk.toEuclideanLin γk +
        (rankOneCorrectionMatrixDifference Hk γk δk).toEuclideanLin γk by
    simp]
  rw [rankOneCorrectionMatrixDifference_apply hdenom]
  simp

end
