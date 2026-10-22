/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_8_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix InnerProductSpace LinearMap

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Definition 1.8.13 is `source-facing`: it names the Davidon--Fletcher--Powell inverse-Hessian
update matrix.

Primary domain:
- quasi-Newton inverse-Hessian updates on Euclidean space.

Owner abstractions sampled before refinement:
- `Matrix.toEuclideanLin`
- `InnerProductSpace.rankOne`
- `LinearMap.adjoint`
- `LinearMap.adjoint_inner_right`

Primitive data:
- the current inverse-Hessian approximation `Hk`
- the gradient difference `γk`
- the step `δk`

Derived API:
- the source-facing DFP update matrix
- its canonical operator realization under `toEuclideanLin`
- the secant-equation consequence under the two nonvanishing DFP denominators

Layer triage:
- `source-facing`: `dfpUpdatedMatrix`
- `core/canonical`: `Matrix.toEuclideanLin`, `InnerProductSpace.rankOne`
- `bridge/view`: `dfpUpdatedMatrix_toEuclideanLin`
-/

private abbrev dfpUpdateOperator (Hk : Mat) (γk δk : E) : E →ₗ[ℝ] E :=
  let H := Hk.toEuclideanLin
  let curvature := inner ℝ γk δk
  let hγ := H γk
  let imageCurvature := inner ℝ γk hγ
  H + curvature⁻¹ • rankOne ℝ δk δk -
    imageCurvature⁻¹ • rankOne ℝ hγ (adjoint H γk)

/-- Definition 1.8.13: the Davidon--Fletcher--Powell update defines the next inverse-Hessian
approximation by
`Hₖ₊₁ = Hₖ + δₖ δₖᵀ / ⟪γₖ, δₖ⟫ - Hₖ γₖ γₖᵀ Hₖ / ⟪γₖ, Hₖ γₖ⟫`. -/
def dfpUpdatedMatrix (Hk : Mat) (γk δk : E) : Mat :=
  toEuclideanLin.symm (dfpUpdateOperator Hk γk δk)

/-- The DFP update matrix realizes the canonical operator-level DFP formula on Euclidean space. -/
theorem dfpUpdatedMatrix_toEuclideanLin (Hk : Mat) (γk δk : E) :
    (dfpUpdatedMatrix Hk γk δk).toEuclideanLin =
      let H := Hk.toEuclideanLin
      let curvature := inner ℝ γk δk
      let hγ := H γk
      let imageCurvature := inner ℝ γk hγ
      H + curvature⁻¹ • rankOne ℝ δk δk -
        imageCurvature⁻¹ • rankOne ℝ hγ (adjoint H γk) := by
  simp [dfpUpdatedMatrix, dfpUpdateOperator]

/-- The DFP-updated inverse-Hessian approximation satisfies the secant equation `Hₖ₊₁ γₖ = δₖ`
whenever the two DFP denominators are nonzero. -/
-- Proof sketch: pass to the canonical operator formula, apply the two rank-one terms to `γₖ`, and
-- use the adjoint pairing identity to identify the denominator of the second correction term with
-- `⟪γₖ, Hₖ γₖ⟫`.
theorem dfpUpdatedMatrix_secantEquation (Hk : Mat) (γk δk : E)
    (hγδ : inner ℝ γk δk ≠ 0)
    (hγHγ : inner ℝ γk (Hk.toEuclideanLin γk) ≠ 0) :
    (dfpUpdatedMatrix Hk γk δk).toEuclideanLin γk = δk := by
  have hadjoint :
      inner ℝ (LinearMap.adjoint (Hk.toEuclideanLin) γk) γk =
        inner ℝ γk (Hk.toEuclideanLin γk) := by
    calc
      inner ℝ (LinearMap.adjoint (Hk.toEuclideanLin) γk) γk =
          inner ℝ γk (LinearMap.adjoint (Hk.toEuclideanLin) γk) := by
        rw [real_inner_comm]
      _ = inner ℝ (Hk.toEuclideanLin γk) γk := by
        simpa using LinearMap.adjoint_inner_right (Hk.toEuclideanLin) γk γk
      _ = inner ℝ γk (Hk.toEuclideanLin γk) := by
        rw [real_inner_comm]
  rw [dfpUpdatedMatrix]
  simp only [LinearEquiv.apply_symm_apply]
  simp [dfpUpdateOperator, hadjoint, real_inner_comm, hγδ, hγHγ]

end
