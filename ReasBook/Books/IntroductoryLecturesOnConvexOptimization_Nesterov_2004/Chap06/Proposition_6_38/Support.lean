/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_36

noncomputable section

open scoped RealSymmetricMatrixSpace

universe u

attribute [local instance 2000] RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup
attribute [local instance 2000] RealSymmetricMatrixSpace.symmetricMatrixNormedSpace
attribute [local instance 2000] RealSymmetricMatrixSpace.symmetricMatrixInnerProductSpace
attribute [local instance 2000] RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace
attribute [local instance 2000] RealSymmetricMatrixSpace.symmetricMatrixIsUniformAddGroup
attribute [local instance 2000] NormedAddCommGroup.toAddCommGroup
attribute [local instance 2000] AddCommGroup.toAddCommMonoid
attribute [local instance 2000] NormedSpace.toModule

namespace RealSymmetricMatrixSpace

/-- Helper for Proposition 6.38: the Frobenius norm on `𝕊^n` induces the pseudometric used by the
carrier-normalized continuous-linear-map calculus. -/
noncomputable instance frobeniusPseudoMetricSpace {n : ℕ} :
    PseudoMetricSpace (𝕊^n) := inferInstance

/-- Helper for Proposition 6.38: use the Frobenius norm-induced topology on `𝕊^n` so the
continuous-linear-map smoothness API stays on one carrier spelling. -/
instance frobeniusTopologicalSpace {n : ℕ} :
    TopologicalSpace (𝕊^n) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Helper for Proposition 6.38: after normalizing the symmetric-carrier topology to the
Frobenius norm topology, every continuous linear map into `𝕊^n` is globally `C²`. -/
theorem continuousLinearMap_contDiff_two
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (A : E →L[ℝ] 𝕊^n) :
    ContDiff ℝ 2 (A : E → 𝕊^n) := by
  -- The normalized carrier instances let the standard continuous-linear-map smoothness API apply
  -- without any further transport.
  simpa using A.contDiff

/-- Helper for Proposition 6.38: the raw rescaling surface `X ↦ ((μ : ℝ)⁻¹) • X` on `𝕊^m` is
globally `C²` once the carrier topology is read through the Frobenius norm. -/
theorem invScale_contDiff_two
    (m : ℕ) (μ : {μ : ℝ // 0 < μ}) :
    ContDiff ℝ 2 (fun X : 𝕊^m ↦ ((μ : ℝ)⁻¹) • X) := by
  let scaleMap : 𝕊^m →L[ℝ] 𝕊^m :=
    ((μ : ℝ)⁻¹) • ContinuousLinearMap.id ℝ (𝕊^m)
  have hScale : ContDiff ℝ 2 (scaleMap : 𝕊^m → 𝕊^m) := by
    -- The rescaling owner is a continuous linear map on the symmetric carrier.
    simpa using scaleMap.contDiff
  simpa [scaleMap] using hScale
end RealSymmetricMatrixSpace
